#!/usr/bin/env python3
"""
RakutenTV UK — EPG + M3U generator

Fetches programme data from the Rakuten v3/live_channels API and merges
stream URLs from an external M3U source to produce:
  • epg.xml      — XMLTV guide
  • playlist.m3u — paired M3U playlist (channels with matched streams only)

Resilience notes (v2):
  • The external M3U host (apsattv.com) can be unreachable from GitHub runners.
    That is no longer fatal. Stream URLs are taken from, in order:
      1. the live M3U source (plus any mirrors in the M3U_MIRRORS env var)
      2. the playlist.m3u already committed in the repo (last good run)
  • The EPG is always generated if the Rakuten API works.
  • An existing playlist.m3u is never overwritten with an empty one.
  • Set DEBUG=1 for verbose logging.
"""

import hashlib
import logging
import os
import re
import sys
import time
import unicodedata
from datetime import datetime, timedelta, timezone
from urllib.parse import urlencode

import pytz
import requests
from lxml import etree

# ── Configuration ─────────────────────────────────────────────────────────────

M3U_SOURCES = ["https://www.apsattv.com/rakuten_uk.m3u"] + [
    u.strip() for u in os.environ.get("M3U_MIRRORS", "").split(",") if u.strip()
]
M3U_HASH_FILE      = ".m3u_source_hash"
EPG_FILE           = "epg.xml"
PLAYLIST_FILE      = "playlist.m3u"
TIMEZONE           = pytz.timezone("Europe/London")
DT_FORMAT          = "%Y%m%d%H%M%S %z"
GAP_THRESHOLD_SECS = 60

# Every channel in the playlist is placed in this group.
GROUP_TITLE        = "Fast RakutenTV UK"

# (connect, read) timeouts. Short connect timeout so an unreachable host
# fails fast instead of burning minutes.
REQUEST_TIMEOUT    = (10, 30)

API_ATTEMPTS       = 4
API_BACKOFF_SECS   = 15
M3U_ATTEMPTS       = 2
M3U_BACKOFF_SECS   = 5

EPG_URL = "https://raw.githubusercontent.com/BuddyChewChew/RakutenTV/main/epg.xml"

BROWSER_UA = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/128.0.0.0 Safari/537.36"
)

API_HEADERS = {
    "User-Agent": BROWSER_UA,
    "Origin": "https://rakuten.tv",
    "Referer": "https://rakuten.tv/",
    "Accept": "application/json, text/plain, */*",
    "Accept-Language": "en-GB,en;q=0.9",
}

M3U_HEADERS = {
    "User-Agent": BROWSER_UA,
    "Accept": "*/*",
    "Accept-Language": "en-GB,en;q=0.9",
}

# Values that have historically worked. 250 is now rejected.
PER_PAGE_CANDIDATES = [100, 50, 20]

logging.basicConfig(
    level=logging.DEBUG if os.environ.get("DEBUG") else logging.INFO,
    format="%(asctime)s %(levelname)-7s %(message)s",
    datefmt="%H:%M:%S",
    stream=sys.stdout,
)
log = logging.getLogger("rakuten")


# ── Helpers ───────────────────────────────────────────────────────────────────

def remove_control_characters(s: str) -> str:
    return "".join(ch for ch in s if unicodedata.category(ch)[0] != "C")


def normalize(name: str) -> str:
    return re.sub(r"[^a-z0-9]", "", name.lower())


def parse_dt(s: str) -> datetime:
    """Parse API timestamps like 2026-11-21T20:00:00.000Z or ...000+00:00."""
    dt = datetime.fromisoformat(s.replace("Z", "+00:00"))
    return dt if dt.tzinfo else dt.replace(tzinfo=timezone.utc)


def to_tz_str(val) -> str:
    if isinstance(val, datetime):
        dt = val if val.tzinfo else val.replace(tzinfo=timezone.utc)
    else:
        dt = datetime.fromtimestamp(val, tz=timezone.utc)
    return dt.astimezone(TIMEZONE).strftime(DT_FORMAT)


def fetch_with_retry(url: str, headers: dict | None = None, attempts: int = 3,
                     backoff: int = 10, timeout=REQUEST_TIMEOUT) -> requests.Response:
    """
    GET with retries on timeouts, connection errors and 5xx.
    4xx responses are logged and raised immediately (retrying won't help).
    """
    last_exc = None
    for attempt in range(1, attempts + 1):
        t0 = time.monotonic()
        try:
            log.debug("GET %s (attempt %d/%d)", url, attempt, attempts)
            resp = requests.get(url, headers=headers or {}, timeout=timeout)
            log.debug("  -> HTTP %s, %d bytes, %.1fs",
                      resp.status_code, len(resp.content), time.monotonic() - t0)

            if 400 <= resp.status_code < 500:
                log.error("HTTP %s from %s — body: %r", resp.status_code, url, resp.text[:500])
                resp.raise_for_status()

            if resp.status_code >= 500:
                last_exc = requests.exceptions.HTTPError(f"HTTP {resp.status_code}", response=resp)
                log.warning("[attempt %d/%d] HTTP %s", attempt, attempts, resp.status_code)
            else:
                return resp

        except requests.exceptions.HTTPError as exc:
            # Only reachable for 4xx (raised above) — don't retry
            raise exc
        except requests.exceptions.RequestException as exc:
            last_exc = exc
            log.warning("[attempt %d/%d] %s: %s (after %.1fs)",
                        attempt, attempts, type(exc).__name__,
                        str(exc)[:200], time.monotonic() - t0)

        if attempt < attempts:
            log.info("  retrying in %ds ...", backoff)
            time.sleep(backoff)

    raise last_exc


# ── EPG window ────────────────────────────────────────────────────────────────

def get_epg_window(hours: int = 72):
    now = datetime.now(timezone.utc).replace(minute=0, second=0, microsecond=0)
    end = (now + timedelta(hours=hours)).replace(hour=0, minute=0, second=0, microsecond=0)
    if end <= now:
        end += timedelta(days=1)
    return now, end


# ── M3U loading & parsing ─────────────────────────────────────────────────────

def check_m3u_freshness(text: str) -> None:
    current_hash = hashlib.sha256(text.encode("utf-8")).hexdigest()
    previous_hash = None
    try:
        with open(M3U_HASH_FILE, "r") as f:
            previous_hash = f.read().strip()
    except FileNotFoundError:
        pass

    if previous_hash is None:
        log.info("[freshness] no previous hash on record — treating as baseline")
    elif current_hash == previous_hash:
        log.info("[freshness] M3U source UNCHANGED since last run")
    else:
        log.info("[freshness] M3U source CHANGED since last run")

    with open(M3U_HASH_FILE, "w") as f:
        f.write(current_hash)


def load_m3u_text():
    """
    Return (text, origin) or (None, None).
    Tries each live source, then falls back to the playlist.m3u already in the repo.
    """
    for url in M3U_SOURCES:
        log.info("Fetching M3U: %s", url)
        try:
            resp = fetch_with_retry(url, headers=M3U_HEADERS,
                                    attempts=M3U_ATTEMPTS, backoff=M3U_BACKOFF_SECS)
            if "#EXTINF" not in resp.text:
                log.warning("  response from %s has no #EXTINF lines — ignoring", url)
                log.debug("  first 300 chars: %r", resp.text[:300])
                continue
            check_m3u_freshness(resp.text)
            return resp.text, f"live:{url}"
        except Exception as exc:
            log.warning("  could not fetch %s (%s: %s)", url, type(exc).__name__, str(exc)[:150])

    if os.path.exists(PLAYLIST_FILE):
        log.warning("All live M3U sources failed — falling back to existing %s", PLAYLIST_FILE)
        with open(PLAYLIST_FILE, "r", encoding="utf-8") as f:
            text = f.read()
        if "#EXTINF" in text:
            return text, f"local:{PLAYLIST_FILE}"
        log.warning("  %s has no #EXTINF lines", PLAYLIST_FILE)

    return None, None


def parse_m3u(text: str):
    by_name, by_slug = {}, {}
    lines = text.splitlines()
    i = 0

    while i < len(lines):
        line = lines[i].strip()
        if line.startswith("#EXTINF"):
            tvg_id_m   = re.search(r'tvg-id="([^"]*)"',   line)
            tvg_logo_m = re.search(r'tvg-logo="([^"]*)"', line)

            tvg_id   = tvg_id_m.group(1)   if tvg_id_m   else ""
            tvg_logo = tvg_logo_m.group(1) if tvg_logo_m else ""
            display_name = line.rsplit(",", 1)[-1].strip()

            stream_url = ""
            i += 1
            while i < len(lines):
                candidate = lines[i].strip()
                if candidate and not candidate.startswith("#"):
                    stream_url = candidate
                    break
                i += 1

            if stream_url:
                entry = {
                    "tvg_id":   tvg_id,
                    "tvg_logo": tvg_logo,
                    "group":    GROUP_TITLE,
                    "name":     display_name,
                    "url":      stream_url,
                }
                by_name[normalize(display_name)] = entry

                slug_m = re.search(r"RakutenTV-UK_(.+)$", tvg_id)
                if slug_m:
                    by_slug[slug_m.group(1).lower()] = entry
                if tvg_id:
                    # Also index by the raw id so a previously generated
                    # playlist.m3u (tvg-id == Rakuten channel id) matches.
                    by_slug.setdefault(tvg_id.lower(), entry)
        i += 1

    log.info("  -> parsed %d channels from M3U", len(by_name))
    return by_name, by_slug


def match_m3u(ch_name: str, ch_id: str, by_name: dict, by_slug: dict):
    norm = normalize(ch_name)

    if norm in by_name:
        return by_name[norm]
    if str(ch_id).lower() in by_slug:
        return by_slug[str(ch_id).lower()]
    for key, entry in by_name.items():
        if norm in key or key in norm:
            return entry
    return None


# ── XMLTV / M3U builders ──────────────────────────────────────────────────────

def build_xmltv(channels: list, programmes: list) -> bytes:
    root = etree.Element("tv")
    root.set("generator-info-name", "rakuten-uk-epg")
    root.set("generator-info-url",  "https://github.com/BuddyChewChew/RakutenTV")

    for ch in channels:
        channel = etree.SubElement(root, "channel")
        channel.set("id", str(ch["id"]))

        display = etree.SubElement(channel, "display-name")
        lang = (ch.get("language") or "en").rstrip("s").lower()
        display.set("lang", lang)
        display.text = ch["name"]

        if ch.get("icon"):
            icon = etree.SubElement(channel, "icon")
            icon.set("src", ch["icon"])
            icon.text = ""

    for pr in programmes:
        prog = etree.SubElement(root, "programme")
        prog.set("channel", str(pr["channel_id"]))
        prog.set("start",   to_tz_str(pr["starts_at"]))
        prog.set("stop",    to_tz_str(pr["ends_at"]))

        title = etree.SubElement(prog, "title")
        title.set("lang", "en")
        title.text = pr["title"]

        if pr.get("subtitle"):
            sub = etree.SubElement(prog, "sub-title")
            sub.set("lang", "en")
            sub.text = remove_control_characters(pr["subtitle"])

        if pr.get("description"):
            desc = etree.SubElement(prog, "desc")
            desc.set("lang", "en")
            desc.text = remove_control_characters(pr["description"])

        for tag in pr.get("tags") or []:
            cat = etree.SubElement(prog, "category")
            cat.set("lang", "en")
            cat.text = tag.get("name", "")

    return etree.tostring(root, pretty_print=True, encoding="utf-8")


def build_m3u(channels: list):
    """Return (playlist_text, matched_count)."""
    lines     = [f'#EXTM3U url-tvg="{EPG_URL}"']
    matched   = 0
    unmatched = []

    for ch in channels:
        url = ch.get("stream_url")
        if not url:
            unmatched.append(ch["name"])
            continue

        tvg_id   = ch.get("tvg_id")   or ch["id"]
        tvg_logo = ch.get("tvg_logo") or ch.get("icon") or ""

        lines.append(
            f'#EXTINF:-1 tvg-id="{tvg_id}" '
            f'tvg-logo="{tvg_logo}" '
            f'group-title="{GROUP_TITLE}",{ch["name"]}'
        )
        lines.append(url)
        matched += 1

    log.info("M3U: %d matched, %d unmatched", matched, len(unmatched))
    if unmatched:
        log.info("Unmatched channels (no stream URL found):")
        for n in unmatched:
            log.info("  - %s", n)

    return "\n".join(lines) + "\n", matched


# ── API helpers ───────────────────────────────────────────────────────────────

def build_api_url(epg_start, epg_end, per_page: int, page: int = 1,
                  include_timestamps: bool = True) -> str:
    params = {
        "classification_id": "18",
        "device_identifier": "web",
        "device_stream_audio_quality": "2.0",
        "device_stream_hdr_type": "NONE",
        "device_stream_video_quality": "FHD",
        "epg_duration_minutes": "360",
        "epg_ends_at": epg_end.strftime("%Y-%m-%dT%H:%M:%S.000Z"),
        "epg_starts_at": epg_start.strftime("%Y-%m-%dT%H:%M:%S.000Z"),
        "locale": "en",
        "market_code": "uk",
        "per_page": str(per_page),
        "page": str(page),
    }
    if include_timestamps:
        params["epg_ends_at_timestamp"] = str(int(epg_end.timestamp()))
        params["epg_starts_at_timestamp"] = str(int(epg_start.timestamp()))

    return "https://gizmo.rakuten.tv/v3/live_channels?" + urlencode(params)


def fetch_one_page(epg_start, epg_end, per_page: int, page: int,
                   include_timestamps: bool) -> list:
    url = build_api_url(epg_start, epg_end, per_page, page, include_timestamps)
    resp = fetch_with_retry(url, headers=API_HEADERS,
                            attempts=API_ATTEMPTS, backoff=API_BACKOFF_SECS)
    body = resp.json()
    data = body.get("data") or []
    if not data:
        log.debug("  empty 'data'; top-level keys: %s", list(body.keys()))
    return data


def fetch_epg_data() -> list:
    """
    Try different per_page values and window sizes until something works.
    Also paginates so we still get the full channel list.
    """
    strategies = [
        {"hours": 72, "timestamps": True,  "label": "72h + timestamps"},
        {"hours": 72, "timestamps": False, "label": "72h (dates only)"},
        {"hours": 48, "timestamps": True,  "label": "48h + timestamps"},
        {"hours": 24, "timestamps": False, "label": "24h (dates only)"},
    ]

    last_exc = None

    for strat in strategies:
        for per_page in PER_PAGE_CANDIDATES:
            epg_start, epg_end = get_epg_window(hours=strat["hours"])
            log.info("Trying: %s, per_page=%d", strat["label"], per_page)
            log.info("  window: %s → %s", epg_start.isoformat(), epg_end.isoformat())

            try:
                all_channels = []
                page = 1
                while True:
                    chunk = fetch_one_page(
                        epg_start, epg_end, per_page, page, strat["timestamps"]
                    )
                    if not chunk:
                        break
                    all_channels.extend(chunk)
                    log.info("  page %d: +%d channels (total %d)", page, len(chunk), len(all_channels))
                    if len(chunk) < per_page:
                        break
                    page += 1
                    if page > 10:
                        log.warning("  hit page safety limit")
                        break

                if all_channels:
                    log.info("  ✓ Success — retrieved %d channels", len(all_channels))
                    return all_channels
                log.warning("  empty data array")
            except Exception as exc:
                last_exc = exc
                log.warning("  ✗ Failed: %s: %s", type(exc).__name__, str(exc)[:200])
                continue

    raise RuntimeError(
        "All EPG fetch strategies failed. Last error: " + str(last_exc)
    ) from last_exc


# ── Main ──────────────────────────────────────────────────────────────────────

def main() -> int:
    log.info("Python %s", sys.version.split()[0])

    # 1. Stream URLs (never fatal)
    text, origin = load_m3u_text()
    if text:
        log.info("M3U stream data origin: %s", origin)
        m3u_by_name, m3u_by_slug = parse_m3u(text)
    else:
        log.warning("No M3U stream data available at all — playlist will not be updated")
        m3u_by_name, m3u_by_slug = {}, {}

    # 2. EPG data (fatal if it fails)
    log.info("Fetching EPG data from Rakuten API ...")
    data = fetch_epg_data()
    log.info("Retrieved %d channels", len(data))

    channels_data  = []
    programme_data = []
    skipped_progs  = 0

    for channel in data:
        ch_name = channel["title"]
        ch_id   = channel["id"]
        log.debug("channel: %s (%s)", ch_name, ch_id)

        ch_icon = None
        if channel.get("images"):
            imgs = channel["images"]
            ch_icon = imgs.get("artwork_negative") or imgs.get("artwork")

        ch_language = ch_tags = None
        if channel.get("labels"):
            labels = channel["labels"]
            langs  = labels.get("languages")
            if langs:
                ch_language = langs[0].get("id")
            ch_tags = labels.get("tags")

        m3u = match_m3u(ch_name, ch_id, m3u_by_name, m3u_by_slug)

        channels_data.append({
            "name":       ch_name,
            "epg_number": channel.get("channel_number"),
            "id":         ch_id,
            "icon":       ch_icon,
            "language":   ch_language,
            "tags":       ch_tags,
            "stream_url": m3u["url"] if m3u else None,
            "tvg_id":     ch_id,
            "tvg_logo":   m3u["tvg_logo"] if m3u else ch_icon,
            "group":      GROUP_TITLE,
        })

        for item in channel.get("live_programs") or []:
            try:
                programme_data.append({
                    "title":       item["title"],
                    "subtitle":    item.get("subtitle"),
                    "description": item.get("description"),
                    "starts_at":   parse_dt(item["starts_at"]),
                    "ends_at":     parse_dt(item["ends_at"]),
                    "channel_id":  ch_id,
                    "language":    ch_language,
                    "tags":        ch_tags,
                })
            except (KeyError, ValueError, TypeError) as exc:
                skipped_progs += 1
                log.debug("  skipped bad programme on %s: %s %r", ch_name, type(exc).__name__, exc)

    log.info("Collected %d programmes (%d skipped as malformed)", len(programme_data), skipped_progs)

    # 3. Normalise end times
    programme_data.sort(key=lambda p: (p["channel_id"], p["starts_at"]))
    by_channel = {}
    for p in programme_data:
        by_channel.setdefault(p["channel_id"], []).append(p)

    for plist in by_channel.values():
        for i in range(len(plist) - 1):
            cur, nxt = plist[i], plist[i + 1]
            if nxt["starts_at"] <= cur["ends_at"]:
                cur["ends_at"] = nxt["starts_at"]
            elif (nxt["starts_at"] - cur["ends_at"]).total_seconds() <= GAP_THRESHOLD_SECS:
                cur["ends_at"] = nxt["starts_at"]

    # 4. Write outputs
    if not programme_data:
        log.error("API returned channels but zero programmes — keeping existing %s", EPG_FILE)
        return 1

    with open(EPG_FILE, "wb") as f:
        f.write(build_xmltv(channels_data, programme_data))
    log.info("Wrote %s", EPG_FILE)

    playlist_text, matched = build_m3u(channels_data)
    if matched == 0:
        log.warning("No channels matched a stream URL — leaving existing %s untouched", PLAYLIST_FILE)
    else:
        with open(PLAYLIST_FILE, "w", encoding="utf-8") as f:
            f.write(playlist_text)
        log.info("Wrote %s (%d channels)", PLAYLIST_FILE, matched)

    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception:
        log.exception("Fatal error")
        sys.exit(1)
