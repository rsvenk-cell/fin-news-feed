#!/usr/bin/env python3
"""
FinBrief news builder.

Reads the sources in feeds.json, fetches them, removes duplicates, sorts items
into categories, trims each publisher excerpt to 100 words, and writes
docs/feed.json, which the FinBrief iPhone app downloads.

Uses only Python's standard library, so nothing needs installing.
"""

import difflib
import hashlib
import html
import json
import os
import re
import sys
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime

ROOT = os.path.dirname(os.path.abspath(__file__))
FEEDS_FILE = os.path.join(ROOT, "feeds.json")
OUT_FILE = os.path.join(ROOT, "docs", "feed.json")

IST = timezone(timedelta(hours=5, minutes=30))
NOW = datetime.now(timezone.utc)
UA = ("Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 "
      "(KHTML, like Gecko) Version/17.0 Safari/605.1.15")
CATEGORY_ORDER = ["Indirect Tax", "Direct Tax", "Accounting", "Regulatory",
                  "Markets", "Economy", "Business"]


# ---------------------------------------------------------------- fetching

def google_news_url(query, when=None):
    q = f"{query} when:{when}" if when else query
    return ("https://news.google.com/rss/search?q=" + urllib.parse.quote(q)
            + "&hl=en-IN&gl=IN&ceid=IN:en")


def fetch(url, timeout=25):
    req = urllib.request.Request(url, headers={
        "User-Agent": UA,
        "Accept": "application/rss+xml, application/atom+xml, application/xml, text/xml, */*",
        "Accept-Language": "en-IN,en;q=0.9",
    })
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return resp.read()


def parse_xml(data):
    """Parse XML, repairing the most common feed mistakes if needed."""
    try:
        return ET.fromstring(data)
    except ET.ParseError:
        pass
    m = re.search(rb'encoding=["\']([A-Za-z0-9_\-]+)["\']', data[:200])
    enc = m.group(1).decode() if m else "utf-8"
    try:
        text = data.decode(enc, errors="replace")
    except LookupError:
        text = data.decode("utf-8", errors="replace")
    text = text.lstrip("﻿ \r\n\t")
    text = re.sub(r"^<\?xml[^>]*\?>", "", text)                     # drop declaration
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)        # control chars
    text = re.sub(r"&(?!#\d+;|#x[0-9a-fA-F]+;|[A-Za-z][A-Za-z0-9]*;)", "&amp;", text)
    return ET.fromstring(text)


# ---------------------------------------------------------------- parsing helpers

def local(tag):
    return tag.rsplit("}", 1)[-1] if isinstance(tag, str) else ""


def child(el, *names):
    for c in el:
        if local(c.tag) in names:
            return c
    return None


def child_text(el, *names):
    for name in names:
        for c in el:
            if local(c.tag) == name:
                t = "".join(c.itertext()).strip()
                if t:
                    return t
    return ""


def item_link(el):
    for c in el:
        if local(c.tag) == "link":
            if c.text and c.text.strip():
                return c.text.strip()
            href = c.get("href")
            if href and c.get("rel", "alternate") == "alternate":
                return href.strip()
    guid = child_text(el, "guid", "id")
    return guid if guid.startswith("http") else ""


def clean_text(raw):
    if not raw:
        return ""
    t = html.unescape(raw)
    t = re.sub(r"(?is)<(script|style)[^>]*>.*?</\1>", " ", t)
    t = re.sub(r"(?s)<[^>]+>", " ", t)
    t = html.unescape(t)
    t = re.sub(r"(?i)the post .{0,300}? appeared first on .{0,80}?\.?\s*$", "", t)
    t = re.sub(r"(?i)(continue reading|read more)\s*[.…»>]*\s*$", "", t)
    t = t.replace("[…]", "…").replace("[...]", "…")
    t = re.sub(r"\s+", " ", t).strip()
    return t


def trim_words(text, limit):
    words = text.split()
    if len(words) <= limit:
        return text
    cut = " ".join(words[:limit])
    last = max(cut.rfind(". "), cut.rfind("? "), cut.rfind("! "))
    if last > len(cut) * 0.6:
        return cut[: last + 1]
    return cut.rstrip(",;:") + "…"


def parse_date(s):
    if not s:
        return None
    d = None
    try:
        d = parsedate_to_datetime(s)
    except (TypeError, ValueError, IndexError):
        d = None
    if d is None:
        try:
            d = datetime.fromisoformat(s.strip().replace("Z", "+00:00"))
        except ValueError:
            for fmt in ("%d %b %Y %H:%M:%S", "%Y-%m-%d %H:%M:%S", "%d-%m-%Y %H:%M:%S",
                        "%a, %d %b %Y %H:%M:%S", "%d %b %Y", "%Y-%m-%d"):
                try:
                    d = datetime.strptime(s.strip()[: len(fmt) + 8].strip(), fmt)
                    break
                except ValueError:
                    continue
    if d is None:
        return None
    if d.tzinfo is None:
        d = d.replace(tzinfo=IST)          # Indian sources usually mean IST
    d = d.astimezone(timezone.utc)
    return min(d, NOW)                     # clamp future-dated items


def norm_title(t):
    return re.sub(r"[^a-z0-9 ]", "", t.lower()).strip()


def make_id(link, title):
    return hashlib.sha1((link or title).encode("utf-8")).hexdigest()[:16]


# ---------------------------------------------------------------- categories

def build_matchers(categories):
    compiled = {}
    for cat, words in categories.items():
        pats = [r"(?<![a-z0-9])" + re.escape(w.lower()) + r"(?![a-z0-9])" for w in words]
        compiled[cat] = re.compile("|".join(pats)) if pats else None
    return compiled


def detect_category(text, matchers):
    low = text.lower()
    for cat in CATEGORY_ORDER + [c for c in matchers if c not in CATEGORY_ORDER]:
        rx = matchers.get(cat)
        if rx and rx.search(low):
            return cat
    return None


# ---------------------------------------------------------------- per-source parsing

def parse_feed_items(root, src, max_words, matchers):
    entries = [e for e in root.iter() if local(e.tag) in ("item", "entry")]
    out = []
    excludes = [x.lower() for x in src.get("exclude", [])]
    is_google = "news.google.com" in src.get("_url", "")
    for e in entries:
        title = clean_text(child_text(e, "title"))
        link = item_link(e)
        if not title or not link:
            continue
        source = src["name"]
        src_el = child(e, "source")
        if src_el is not None and (src_el.text or "").strip():
            source = src_el.text.strip()
        if is_google:
            suffix = " - " + source
            if title.endswith(suffix):
                title = title[: -len(suffix)].strip()
        if any(x in title.lower() for x in excludes):
            continue

        # Pick the best publisher excerpt: first one with 25+ words, else the longest.
        candidates = [clean_text(child_text(e, n))
                      for n in ("description", "summary", "encoded", "content")]
        candidates = [c for c in candidates if c]
        summary = next((c for c in candidates if len(c.split()) >= 25),
                       max(candidates, key=len) if candidates else "")
        # Google News / headline-only excerpts just repeat the title: drop them.
        if summary:
            ratio = difflib.SequenceMatcher(None, norm_title(summary)[:200], norm_title(title)).ratio()
            if ratio > 0.7 or norm_title(summary).startswith(norm_title(title)[:40]):
                summary = ""
        summary = trim_words(summary, max_words)

        published = parse_date(child_text(e, "pubDate", "published", "updated", "date")) or NOW

        text = f"{title} {summary}"
        detected = detect_category(text, matchers)
        if src.get("filter") and not detected:
            continue                                   # mixed feed: keep finance/business only
        category = src.get("category") or detected or src.get("fallback", "Business")

        out.append({
            "id": make_id(link, title),
            "title": title,
            "link": link,
            "source": source,
            "category": category,
            "published": published,
            "summary": summary,
            "_weight": src.get("weight", 1),
        })
    return out


def parse_trends(root, max_words, matchers):
    out = []
    for rank, e in enumerate(r for r in root.iter() if local(r.tag) == "item"):
        term = clean_text(child_text(e, "title"))
        if not term:
            continue
        traffic = child_text(e, "approx_traffic")
        news = [n for n in e if local(n.tag) == "news_item"]
        link, ntitle, snippet, nsource = "", "", "", "Google Trends"
        if news:
            n = news[0]
            ntitle = clean_text(child_text(n, "news_item_title"))
            snippet = clean_text(child_text(n, "news_item_snippet"))
            link = child_text(n, "news_item_url")
            nsource = child_text(n, "news_item_source") or nsource
        if not link:
            link = "https://www.google.com/search?q=" + urllib.parse.quote(term)
        parts = []
        if traffic:
            parts.append(f"About {traffic} searches in India.")
        if ntitle:
            parts.append(ntitle.rstrip(".") + ".")
        if snippet and snippet not in ntitle:
            parts.append(snippet)
        detected = detect_category(f"{term} {ntitle} {snippet}", matchers)
        out.append({
            "id": make_id(link, term),
            "title": term.title() if term.islower() else term,
            "link": link,
            "source": nsource,
            "category": "Business" if detected else "General",
            "published": parse_date(child_text(e, "pubDate")) or NOW,
            "summary": trim_words(" ".join(parts), max_words),
            "_rank": rank,
        })
    return out


def load_source(src, max_words, matchers):
    if src.get("type") == "google_news":
        url = google_news_url(src["query"], src.get("when"))
    else:
        url = src["url"]
    src["_url"] = url
    try:
        root = parse_xml(fetch(url))
        if src.get("type") == "google_trends":
            items = parse_trends(root, max_words, matchers)
        else:
            items = parse_feed_items(root, src, max_words, matchers)
        return src["name"], items, None
    except Exception as exc:                            # one bad source never stops the run
        return src["name"], [], f"{type(exc).__name__}: {exc}"


def load_all(sources, max_words, matchers):
    with ThreadPoolExecutor(max_workers=8) as pool:
        results = list(pool.map(lambda s: load_source(s, max_words, matchers), sources))
    ok, failed, items = [], [], []
    for name, its, err in results:
        if err:
            failed.append(f"{name} ({err[:120]})")
        else:
            ok.append(f"{name}: {len(its)}")
            items.extend(its)
    return items, ok, failed


# ---------------------------------------------------------------- selection

def is_duplicate(item, chosen, seen_ids):
    if item["id"] in seen_ids:
        return True
    t = norm_title(item["title"])
    for c in chosen:
        if difflib.SequenceMatcher(None, t, norm_title(c["title"])).ratio() > 0.8:
            return True
    return False


def select_daily(items, cfg):
    cutoff = NOW - timedelta(hours=cfg["daily_max_age_hours"])
    fresh = [i for i in items if i["published"] >= cutoff]

    def score(i):
        age_h = (NOW - i["published"]).total_seconds() / 3600
        return i["_weight"] * 6 + max(0.0, 24 - age_h) / 2

    fresh.sort(key=score, reverse=True)
    chosen, ids, per_cat = [], set(), {}
    for i in fresh:
        if len(chosen) >= cfg["daily_max"]:
            break
        if per_cat.get(i["category"], 0) >= cfg["daily_per_category_max"]:
            continue
        if is_duplicate(i, chosen, ids):
            continue
        chosen.append(i)
        ids.add(i["id"])
        per_cat[i["category"]] = per_cat.get(i["category"], 0) + 1
    chosen.sort(key=lambda i: i["published"], reverse=True)
    return chosen


def select_breaking(items, cfg, daily):
    cutoff = NOW - timedelta(hours=cfg["breaking_max_age_hours"])
    daily_ids = {d["id"] for d in daily}
    fresh = sorted((i for i in items if i["published"] >= cutoff and i["id"] not in daily_ids),
                   key=lambda i: i["published"], reverse=True)
    chosen, ids = [], set()
    for i in fresh:
        if len(chosen) >= cfg["breaking_max"]:
            break
        if not is_duplicate(i, chosen + daily, ids):
            chosen.append(i)
            ids.add(i["id"])
    return chosen


def select_trending(items, cfg):
    chosen, ids = [], set()
    # Business-related trends first, then the general top trends in India.
    for i in sorted(items, key=lambda i: (i["category"] != "Business", i["_rank"])):
        if len(chosen) >= cfg["trending_max"]:
            break
        if not is_duplicate(i, chosen, ids):
            chosen.append(i)
            ids.add(i["id"])
    return chosen


def public(item):
    return {
        "id": item["id"],
        "title": item["title"],
        "link": item["link"],
        "source": item["source"],
        "category": item["category"],
        "published": item["published"].strftime("%Y-%m-%dT%H:%M:%SZ"),
        "summary": item["summary"],
    }


# ---------------------------------------------------------------- main

def main():
    with open(FEEDS_FILE, encoding="utf-8") as f:
        conf = json.load(f)
    cfg = conf["settings"]
    max_words = cfg.get("summary_max_words", 100)
    matchers = build_matchers(conf["categories"])

    daily_raw, d_ok, d_fail = load_all(conf["daily"], max_words, matchers)
    breaking_raw, b_ok, b_fail = load_all(conf["breaking"], max_words, matchers)
    trend_raw, t_ok, t_fail = [], [], []
    for src in conf["trending"]:                       # use the first trends address that works
        trend_raw, ok, fail = load_all([src], max_words, matchers)
        t_ok += ok
        t_fail += fail
        if trend_raw:
            break

    daily = select_daily(daily_raw, cfg)
    breaking = select_breaking(breaking_raw, cfg, daily)
    trending = select_trending(trend_raw, cfg)

    print("Sources OK:\n  " + "\n  ".join(d_ok + b_ok + t_ok))
    if d_fail or b_fail or t_fail:
        print("Sources skipped (will retry next run):\n  " + "\n  ".join(d_fail + b_fail + t_fail))
    print(f"Daily: {len(daily)}  Breaking: {len(breaking)}  Trending: {len(trending)}")

    if not (daily or breaking or trending):
        print("No items fetched at all; keeping the previous feed.json.")
        sys.exit(1)

    out = {
        "generated": NOW.strftime("%Y-%m-%dT%H:%M:%SZ"),
        "daily": [public(i) for i in daily],
        "breaking": [public(i) for i in breaking],
        "trending": [public(i) for i in trending],
        "skipped_sources": d_fail + b_fail + t_fail,
    }
    os.makedirs(os.path.dirname(OUT_FILE), exist_ok=True)
    with open(OUT_FILE, "w", encoding="utf-8") as f:
        json.dump(out, f, ensure_ascii=False, indent=1)


if __name__ == "__main__":
    main()
