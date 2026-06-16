#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
为所有含 en.wikipedia.org URL 的文档注入 Wikidata QID。

基于 `external_ids.wikipedia_url`，查询 Wikidata API，将对应的 QID 写入
external_ids.wikidata_id 与 references.databases.wikidata。
"""

import re
import time
import yaml
import json
import urllib.request
import urllib.error
import urllib.parse
from pathlib import Path
from datetime import date

PROJECT_ROOT = Path(__file__).resolve().parents[1]
CACHE_PATH = PROJECT_ROOT / ".test_cache" / "wikidata_title_cache.json"
WIKI_RE = re.compile(r"https?://en\.wikipedia\.org/wiki/([^/#?\s]+)")


def parse_frontmatter(text: str):
    if text.startswith("---"):
        end = text.find("---", 3)
        if end != -1:
            fm_text = text[3:end].strip()
            body = text[end + 3 :].lstrip("\n")
            try:
                return yaml.safe_load(fm_text) or {}, body, fm_text
            except yaml.YAMLError:
                return None, body, fm_text
    return {}, text, ""


def wiki_title(url: str):
    m = WIKI_RE.search(url)
    if not m:
        return None
    return urllib.parse.unquote(m.group(1).replace("_", " "))


def load_cache():
    if CACHE_PATH.exists():
        try:
            return json.loads(CACHE_PATH.read_text(encoding="utf-8"))
        except Exception:
            return {}
    return {}


def save_cache(cache: dict):
    CACHE_PATH.parent.mkdir(parents=True, exist_ok=True)
    CACHE_PATH.write_text(json.dumps(cache, ensure_ascii=False, indent=2), encoding="utf-8")


def fetch_wikidata(titles, cache: dict):
    to_fetch = [t for t in titles if t not in cache]
    if not to_fetch:
        return cache
    for i in range(0, len(to_fetch), 50):
        batch = to_fetch[i : i + 50]
        url = (
            "https://www.wikidata.org/w/api.php"
            + "?action=wbgetentities"
            + "&sites=enwiki"
            + "&titles=" + urllib.parse.quote("|".join(batch))
            + "&props=sitelinks"
            + "&format=json"
        )
        req = urllib.request.Request(url, headers={"User-Agent": "FormalMath-Wikidata/1.0 (research@formalmath.example)"})
        for attempt in range(3):
            try:
                with urllib.request.urlopen(req, timeout=20) as resp:
                    data = yaml.safe_load(resp.read().decode("utf-8"))
                for qid, entity in (data or {}).get("entities", {}).items():
                    if qid.startswith("Q"):
                        sitelink = (entity.get("sitelinks") or {}).get("enwiki", {})
                        en_title = sitelink.get("title")
                        if en_title:
                            cache[en_title] = qid
                break
            except urllib.error.HTTPError as e:
                if e.code == 403:
                    wait = 2 ** attempt
                    print(f"Wikidata rate limit, sleeping {wait}s...")
                    time.sleep(wait)
                    continue
                print(f"Wikidata API error: {e}")
                break
            except Exception as e:
                print(f"Wikidata API error: {e}")
                break
        time.sleep(1.5)
    return cache


def inject(doc_path: Path, qid: str):
    text = doc_path.read_text(encoding="utf-8", errors="ignore")
    fm, body, fm_text = parse_frontmatter(text)
    if fm is None:
        return False
    ext = fm.get("external_ids") or {}
    if ext.get("wikidata_id") == qid:
        return False
    ext["wikidata_id"] = qid
    fm["external_ids"] = ext

    refs = fm.get("references") or {}
    databases = refs.get("databases") or []
    if not any(db.get("id") == "wikidata" for db in databases):
        databases.append({
            "id": "wikidata",
            "type": "database",
            "name": "Wikidata",
            "entry_url": f"https://www.wikidata.org/entity/{qid}",
            "consulted_at": str(date.today()),
        })
        refs["databases"] = databases
        fm["references"] = refs

    new_text = (
        "---\n"
        + yaml.safe_dump(fm, allow_unicode=True, sort_keys=False, default_flow_style=False)
        + "---\n"
        + body
    )
    doc_path.write_text(new_text, encoding="utf-8")
    return True


def main():
    cache = load_cache()
    title_to_paths = {}
    for doc_path in PROJECT_ROOT.rglob("*.md"):
        if ".git" in doc_path.parts:
            continue
        text = doc_path.read_text(encoding="utf-8", errors="ignore")
        fm, _, _ = parse_frontmatter(text)
        if fm is None:
            continue
        wiki_url = (fm.get("external_ids") or {}).get("wikipedia_url")
        if not wiki_url:
            continue
        title = wiki_title(wiki_url)
        if not title:
            continue
        title_to_paths.setdefault(title, []).append(doc_path)

    titles = list(title_to_paths.keys())
    print(f"Found {len(titles)} unique Wikipedia titles to query.")
    cache = fetch_wikidata(titles, cache)
    save_cache(cache)

    injected = 0
    for title, qid in cache.items():
        for doc_path in title_to_paths.get(title, []):
            if inject(doc_path, qid):
                injected += 1

    print(f"Injected Wikidata QID into {injected} docs.")


if __name__ == "__main__":
    main()
