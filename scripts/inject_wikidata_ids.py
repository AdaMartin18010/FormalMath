#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
为数学家理念体系文档注入 Wikidata QID。

基于已有的 en.wikipedia.org URL，批量查询 Wikidata API，仅当对应实体为
人（Q5）且职业包含数学家（Q170790）等时才注入 external_ids.wikidata_id。
"""

import re
import time
import yaml
import urllib.request
import urllib.parse
from pathlib import Path
from datetime import date

PROJECT_ROOT = Path(__file__).resolve().parents[1]
MATH_DIR = PROJECT_ROOT / "数学家理念体系"
WIKI_RE = re.compile(r"https?://en\.wikipedia\.org/wiki/([^/#?\s]+)")

OCCUPATION_OK = {
    "Q170790",   # mathematician
    "Q82594",    # computer scientist
    "Q169470",   # physicist
    "Q3745071",  # logician
    "Q11063",    # astronomer
    "Q593644",   # philosopher
    "Q81096",    # engineer
}


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


def fetch_wikidata(titles):
    if not titles:
        return {}
    url = (
        "https://www.wikidata.org/w/api.php"
        + "?action=wbgetentities"
        + "&sites=enwiki"
        + "&titles=" + urllib.parse.quote("|".join(titles))
        + "&props=claims|sitelinks"
        + "&format=json"
    )
    req = urllib.request.Request(url, headers={"User-Agent": "FormalMath-Wikidata/1.0 (research@formalmath.example)"})
    for attempt in range(3):
        try:
            with urllib.request.urlopen(req, timeout=20) as resp:
                data = yaml.safe_load(resp.read().decode("utf-8"))
            return data.get("entities", {})
        except urllib.error.HTTPError as e:
            if e.code == 403:
                wait = 2 ** attempt
                print(f"Wikidata rate limit, sleeping {wait}s...")
                time.sleep(wait)
                continue
            print(f"Wikidata API error: {e}")
            return {}
        except Exception as e:
            print(f"Wikidata API error: {e}")
            return {}
    return {}


def is_relevant_mathematician(entity: dict):
    claims = entity.get("claims", {})
    # instance of human Q5
    instances = {c.get("mainsnak", {}).get("datavalue", {}).get("value", {}).get("id")
                 for c in claims.get("P31", [])}
    if "Q5" not in instances:
        return False
    occupations = {c.get("mainsnak", {}).get("datavalue", {}).get("value", {}).get("id")
                   for c in claims.get("P106", [])}
    if occupations & OCCUPATION_OK:
        return True
    return False


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
    title_to_paths = {}
    for doc_path in MATH_DIR.rglob("*.md"):
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

    injected = 0
    for i in range(0, len(titles), 50):
        batch = titles[i : i + 50]
        entities = fetch_wikidata(batch)
        for qid, entity in entities.items():
            if not is_relevant_mathematician(entity):
                continue
            sitelink = (entity.get("sitelinks") or {}).get("enwiki", {})
            en_title = sitelink.get("title")
            if not en_title:
                continue
            for doc_path in title_to_paths.get(en_title, []):
                if inject(doc_path, qid):
                    injected += 1
        time.sleep(1.5)

    print(f"Injected Wikidata QID into {injected} mathematician docs.")


if __name__ == "__main__":
    main()
