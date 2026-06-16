#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
为已有 Wikipedia 链接的数学家文档补充 MacTutor 传记链接（从英文姓氏推断）。

用法：
    python scripts/inject_mathematician_mactutor.py
"""

import re
import yaml
import urllib.parse
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]
MATH_DIR = PROJECT_ROOT / "数学家理念体系"
WIKI_RE = re.compile(r"https?://en\.wikipedia\.org/wiki/([^/#?\s]+)")


def parse_frontmatter(text: str):
    if text.startswith("---"):
        end = text.find("---", 3)
        if end != -1:
            fm_text = text[3:end].strip()
            body = text[end + 3 :].lstrip("\n")
            try:
                return yaml.safe_load(fm_text) or {}, body
            except yaml.YAMLError:
                return None, body
    return {}, text


def derive_mactutor_id(wiki_url: str):
    m = WIKI_RE.search(wiki_url)
    if not m:
        return None
    title = urllib.parse.unquote(m.group(1).replace("_", " "))
    title = re.sub(r"\s*\([^)]*\)\s*$", "", title)
    parts = title.split()
    if not parts:
        return None
    # MacTutor ID 多为姓氏；单人名则取全名
    candidate = parts[-1]
    if not candidate:
        return None
    return candidate


def inject_mactutor(doc_path: Path):
    text = doc_path.read_text(encoding="utf-8", errors="ignore")
    fm, body = parse_frontmatter(text)
    if fm is None:
        return False
    ext = fm.get("external_ids") or {}
    wiki_url = ext.get("wikipedia_url")
    if not wiki_url or ext.get("mactutor_url"):
        return False
    mactutor_id = derive_mactutor_id(wiki_url)
    if not mactutor_id:
        return False
    mac_url = f"https://mathshistory.st-andrews.ac.uk/Biographies/{mactutor_id}/"
    ext["mactutor_url"] = mac_url
    fm["external_ids"] = ext

    refs = fm.get("references") or {}
    databases = refs.get("databases") or []
    if not any(db.get("id") == "mactutor" for db in databases):
        databases.append({
            "id": "mactutor",
            "type": "database",
            "name": "MacTutor History of Mathematics",
            "entry_url": mac_url,
            "consulted_at": "2026-04-17",
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
    changed = 0
    skipped_archives = {"00-归档", "00-归档-2026年4月-其他数学家"}
    for doc_path in MATH_DIR.rglob("*.md"):
        if any(p in doc_path.parts for p in skipped_archives):
            continue
        if inject_mactutor(doc_path):
            changed += 1
    print(f"Injected mactutor_url into {changed} mathematician docs.")


if __name__ == "__main__":
    main()
