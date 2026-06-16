#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
将 references.databases 中的占位 entry_url 同步为 external_ids 中的精确 URL。

用法：
    python scripts/sync_database_entry_urls.py
"""

import re
import yaml
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]


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


def is_placeholder(url):
    return not url or "{" in url


def sync_doc(doc_path: Path):
    text = doc_path.read_text(encoding="utf-8", errors="ignore")
    fm, body = parse_frontmatter(text)
    if fm is None:
        return False
    ext = fm.get("external_ids") or {}
    refs = fm.get("references") or {}
    databases = refs.get("databases") or []
    changed = False

    id_to_url = {}
    if not is_placeholder(ext.get("nlab_url")):
        id_to_url["nlab"] = ext["nlab_url"]
    if not is_placeholder(ext.get("wikipedia_url")):
        id_to_url["wikipedia"] = ext["wikipedia_url"]
    if not is_placeholder(ext.get("mactutor_url")):
        id_to_url["mactutor"] = ext["mactutor_url"]
    if not is_placeholder(ext.get("zbmath_url")):
        id_to_url["zbmath"] = ext["zbmath_url"]
    stacks_tag = ext.get("stacks_tag")
    if isinstance(stacks_tag, dict) and stacks_tag.get("url"):
        id_to_url["stacks_project"] = stacks_tag["url"]

    for db in databases:
        if not isinstance(db, dict):
            continue
        db_id = db.get("id")
        if db_id in id_to_url and is_placeholder(db.get("entry_url")):
            db["entry_url"] = id_to_url[db_id]
            changed = True

    if not changed:
        return False
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
    for doc_path in PROJECT_ROOT.rglob("*.md"):
        if ".git" in doc_path.parts:
            continue
        if sync_doc(doc_path):
            changed += 1
    print(f"Synced database entry URLs in {changed} docs.")


if __name__ == "__main__":
    main()
