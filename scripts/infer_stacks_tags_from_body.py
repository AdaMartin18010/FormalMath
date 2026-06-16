#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
从正文已有的 Stacks Project tag URL 中推断精确标签，并写入 frontmatter external_ids。

用法：
    python scripts/infer_stacks_tags_from_body.py
"""

import re
import yaml
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]
TAG_RE = re.compile(r"https?://stacks\.math\.columbia\.edu/tag/([A-Z0-9]{4})")


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


def existing_tags(fm: dict):
    ext = fm.get("external_ids") or {}
    tags = set()
    single = ext.get("stacks_tag")
    if isinstance(single, dict):
        tags.add(single.get("tag"))
    elif isinstance(single, str):
        tags.add(single)
    multi = ext.get("stacks_tags")
    if isinstance(multi, list):
        for item in multi:
            if isinstance(item, dict):
                tags.add(item.get("tag"))
            elif isinstance(item, str):
                tags.add(item)
    return tags


def inject_tags(doc_path: Path, tags: set):
    text = doc_path.read_text(encoding="utf-8", errors="ignore")
    fm, body = parse_frontmatter(text)
    if fm is None:
        return False

    ext = fm.get("external_ids") or {}
    old = existing_tags(fm)
    new = tags - old
    if not new:
        return False

    all_tags = old | new
    multi = [{"tag": t, "url": f"https://stacks.math.columbia.edu/tag/{t}"} for t in sorted(all_tags)]
    if len(multi) == 1:
        ext["stacks_tag"] = multi[0]
    else:
        ext["stacks_tag"] = multi[0]
        ext["stacks_tags"] = multi

    fm["external_ids"] = ext

    refs = fm.get("references") or {}
    databases = refs.get("databases") or []
    entry = next((db for db in databases if isinstance(db, dict) and db.get("id") == "stacks_project"), None)
    if entry is None:
        databases.append({
            "id": "stacks_project",
            "type": "database",
            "name": "Stacks Project",
            "entry_url": f"https://stacks.math.columbia.edu/tag/{multi[0]['tag']}",
            "tags": [t["tag"] for t in multi],
            "consulted_at": "2026-04-17",
        })
    else:
        entry["entry_url"] = f"https://stacks.math.columbia.edu/tag/{multi[0]['tag']}"
        entry["tags"] = [t["tag"] for t in multi]
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
        text = doc_path.read_text(encoding="utf-8", errors="ignore")
        tags = set(TAG_RE.findall(text))
        if not tags:
            continue
        if inject_tags(doc_path, tags):
            changed += 1
            print(f"  {doc_path.relative_to(PROJECT_ROOT)} <- {sorted(tags)}")
    print(f"\nInjected stacks tags into {changed} docs.")


if __name__ == "__main__":
    main()
