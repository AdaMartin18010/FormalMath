#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
清理 frontmatter 中占位符形式的数据库 entry_url 和 external_ids URL，避免链接校验误报。

用法：
    python scripts/cleanup_placeholder_database_urls.py
"""

import re
import yaml
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]

PLACEHOLDER_PATTERNS = [
    re.compile(r"\{[^}]*\}"),
    re.compile(r"/nlab/show/\s*$"),
    re.compile(r"/tag/\s*$"),
    re.compile(r"\?q=an\s*$"),
    re.compile(r"\?q=au\s*$"),
    re.compile(r"\?q=au:\s*$"),
    re.compile(r"\?query=\s*$"),
]


def is_placeholder_url(url):
    if not isinstance(url, str):
        return True
    if not url.startswith("http"):
        return True
    for pat in PLACEHOLDER_PATTERNS:
        if pat.search(url):
            return True
    return False


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


def clean_doc(doc_path: Path):
    text = doc_path.read_text(encoding="utf-8", errors="ignore")
    fm, body = parse_frontmatter(text)
    if fm is None:
        return False
    changed = False

    # 清理 external_ids 中的占位 URL
    ext = fm.get("external_ids") or {}
    for key in list(ext.keys()):
        val = ext[key]
        if isinstance(val, str) and is_placeholder_url(val):
            del ext[key]
            changed = True
        elif isinstance(val, list):
            cleaned = [u for u in val if not is_placeholder_url(u)]
            if len(cleaned) != len(val):
                ext[key] = cleaned
                changed = True
    if ext:
        fm["external_ids"] = ext
    elif "external_ids" in fm:
        del fm["external_ids"]
        changed = True

    # 清理 references.databases
    refs = fm.get("references") or {}
    databases = refs.get("databases") or []
    new_dbs = []
    for db in databases:
        if not isinstance(db, dict):
            continue
        entry_url = db.get("entry_url", "")
        db_id = db.get("id", "")
        # 如果占位，尝试用 external_ids 精确 URL 替换
        if is_placeholder_url(entry_url):
            replacement = None
            if db_id == "nlab" and not is_placeholder_url(ext.get("nlab_url")):
                replacement = ext["nlab_url"]
            elif db_id == "wikipedia" and not is_placeholder_url(ext.get("wikipedia_url")):
                replacement = ext["wikipedia_url"]
            elif db_id == "mactutor" and not is_placeholder_url(ext.get("mactutor_url")):
                replacement = ext["mactutor_url"]
            elif db_id == "zbmath" and not is_placeholder_url(ext.get("zbmath_url")):
                replacement = ext["zbmath_url"]
            elif db_id == "stacks_project":
                st = ext.get("stacks_tag")
                if isinstance(st, dict) and not is_placeholder_url(st.get("url")):
                    replacement = st["url"]
            if replacement:
                db["entry_url"] = replacement
                new_dbs.append(db)
                changed = True
            else:
                # 无法替换则移除
                changed = True
                continue
        else:
            new_dbs.append(db)
    if new_dbs:
        refs["databases"] = new_dbs
    elif "databases" in refs:
        del refs["databases"]
        changed = True
    if refs:
        fm["references"] = refs
    elif "references" in fm:
        del fm["references"]
        changed = True

    if not changed:
        return False

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
        if clean_doc(doc_path):
            changed += 1
    print(f"Cleaned placeholder URLs in {changed} docs.")


if __name__ == "__main__":
    main()
