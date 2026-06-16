#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
根据 ref/Stacks-Project-Tag-对齐映射表.md 中的映射，
向对应 FormalMath 文档注入 external_ids.stacks_tag。

用法：
    python scripts/inject_stacks_tags_from_mapping.py
"""

import yaml
import re
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]
MAPPING_FILE = PROJECT_ROOT / "ref" / "Stacks-Project-Tag-对齐映射表.md"


def parse_frontmatter(text: str):
    if text.startswith("---"):
        end = text.find("---", 3)
        if end != -1:
            fm_text = text[3:end].strip()
            body = text[end + 3 :].strip()
            try:
                return yaml.safe_load(fm_text) or {}, body
            except yaml.YAMLError:
                return None, body
    return {}, text


def parse_mapping_table(content: str):
    """从 Markdown 表格中提取 (tag, doc_path) 映射。"""
    rows = []
    for line in content.splitlines():
        line = line.strip()
        if not line.startswith("|") or "Stacks Tag" in line or "---" in line:
            continue
        cells = [c.strip() for c in line.strip("|").split("|")]
        if len(cells) < 5:
            continue
        tag = cells[0]
        doc_ref = cells[3]
        status = cells[4]
        if not tag or not doc_ref or tag.lower() == "stacks tag":
            continue
        if status == "❌ 暂不适用":
            continue
        # doc_ref 形如 `docs/.../xxx.md`
        m = re.search(r"`([^`]+\.(?:md|lean))`", doc_ref)
        if not m:
            continue
        path = m.group(1)
        rows.append((tag, path))
    return rows


def process_doc(doc_path: Path, tag: str):
    if not doc_path.exists():
        return False
    text = doc_path.read_text(encoding="utf-8", errors="ignore")
    fm, body = parse_frontmatter(text)
    if fm is None:
        return False

    external_ids = fm.get("external_ids") or {}
    tag_url = f"https://stacks.math.columbia.edu/tag/{tag}"
    existing = external_ids.get("stacks_tag")
    if isinstance(existing, dict):
        if existing.get("tag") == tag:
            return False
    elif existing == tag:
        return False

    external_ids["stacks_tag"] = {"tag": tag, "url": tag_url}
    fm["external_ids"] = external_ids

    # 如果文档已有 references，追加 Stacks Project 数据库引用
    refs = fm.get("references") or {}
    databases = refs.get("databases") or []
    if not any(db.get("id") == "stacks_project" for db in databases):
        databases.append({
            "id": "stacks_project",
            "type": "database",
            "name": "Stacks Project",
            "entry_url": "https://stacks.math.columbia.edu/tag/{tag}",
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
    content = MAPPING_FILE.read_text(encoding="utf-8", errors="ignore")
    mappings = parse_mapping_table(content)
    print(f"Found {len(mappings)} usable mappings in {MAPPING_FILE.name}")

    changed = 0
    skipped = 0
    for tag, rel_path in mappings:
        doc_path = PROJECT_ROOT / rel_path
        if process_doc(doc_path, tag):
            changed += 1
            print(f"  {rel_path} <- {tag}")
        else:
            skipped += 1
    print(f"\nInjected stacks_tag into {changed} docs, skipped {skipped}.")


if __name__ == "__main__":
    main()
