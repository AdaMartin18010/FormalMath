#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
根据 ref/Stacks-Tag-解读/ 下的中文标签解读文件名，为核心数学概念文档注入 Stacks Project 精确 tag 链接。

用法：
    python scripts/inject_stacks_tags.py
"""

import re
import yaml
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]
STACKS_DIR = PROJECT_ROOT / "ref" / "Stacks-Tag-解读"

TAG_RE = re.compile(r"Tag-([0-9A-Z]{4})-(.+)\.md$")
REPORT_MARKERS = ["报告", "进度", "日报", "总结", "计划", "索引", "README", "FAQ", "指南", "模板", "清单"]


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


def load_tag_mapping():
    mapping = {}
    if not STACKS_DIR.exists():
        return mapping
    for p in STACKS_DIR.glob("Tag-*.md"):
        m = TAG_RE.match(p.name)
        if not m:
            continue
        tag, concept = m.groups()
        # 文件名中的概念可能含英文连字符，统一替换为空格
        concept = concept.replace("-", " ")
        # 只保留长度 ≥2 的关键词，避免过短误匹配
        if len(concept) >= 2:
            mapping.setdefault(concept, set()).add(tag)
    return mapping


def is_report_like(title: str, stem: str):
    if stem.startswith("00-"):
        return True
    if any(m in title or m in stem for m in REPORT_MARKERS):
        return True
    return False


def main():
    tag_map = load_tag_mapping()
    print(f"Loaded {len(tag_map)} concept -> Stacks tag mappings.")

    roots = [
        PROJECT_ROOT / "docs",
        PROJECT_ROOT / "concept",
        PROJECT_ROOT / "FormalMath-v2",
        PROJECT_ROOT / "FormalMathLean4",
    ]
    changed = 0
    for root in roots:
        if not root.exists():
            continue
        for p in root.rglob("*.md"):
            if any(x in p.parts for x in ("node_modules", ".git", "00-归档", "归档")):
                continue
            text = p.read_text(encoding="utf-8", errors="ignore")
            fm, body = parse_frontmatter(text)
            if fm is None:
                continue
            level = str(fm.get("level", "")).lower()
            if level in ("meta", "l0", "project"):
                continue
            title = str(fm.get("title", ""))
            stem = p.stem
            if is_report_like(title, stem):
                continue

            matched_tags = set()
            for concept, tags in tag_map.items():
                if concept in title or concept in stem:
                    matched_tags.update(tags)
            if not matched_tags:
                continue

            external_ids = fm.get("external_ids") or {}
            existing = set()
            for k in ("stacks_tag", "stacks_tag_url"):
                v = external_ids.get(k, "")
                if v:
                    existing.update(re.findall(r"tag/([A-Z0-9]{4})", str(v)))
            new_tags = sorted(matched_tags - existing)
            if not new_tags:
                continue

            base_url = "https://stacks.math.columbia.edu/tag/"
            current = external_ids.get("stacks_tag_url", "")
            parts = [current] if current else []
            for tag in new_tags:
                parts.append(f"{base_url}{tag}")
            external_ids["stacks_tag_url"] = "\n".join(parts)
            fm["external_ids"] = external_ids

            new_text = (
                "---\n"
                + yaml.safe_dump(fm, allow_unicode=True, sort_keys=False, default_flow_style=False)
                + "---\n"
                + body
            )
            p.write_text(new_text, encoding="utf-8")
            changed += 1

    print(f"Injected Stacks tag links into {changed} docs.")


if __name__ == "__main__":
    main()
