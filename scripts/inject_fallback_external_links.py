#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
为尚未获得精确外部链接映射的数学内容文档，注入 nLab / Wikipedia 搜索链接作为兜底对齐。

用法：
    python scripts/inject_fallback_external_links.py
"""

import yaml
from pathlib import Path
from urllib.parse import quote

PROJECT_ROOT = Path(__file__).resolve().parents[1]

REPORT_MARKERS = ["报告", "进度", "日报", "总结", "计划", "索引", "README", "FAQ", "指南", "模板", "清单", "对齐", "课程表", "Syllabus"]


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


def is_report_like(title: str, stem: str):
    if stem.startswith("00-"):
        return True
    if any(m in title or m in stem for m in REPORT_MARKERS):
        return True
    return False


def main():
    roots = [
        PROJECT_ROOT / "docs",
        PROJECT_ROOT / "concept",
        PROJECT_ROOT / "数学家理念体系",
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
            title = str(fm.get("title", "")).strip()
            stem = p.stem
            if not title or is_report_like(title, stem):
                continue
            external_ids = fm.get("external_ids") or {}
            if external_ids:
                continue

            # 使用标题作为搜索关键词
            query = title.replace(" ", "+").replace("_", " ")
            external_ids["wikipedia_search_url"] = f"https://en.wikipedia.org/wiki/Special:Search?search={quote(query)}"
            external_ids["nlab_search_url"] = f"https://ncatlab.org/nlab/search?query={quote(query)}"
            fm["external_ids"] = external_ids

            new_text = (
                "---\n"
                + yaml.safe_dump(fm, allow_unicode=True, sort_keys=False, default_flow_style=False)
                + "---\n"
                + body
            )
            p.write_text(new_text, encoding="utf-8")
            changed += 1

    print(f"Injected fallback external links into {changed} docs.")


if __name__ == "__main__":
    main()
