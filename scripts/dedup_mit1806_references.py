#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
清理 MIT 18.06 线性代数文档 frontmatter 中的重复引用项。
"""

import yaml
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]
COURSE_DIR = PROJECT_ROOT / "docs" / "00-银层核心课程" / "MIT-18.06-线性代数"


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


def dedup_textbooks(textbooks):
    seen = {}
    for tb in textbooks:
        key = (tb.get("title", ""), tb.get("author", ""), tb.get("edition", ""))
        if key not in seen:
            seen[key] = tb
        else:
            # 合并字段
            existing = seen[key]
            for k, v in tb.items():
                if v and not existing.get(k):
                    existing[k] = v
    return list(seen.values())


def dedup_lectures(lectures):
    seen = {}
    for lec in lectures:
        url = lec.get("url", "")
        # 跳过课程主页链接，保留具体讲座链接
        if url.endswith("18-06-linear-algebra-spring-2010/"):
            continue
        if url not in seen:
            seen[url] = lec
        else:
            existing = seen[url]
            for k, v in lec.items():
                if v and not existing.get(k):
                    existing[k] = v
    return list(seen.values())


def main():
    updated = 0
    for md_file in sorted(COURSE_DIR.glob("Ch*.md")):
        text = md_file.read_text(encoding="utf-8", errors="ignore")
        fm, body = parse_frontmatter(text)
        if fm is None:
            continue
        refs = fm.get("references") or {}
        if refs.get("textbooks"):
            refs["textbooks"] = dedup_textbooks(refs["textbooks"])
        if refs.get("lectures"):
            refs["lectures"] = dedup_lectures(refs["lectures"])
        fm["references"] = refs

        # 修正 prerequisites 为上一章具体路径
        chapter = int(fm.get("chapter", 0))
        if chapter > 1:
            prev = f"docs/00-银层核心课程/MIT-18.06-线性代数/Ch{chapter-1:02d}-*.md"
            fm["prerequisites"] = [prev]
        else:
            fm["prerequisites"] = ["docs/00-银层核心课程/MIT-18.02-多变量微积分/"]

        new_text = "---\n" + yaml.safe_dump(
            fm, allow_unicode=True, sort_keys=False, default_flow_style=False
        ) + "---\n" + body
        md_file.write_text(new_text, encoding="utf-8")
        updated += 1
    print(f"Deduped {updated} files.")


if __name__ == "__main__":
    main()
