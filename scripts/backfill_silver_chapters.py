#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
为无法从文件名推断章节的银层核心课程文档补充 chapter。

用法：
    python scripts/backfill_silver_chapters.py
"""

import yaml
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]

CHAPTER_MAP = {
    # MIT 18.100A
    ("MIT 18.100A", "确界原理与Archimedean性质"): "1",
    ("MIT 18.100A", "介值定理"): "3",
    ("MIT 18.100A", "一致连续性"): "3",
    ("MIT 18.100A", "中值定理"): "4",
    ("MIT 18.100A", "Taylor定理"): "4",
    ("MIT 18.100A", "比较判别法"): "2",
    ("MIT 18.100A", "比值根值判别法"): "2",
    ("MIT 18.100A", "Weierstrass-M判别法"): "5",

    # MIT 18.701
    ("MIT 18.701", "拉格朗日定理"): "2",
    ("MIT 18.701", "群第一同构定理"): "2",
    ("MIT 18.701", "Cauchy定理"): "2",
    ("MIT 18.701", "Sylow第一定理"): "6",
    ("MIT 18.701", "轨道稳定子定理"): "2",
    ("MIT 18.701", "环第一同构定理"): "10",
    ("MIT 18.701", "多项式环唯一分解定理"): "10",

    # 其他
    ("IMO", "IMO真题-代数1"): "1",
    ("Green", "Green定理-自然语言与Lean4对照"): "10",
}


def lookup_chapter(course: str, title: str, stem: str):
    for (c, t), ch in CHAPTER_MAP.items():
        course_match = (not course and (c in title or c in stem)) or (course and c in course)
        if course_match and (t in title or t in stem):
            return ch
    # 学习诊断手册统一归为附录/诊断章
    if "学习诊断手册" in title or "学习诊断手册" in stem:
        return "0"
    return None


def parse_frontmatter(text: str):
    if text.startswith("---"):
        end = text.find("---", 3)
        if end != -1:
            fm_text = text[3:end].strip()
            body = text[end + 3 :].strip()
            try:
                return yaml.safe_load(fm_text) or {}, fm_text, body
            except yaml.YAMLError:
                return None, fm_text, body
    return {}, "", text


def process_file(path: Path):
    text = path.read_text(encoding="utf-8", errors="ignore")
    fm, fm_text, body = parse_frontmatter(text)
    if fm is None or fm.get("level") != "silver":
        return None
    if fm.get("chapter"):
        return None
    course = fm.get("course", "")
    title = fm.get("title", "")
    stem = path.stem
    chapter = lookup_chapter(course, title, stem)
    if chapter is None:
        return None

    # 为特殊银层文档补充 course 占位
    if not course:
        if "IMO" in stem or "IMO" in title:
            fm["course"] = "IMO 竞赛数学"
        elif "Green" in stem or "Green" in title:
            fm["course"] = "向量微积分"

    fm["chapter"] = chapter
    new_text = (
        "---\n"
        + yaml.safe_dump(fm, allow_unicode=True, sort_keys=False, default_flow_style=False)
        + "---\n"
        + body
    )
    path.write_text(new_text, encoding="utf-8")
    return chapter


def main():
    changed = 0
    for p in PROJECT_ROOT.rglob("*.md"):
        if any(x in p.parts for x in ("node_modules", ".git", "00-归档", "归档")):
            continue
        chapter = process_file(p)
        if chapter:
            changed += 1
            print(f"  {p.relative_to(PROJECT_ROOT)}: chapter -> {chapter}")
    print(f"\nUpdated {changed} docs.")


if __name__ == "__main__":
    main()
