#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
批量规范化银层核心课程文档的 frontmatter。

功能：
1. 补全缺失的 level/course/chapter/msc_primary
2. 注入 external_ids（课程主页、教材 ISBN 等）
3. 注入标准化教材引用

用法：
    python scripts/normalize_silver_frontmatter.py
"""

import yaml
import re
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]
COURSES_DIR = PROJECT_ROOT / "docs" / "00-银层核心课程"

COURSE_META = {
    "MIT-18.06-线性代数": {
        "course_name": "MIT 18.06 线性代数",
        "course_name_en": "MIT 18.06 Linear Algebra",
        "msc_primary": 15,
        "ocw_url": "https://ocw.mit.edu/courses/mathematics/18-06-linear-algebra-spring-2010/",
        "ocw_ps_url": "https://ocw.mit.edu/courses/mathematics/18-06-linear-algebra-spring-2010/assignments/",
        "textbook": {
            "title": "Introduction to Linear Algebra",
            "author": "Gilbert Strang",
            "edition": "5th",
            "publisher": "Wellesley-Cambridge Press",
            "year": 2016,
            "isbn": "9780980232776",
        },
    },
    "MIT-18.100A-实分析": {
        "course_name": "MIT 18.100A 实分析",
        "course_name_en": "MIT 18.100A Real Analysis",
        "msc_primary": 26,
        "ocw_url": "https://ocw.mit.edu/courses/mathematics/18-100a-real-analysis-fall-2020/",
        "ocw_ps_url": "https://ocw.mit.edu/courses/mathematics/18-100a-real-analysis-fall-2020/pages/assignments/",
        "textbook": {
            "title": "Principles of Mathematical Analysis",
            "author": "Walter Rudin",
            "edition": "3rd",
            "publisher": "McGraw-Hill",
            "year": 1976,
            "isbn": "9780070542358",
        },
    },
    "MIT-18.701-抽象代数": {
        "course_name": "MIT 18.701 抽象代数",
        "course_name_en": "MIT 18.701 Algebra I",
        "msc_primary": 12,
        "ocw_url": "https://ocw.mit.edu/courses/mathematics/18-701-algebra-i-fall-2010/",
        "ocw_ps_url": "https://ocw.mit.edu/courses/mathematics/18-701-algebra-i-fall-2010/pages/assignments/",
        "textbook": {
            "title": "Algebra",
            "author": "Michael Artin",
            "edition": "2nd",
            "publisher": "Pearson",
            "year": 2010,
            "isbn": "9780132413770",
        },
    },
    "Harvard-232br-代数几何": {
        "course_name": "Harvard 232br 代数几何",
        "course_name_en": "Harvard Math 232br Algebraic Geometry II",
        "msc_primary": 14,
        "ocw_url": "https://www.math.harvard.edu/course/mathematics-232br/",
        "ocw_ps_url": "https://people.math.harvard.edu/~landesman/notes.html",
        "textbook": {
            "title": "Algebraic Geometry",
            "author": "Robin Hartshorne",
            "edition": "1st",
            "publisher": "Springer",
            "year": 1977,
            "isbn": "9780387902449",
        },
    },
    "Stanford-FOAG-基础代数几何": {
        "course_name": "Stanford FOAG 基础代数几何",
        "course_name_en": "Stanford FOAG Foundations of Algebraic Geometry",
        "msc_primary": 14,
        "ocw_url": "https://math.stanford.edu/~vakil/216blog/",
        "ocw_ps_url": "https://math.stanford.edu/~vakil/216blog/",
        "textbook": {
            "title": "The Rising Sea: Foundations of Algebraic Geometry",
            "author": "Ravi Vakil",
            "edition": "preprint",
            "publisher": "Stanford University",
            "year": 2022,
            "isbn": "",
        },
    },
    "MIT-18.02-多变量微积分": {
        "course_name": "MIT 18.02 多变量微积分",
        "course_name_en": "MIT 18.02 Multivariable Calculus",
        "msc_primary": 26,
        "ocw_url": "https://ocw.mit.edu/courses/mathematics/18-02sc-multivariable-calculus-fall-2010/",
        "ocw_ps_url": "https://ocw.mit.edu/courses/mathematics/18-02sc-multivariable-calculus-fall-2010/pages/problem-sets-and-exams/",
        "textbook": {
            "title": "Multivariable Calculus",
            "author": "Jerrold E. Marsden, Anthony J. Tromba",
            "edition": "6th",
            "publisher": "W. H. Freeman",
            "year": 2011,
            "isbn": "9781429215084",
        },
    },
    "Princeton-复分析": {
        "course_name": "Princeton 复分析",
        "course_name_en": "Princeton Complex Analysis",
        "msc_primary": 30,
        "ocw_url": "",
        "ocw_ps_url": "",
        "textbook": {
            "title": "Complex Analysis",
            "author": "Elias M. Stein, Rami Shakarchi",
            "edition": "1st",
            "publisher": "Princeton University Press",
            "year": 2003,
            "isbn": "9780691113852",
        },
    },
    "Oxford-表示论": {
        "course_name": "Oxford 表示论",
        "course_name_en": "Oxford Representation Theory",
        "msc_primary": 20,
        "ocw_url": "",
        "ocw_ps_url": "",
        "textbook": {
            "title": "Representation Theory: A First Course",
            "author": "William Fulton, Joe Harris",
            "edition": "1st",
            "publisher": "Springer",
            "year": 1991,
            "isbn": "9780387974958",
        },
    },
    "UCLA-微分几何": {
        "course_name": "UCLA 微分几何",
        "course_name_en": "UCLA Differential Geometry",
        "msc_primary": 53,
        "ocw_url": "",
        "ocw_ps_url": "",
        "textbook": {
            "title": "Differential Geometry of Curves and Surfaces",
            "author": "Manfredo P. do Carmo",
            "edition": "1st",
            "publisher": "Prentice-Hall",
            "year": 1976,
            "isbn": "9780132125895",
        },
    },
}


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


def infer_chapter(filename: str):
    """从文件名推断章节号"""
    patterns = [
        r"Ch(?:apter)?[\s_-]?(\d+)",
        r"^Ch(\d+)",
        r"^(\d{1,2})[\s_-]",
        r"Part(\w+)-L(\d+)",
        r"Part[\s_-]?(\w+)",
        r"^([IVX]+)[\s_-]",
    ]
    for pat in patterns:
        m = re.search(pat, filename, re.IGNORECASE)
        if m:
            return m.group(1)
    return ""


def normalize_frontmatter(fm: dict, course_key: str, chapter: str):
    meta = COURSE_META.get(course_key)
    if not meta:
        return fm, []

    changes = []

    if fm.get("level") != "silver":
        fm["level"] = "silver"
        changes.append("level")

    if not fm.get("course"):
        fm["course"] = meta["course_name"]
        changes.append("course")

    if not fm.get("chapter"):
        fm["chapter"] = chapter
        changes.append("chapter")

    if not fm.get("msc_primary"):
        fm["msc_primary"] = meta["msc_primary"]
        changes.append("msc_primary")

    external_ids = fm.get("external_ids") or {}
    if not external_ids.get("ocw_url") and meta.get("ocw_url"):
        external_ids["ocw_url"] = meta["ocw_url"]
        changes.append("external_ids.ocw_url")
    if not external_ids.get("ocw_ps_url") and meta.get("ocw_ps_url"):
        external_ids["ocw_ps_url"] = meta["ocw_ps_url"]
        changes.append("external_ids.ocw_ps_url")
    if external_ids:
        fm["external_ids"] = external_ids

    refs = fm.get("references") or {}
    textbooks = refs.get("textbooks") or []
    isbns = {str(tb.get("isbn", "")) for tb in textbooks}
    if meta["textbook"].get("isbn") and meta["textbook"]["isbn"] not in isbns:
        textbooks.append(meta["textbook"])
        refs["textbooks"] = textbooks
        changes.append("references.textbooks")
    if refs:
        fm["references"] = refs

    return fm, changes


def main():
    changed_files = []
    skipped = []

    for course_dir in sorted(COURSES_DIR.iterdir()):
        if not course_dir.is_dir():
            continue
        course_key = course_dir.name
        if course_key not in COURSE_META:
            continue
        for md_file in sorted(course_dir.rglob("*.md")):
            if md_file.name.startswith("INDEX"):
                continue
            text = md_file.read_text(encoding="utf-8", errors="ignore")
            fm, body = parse_frontmatter(text)
            if fm is None:
                skipped.append(str(md_file.relative_to(PROJECT_ROOT)))
                continue
            chapter = fm.get("chapter") or infer_chapter(md_file.stem)
            new_fm, changes = normalize_frontmatter(fm, course_key, chapter)
            if changes:
                new_text = "---\n" + yaml.safe_dump(
                    new_fm,
                    allow_unicode=True,
                    sort_keys=False,
                    default_flow_style=False,
                ) + "---\n" + body
                md_file.write_text(new_text, encoding="utf-8")
                changed_files.append((str(md_file.relative_to(PROJECT_ROOT)), changes))

    print(f"Updated {len(changed_files)} files.")
    if skipped:
        print(f"Skipped {len(skipped)} files due to frontmatter parse errors.")
    for rel, changes in changed_files[:20]:
        print(f"  {rel}: {', '.join(changes)}")
    if len(changed_files) > 20:
        print(f"  ... and {len(changed_files) - 20} more")


if __name__ == "__main__":
    main()
