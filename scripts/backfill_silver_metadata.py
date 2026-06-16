#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
回填银层文档缺失的 course / chapter / external_ids / references 元数据。

用法：
    python scripts/backfill_silver_metadata.py
"""

import yaml
import re
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]

COURSE_META = {
    "MIT-18.06-线性代数": {
        "course": "MIT 18.06 线性代数",
        "course_en": "MIT 18.06 Linear Algebra",
        "msc_primary": "15-01",
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
        "course": "MIT 18.100A 实分析",
        "course_en": "MIT 18.100A Real Analysis",
        "msc_primary": "26-01",
        "ocw_url": "https://ocw.mit.edu/courses/mathematics/18-100a-real-analysis-fall-2020/",
        "ocw_ps_url": "https://ocw.mit.edu/courses/mathematics/18-100a-real-analysis-fall-2020/pages/assignments/",
        "textbook": {
            "title": "Understanding Analysis",
            "author": "Stephen Abbott",
            "edition": "2nd",
            "publisher": "Springer",
            "year": 2015,
            "isbn": "9781493927111",
        },
    },
    "MIT-18.701-抽象代数": {
        "course": "MIT 18.701 抽象代数",
        "course_en": "MIT 18.701 Algebra I",
        "msc_primary": "12-01",
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
        "course": "Harvard 232br 代数几何",
        "course_en": "Harvard Math 232br Algebraic Geometry II",
        "msc_primary": "14-01",
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
        "course": "Stanford FOAG 基础代数几何",
        "course_en": "Stanford FOAG Foundations of Algebraic Geometry",
        "msc_primary": "14-01",
        "ocw_url": "https://math.stanford.edu/~vakil/216blog/",
        "ocw_ps_url": "https://math.stanford.edu/~vakil/216blog/",
        "textbook": {
            "title": "The Rising Sea: Foundations of Algebraic Geometry",
            "author": "Ravi Vakil",
            "edition": "draft",
            "publisher": "Stanford University",
            "year": 2024,
            "isbn": "",
        },
    },
    "MIT-18.02-多变量微积分": {
        "course": "MIT 18.02 多变量微积分",
        "course_en": "MIT 18.02 Multivariable Calculus",
        "msc_primary": "26-01",
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
}

COURSE_DIR_PATTERNS = {
    "MIT-18.06-线性代数": re.compile(r"MIT[-_]?18\.06|18\.06-线性代数"),
    "MIT-18.100A-实分析": re.compile(r"MIT[-_]?18\.100A|18\.100A-实分析"),
    "MIT-18.701-抽象代数": re.compile(r"MIT[-_]?18\.701|18\.701-抽象代数"),
    "Harvard-232br-代数几何": re.compile(r"Harvard[-_]?232br|232br-代数几何"),
    "Stanford-FOAG-基础代数几何": re.compile(r"Stanford[-_]?FOAG|FOAG-基础代数几何"),
    "MIT-18.02-多变量微积分": re.compile(r"MIT[-_]?18\.02|18\.02-多变量微积分|18\.02-多元微积分"),
}


def infer_course(path: Path):
    rel = str(path.relative_to(PROJECT_ROOT))
    for key, pat in COURSE_DIR_PATTERNS.items():
        if pat.search(rel):
            return key
    return None


def infer_chapter(filename: str):
    patterns = [
        r"Ch(?:apter)?[\s_-]?(\d+)",
        r"^Ch(\d+)",
        r"^(\d{1,2})[\s_-]",
        r"Part(\w+)-L(\d+)",
        r"Part[\s_-]?(\w+)",
        r"^([IVX]+)[\s_-]",
        r"II\.(\d+)",
        r"III\.(\d+)",
        r"IV\.(\d+)",
        r"V\.(\d+)",
    ]
    for pat in patterns:
        m = re.search(pat, filename, re.IGNORECASE)
        if m:
            return m.group(1)
    return ""


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


def merge_textbooks(existing: list, new: dict):
    isbn = str(new.get("isbn", "")).replace("-", "")
    for tb in existing:
        tb_isbn = str(tb.get("isbn", "")).replace("-", "")
        if tb_isbn and tb_isbn == isbn:
            return existing
        if tb.get("title") == new.get("title") and tb.get("author") == new.get("author"):
            return existing
    existing.append(new)
    return existing


def process_file(path: Path):
    text = path.read_text(encoding="utf-8", errors="ignore")
    fm, fm_text, body = parse_frontmatter(text)
    if fm is None:
        return None
    if fm.get("level") != "silver":
        return None

    changes = []
    course_key = infer_course(path)
    if not course_key:
        return None
    meta = COURSE_META[course_key]

    if not fm.get("course"):
        fm["course"] = meta["course"]
        changes.append("course")

    chapter = fm.get("chapter") or infer_chapter(path.stem)
    if chapter and not fm.get("chapter"):
        fm["chapter"] = str(chapter)
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
    if meta.get("textbook"):
        textbooks = merge_textbooks(textbooks, meta["textbook"])
        if textbooks is not refs.get("textbooks"):
            refs["textbooks"] = textbooks
            changes.append("references.textbooks")
    if refs:
        fm["references"] = refs

    if not changes:
        return None

    new_text = (
        "---\n"
        + yaml.safe_dump(fm, allow_unicode=True, sort_keys=False, default_flow_style=False)
        + "---\n"
        + body
    )
    path.write_text(new_text, encoding="utf-8")
    return changes


def main():
    changed = 0
    skipped = 0
    for p in PROJECT_ROOT.rglob("*.md"):
        if any(x in p.parts for x in ("node_modules", ".git", "00-归档", "归档")):
            continue
        res = process_file(p)
        if res is None:
            continue
        if res:
            changed += 1
            print(f"  {p.relative_to(PROJECT_ROOT)}: {', '.join(res)}")
        else:
            skipped += 1
    print(f"\nUpdated {changed} silver docs.")


if __name__ == "__main__":
    main()
