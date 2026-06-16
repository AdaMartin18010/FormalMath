#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
为其余 4 门核心课程（MIT 18.100A、18.701、Harvard 232br、Stanford FOAG）
注入精确外部资源对齐，复用 MIT 18.06 银层模板模式。

用法：
    python scripts/enrich_remaining_core_courses.py
"""

import yaml
import re
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]

COURSE_BASE = {
    "MIT-18.100A-实分析": {
        "ocw_url": "https://ocw.mit.edu/courses/mathematics/18-100a-real-analysis-fall-2020/",
        "assignments_url": "https://ocw.mit.edu/courses/mathematics/18-100a-real-analysis-fall-2020/pages/assignments/",
        "readings_url": "https://ocw.mit.edu/courses/mathematics/18-100a-real-analysis-fall-2020/pages/calendar-and-readings/",
        "lectures_url": "https://ocw.mit.edu/courses/mathematics/18-100a-real-analysis-fall-2020/video_galleries/lecture-videos/",
        "pset_pdf_base": "https://ocw.mit.edu/courses/mathematics/18-100a-real-analysis-fall-2020/assignments/MIT18_100A_f20_pset",
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
        "ocw_url": "https://ocw.mit.edu/courses/mathematics/18-701-algebra-i-fall-2010/",
        "assignments_url": "https://ocw.mit.edu/courses/mathematics/18-701-algebra-i-fall-2010/pages/assignments/",
        "lectures_url": "https://ocw.mit.edu/courses/mathematics/18-701-algebra-i-fall-2010/pages/lecture-notes/",
        "pset_pdf_base": "https://ocw.mit.edu/courses/mathematics/18-701-algebra-i-fall-2010/assignments/MIT18_701F10_pset",
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
        "course_url": "https://www.math.harvard.edu/course/mathematics-232br/",
        "notes_url": "https://people.math.harvard.edu/~landesman/notes.html",
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
        "course_url": "https://math.stanford.edu/~vakil/216blog/",
        "textbook": {
            "title": "The Rising Sea: Foundations of Algebraic Geometry",
            "author": "Ravi Vakil",
            "edition": "draft",
            "publisher": "Stanford University",
            "year": 2024,
            "isbn": "",
        },
    },
}

TOPIC_META = {
    "MIT-18.100A-实分析": {
        "确界原理与Archimedean性质": {"chapter": "1", "psets": [1], "pages": "10-18"},
        "比较判别法": {"chapter": "2", "psets": [2], "pages": "62-68"},
        "比值根值判别法": {"chapter": "2", "psets": [2], "pages": "68-73"},
        "介值定理": {"chapter": "3", "psets": [3], "pages": "110-115"},
        "一致连续性定理": {"chapter": "3", "psets": [3], "pages": "115-122"},
        "中值定理": {"chapter": "4", "psets": [4], "pages": "131-137"},
        "Taylor定理": {"chapter": "4", "psets": [4], "pages": "137-143"},
        "Weierstrass-M判别法": {"chapter": "5", "psets": [5], "pages": "155-160"},
    },
    "MIT-18.701-抽象代数": {
        "拉格朗日定理": {"chapter": "2", "psets": [1], "pages": "47-50"},
        "群第一同构定理": {"chapter": "2", "psets": [2], "pages": "68-72"},
        "轨道稳定子定理": {"chapter": "2", "psets": [2], "pages": "72-75"},
        "Cauchy定理": {"chapter": "2", "psets": [3], "pages": "75-78"},
        "Sylow第一定理": {"chapter": "6", "psets": [4], "pages": "206-210"},
        "环第一同构定理": {"chapter": "10", "psets": [5], "pages": "335-340"},
        "多项式环唯一分解定理": {"chapter": "10", "psets": [6], "pages": "340-345"},
    },
    "Harvard-232br-代数几何": {
        "II.1-层的基本性质": {"hartshorne": "II.1", "pages": "60-65"},
        "II.2-概形的基本性质": {"hartshorne": "II.2", "pages": "65-70"},
        "II.3-态射性质": {"hartshorne": "II.3", "pages": "70-78"},
        "II.4-分离性与本征性": {"hartshorne": "II.4", "pages": "78-86"},
        "II.5-模与层": {"hartshorne": "II.5", "pages": "110-117"},
        "II.5-模与层-续": {"hartshorne": "II.5", "pages": "110-117"},
        "II.6-除子": {"hartshorne": "II.6", "pages": "130-137"},
        "II.7-射影态射": {"hartshorne": "II.7", "pages": "144-152"},
        "II.8-微分形式": {"hartshorne": "II.8", "pages": "172-180"},
        "II.9-形式概形": {"hartshorne": "II.9", "pages": "190-198"},
        "III.2-导出函子与上同调基本性质": {"hartshorne": "III.1-III.2", "pages": "200-210"},
        "III.3-Čech上同调与导出上同调": {"hartshorne": "III.4", "pages": "220-230"},
        "III.4-上同调计算与应用": {"hartshorne": "III.5", "pages": "230-240"},
        "IV.1-IV.4-曲线基本理论": {"hartshorne": "IV.1-IV.4", "pages": "295-340"},
        "IV.5-IV.6-曲线深化": {"hartshorne": "IV.5-IV.6", "pages": "340-368"},
        "V.1-V.3-曲面初步": {"hartshorne": "V.1-V.3", "pages": "360-400"},
    },
    "Stanford-FOAG-基础代数几何": {
        "Ch23-25-smooth-etale-flat态射深入证明": {"vakil": "Ch 23–25"},
        "Ch26-27-对偶理论-Grothendieck与Serre对偶": {"vakil": "Ch 26–27"},
        "Ch28-29-上同调与基变换": {"vakil": "Ch 28–29"},
        "Part-VI-L5-核心习题精选": {"vakil": "Part VI"},
        "PartVI-L5-习题2": {"vakil": "Part VI"},
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


def merge_textbook(textbooks: list, new_tb: dict):
    title = new_tb.get("title", "")
    author = new_tb.get("author", "")
    for tb in textbooks:
        if tb.get("title") == title and tb.get("author") == author:
            for k, v in new_tb.items():
                if v and not tb.get(k):
                    tb[k] = v
            return textbooks
    textbooks.append(new_tb)
    return textbooks


def update_mit_100a(fm: dict, stem: str, base: dict):
    meta = TOPIC_META["MIT-18.100A-实分析"].get(stem)
    if not meta:
        return []
    changes = []

    external_ids = fm.get("external_ids") or {}
    if "ocw_readings_url" not in external_ids:
        external_ids["ocw_readings_url"] = base["readings_url"]
        changes.append("ocw_readings_url")
    if "ocw_lectures_url" not in external_ids:
        external_ids["ocw_lectures_url"] = base["lectures_url"]
        changes.append("ocw_lectures_url")
    pset_urls = [f"{base['pset_pdf_base']}{n}.pdf" for n in meta["psets"]]
    if external_ids.get("ocw_problem_sets") != pset_urls:
        external_ids["ocw_problem_sets"] = pset_urls
        changes.append("ocw_problem_sets")
    fm["external_ids"] = external_ids

    refs = fm.get("references") or {}
    textbooks = refs.get("textbooks") or []
    textbooks = merge_textbook(textbooks, dict(base["textbook"], chapters=f"Ch. {meta['chapter']}", pages=meta.get("pages", "")))
    refs["textbooks"] = textbooks

    assignments = refs.get("assignments") or []
    existing = {a.get("url") for a in assignments}
    for n in meta["psets"]:
        url = f"{base['pset_pdf_base']}{n}.pdf"
        if url not in existing:
            assignments.append({"name": f"Problem Set {n}", "url": url})
            existing.add(url)
    if assignments:
        refs["assignments"] = assignments
        changes.append("assignments")

    fm["references"] = refs
    return changes


def update_mit_701(fm: dict, stem: str, base: dict):
    meta = TOPIC_META["MIT-18.701-抽象代数"].get(stem)
    if not meta:
        return []
    changes = []

    external_ids = fm.get("external_ids") or {}
    if "ocw_lecture_notes_url" not in external_ids:
        external_ids["ocw_lecture_notes_url"] = base["lectures_url"]
        changes.append("ocw_lecture_notes_url")
    pset_urls = [f"{base['pset_pdf_base']}{n}.pdf" for n in meta["psets"]]
    if external_ids.get("ocw_problem_sets") != pset_urls:
        external_ids["ocw_problem_sets"] = pset_urls
        changes.append("ocw_problem_sets")
    fm["external_ids"] = external_ids

    refs = fm.get("references") or {}
    textbooks = refs.get("textbooks") or []
    textbooks = merge_textbook(textbooks, dict(base["textbook"], chapters=f"Chapter {meta['chapter']}", pages=meta.get("pages", "")))
    refs["textbooks"] = textbooks

    assignments = refs.get("assignments") or []
    existing = {a.get("url") for a in assignments}
    for n in meta["psets"]:
        url = f"{base['pset_pdf_base']}{n}.pdf"
        if url not in existing:
            assignments.append({"name": f"Problem Set {n}", "url": url})
            existing.add(url)
    if assignments:
        refs["assignments"] = assignments
        changes.append("assignments")

    fm["references"] = refs
    return changes


def update_harvard_232br(fm: dict, stem: str, base: dict):
    meta = TOPIC_META["Harvard-232br-代数几何"].get(stem)
    if not meta:
        return []
    changes = []

    external_ids = fm.get("external_ids") or {}
    if "harvard_notes_url" not in external_ids:
        external_ids["harvard_notes_url"] = base["notes_url"]
        changes.append("harvard_notes_url")
    fm["external_ids"] = external_ids

    refs = fm.get("references") or {}
    textbooks = refs.get("textbooks") or []
    textbooks = merge_textbook(textbooks, dict(base["textbook"], chapters=meta.get("hartshorne"), pages=meta.get("pages", "")))
    refs["textbooks"] = textbooks
    fm["references"] = refs
    return changes


def update_stanford_foag(fm: dict, stem: str, base: dict):
    meta = TOPIC_META["Stanford-FOAG-基础代数几何"].get(stem)
    if not meta:
        return []
    changes = []

    external_ids = fm.get("external_ids") or {}
    if "foag_pdf_url" not in external_ids:
        external_ids["foag_pdf_url"] = base["course_url"]
        changes.append("foag_pdf_url")
    fm["external_ids"] = external_ids

    refs = fm.get("references") or {}
    textbooks = refs.get("textbooks") or []
    textbooks = merge_textbook(textbooks, dict(base["textbook"], chapters=meta.get("vakil")))
    refs["textbooks"] = textbooks
    fm["references"] = refs
    return changes


def process_course(course_dir: Path, course_key: str):
    base = COURSE_BASE[course_key]
    changed = 0
    for md_file in sorted(course_dir.glob("*.md")):
        if md_file.name.startswith("INDEX"):
            continue
        text = md_file.read_text(encoding="utf-8", errors="ignore")
        fm, body = parse_frontmatter(text)
        if fm is None:
            continue
        stem = md_file.stem
        if course_key == "MIT-18.100A-实分析":
            changes = update_mit_100a(fm, stem, base)
        elif course_key == "MIT-18.701-抽象代数":
            changes = update_mit_701(fm, stem, base)
        elif course_key == "Harvard-232br-代数几何":
            changes = update_harvard_232br(fm, stem, base)
        elif course_key == "Stanford-FOAG-基础代数几何":
            changes = update_stanford_foag(fm, stem, base)
        else:
            changes = []

        if not changes:
            continue

        new_text = (
            "---\n"
            + yaml.safe_dump(fm, allow_unicode=True, sort_keys=False, default_flow_style=False)
            + "---\n"
            + body
        )
        md_file.write_text(new_text, encoding="utf-8")
        changed += 1
        print(f"  {md_file.relative_to(PROJECT_ROOT)}: {', '.join(changes)}")
    return changed


def main():
    total = 0
    course_root = PROJECT_ROOT / "docs" / "00-银层核心课程"
    for course_key in COURSE_BASE:
        course_dir = course_root / course_key
        if not course_dir.exists():
            continue
        print(f"\n=== {course_key} ===")
        total += process_course(course_dir, course_key)
    print(f"\nUpdated {total} files across 4 core courses.")


if __name__ == "__main__":
    main()
