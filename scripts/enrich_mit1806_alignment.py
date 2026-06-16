#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
深化 MIT 18.06 线性代数的 L3-L6 语义对齐。

为每章注入：
- 具体 OCW Lecture URL
- 对应 Problem Set / Exam 链接
- Strang 教材精确章节
- 前置章节链接

用法：
    python scripts/enrich_mit1806_alignment.py
"""

import yaml
import re
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]
COURSE_DIR = PROJECT_ROOT / "docs" / "00-银层核心课程" / "MIT-18.06-线性代数"
OCW_BASE = "https://ocw.mit.edu/courses/mathematics/18-06-linear-algebra-spring-2010"


def slugify(title: str) -> str:
    s = title.lower()
    s = re.sub(r"[^a-z0-9\s-]", "", s)
    s = re.sub(r"\s+", "-", s).strip("-")
    return s


LECTURE_TITLES = {
    1: "The geometry of linear equations",
    2: "Elimination with matrices",
    3: "Multiplication and inverse matrices",
    4: "Factorization into A = LU",
    5: "Transposes permutations spaces Rn",
    6: "Column space and nullspace",
    7: "Solving Ax = 0 pivot variables special solutions",
    8: "Solving Ax = b row reduced form R",
    9: "Independence basis and dimension",
    10: "The four fundamental subspaces",
    11: "Matrix spaces rank 1 small world graphs",
    12: "Graphs networks incidence matrices",
    13: "Quiz 1 review",
    14: "Orthogonal vectors and subspaces",
    15: "Projections onto subspaces",
    16: "Projection matrices and least squares",
    17: "Orthogonal matrices and Gram-Schmidt",
    18: "Properties of determinants",
    19: "Determinant formulas and cofactors",
    20: "Cramers rule inverse matrix and volume",
    21: "Eigenvalues and eigenvectors",
    22: "Diagonalization and powers of A",
    23: "Differential equations and expAt",
    24: "Markov matrices Fourier series",
    25: "Symmetric matrices and positive definiteness",
    26: "Complex matrices fast Fourier transform",
    27: "Positive definite matrices and minima",
    28: "Similar matrices and Jordan form",
    29: "Singular value decomposition",
    30: "Linear transformations and their matrices",
    31: "Change of basis image compression",
    32: "Quiz 3 review",
    33: "Left and right inverses pseudoinverse",
    34: "Final course review",
}

CHAPTER_LECTURES = {
    1: [1],
    2: [2],
    3: [3],
    4: [4],
    5: [5],
    6: [6],
    7: [7, 8],
    8: [9],
    9: [10],
    10: [14, 15],
    11: [16, 17],
    12: [18, 19, 20],
    13: [21],
    14: [22, 25, 27, 28],
    15: [29, 30, 31, 33],
}

CHAPTER_PROBLEM_SETS = {
    1: [1],
    2: [1, 2],
    3: [2, 3],
    4: [4],
    5: [5, 6],
    6: [6, 7],
    7: [7, 8],
    8: [8],
    9: [8, 9],
    10: [9],
    11: [9, 10],
    12: [10],
    13: [10],
    14: [10],
    15: [10],
}

CHAPTER_STRANG_SECTIONS = {
    1: "1.1-1.2",
    2: "1.3, 2.1-2.3",
    3: "2.4-2.5",
    4: "2.6",
    5: "3.1",
    6: "3.2-3.3",
    7: "3.3-3.4",
    8: "3.5",
    9: "3.6",
    10: "4.1-4.2",
    11: "4.3-4.4",
    12: "5.1-5.3",
    13: "6.1",
    14: "6.2-6.5, 6.7",
    15: "7.1-7.3, 8.1",
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


def lecture_url(n: int) -> str:
    title = LECTURE_TITLES[n]
    return f"{OCW_BASE}/resources/lecture-{n}-{slugify(title)}/"


def problem_set_url(n: int) -> str:
    return f"{OCW_BASE}/assignments/MIT18_06S10_pset{n}.pdf"


def exam_url(exam: str) -> str:
    return f"{OCW_BASE}/exams/MIT18_06S10_{exam}_s10.pdf"


def exam_solution_url(exam: str) -> str:
    return f"{OCW_BASE}/exams/MIT18_06S10_{exam}_s10_sol.pdf"


def update_frontmatter(fm: dict, chapter: int):
    external_ids = fm.get("external_ids") or {}
    external_ids["ocw_lectures"] = [lecture_url(n) for n in CHAPTER_LECTURES.get(chapter, [])]
    external_ids["ocw_problem_sets"] = [problem_set_url(n) for n in CHAPTER_PROBLEM_SETS.get(chapter, [])]
    fm["external_ids"] = external_ids

    refs = fm.get("references") or {}
    # 教材引用：精确到章节
    textbooks = refs.get("textbooks") or []
    # 查找是否已有 Strang 教材，更新 chapters 字段
    updated = False
    for tb in textbooks:
        if tb.get("author", "").startswith("Gilbert Strang") and tb.get("title", "").startswith("Introduction to Linear Algebra"):
            tb["chapters"] = f"Chapter {chapter}, Sections {CHAPTER_STRANG_SECTIONS.get(chapter, '')}"
            tb["isbn"] = "9780980232776"
            updated = True
    if not updated:
        textbooks.append({
            "title": "Introduction to Linear Algebra",
            "author": "Gilbert Strang",
            "edition": "5th",
            "publisher": "Wellesley-Cambridge Press",
            "year": 2016,
            "isbn": "9780980232776",
            "chapters": f"Chapter {chapter}, Sections {CHAPTER_STRANG_SECTIONS.get(chapter, '')}",
        })
    refs["textbooks"] = textbooks

    # OCW 讲座引用
    lectures = refs.get("lectures") or []
    # 去重
    existing_urls = {l.get("url", "") for l in lectures}
    for n in CHAPTER_LECTURES.get(chapter, []):
        url = lecture_url(n)
        if url not in existing_urls:
            lectures.append({
                "institution": "MIT",
                "course_code": "18.06",
                "lecture": f"L{n}",
                "title": LECTURE_TITLES[n],
                "url": url,
            })
            existing_urls.add(url)
    refs["lectures"] = lectures

    # 考试引用（按章节范围）
    exams = []
    if chapter <= 9:
        exams.append({"name": "Exam 1", "url": exam_url("exam1"), "solution_url": exam_solution_url("exam1")})
    if 10 <= chapter <= 19:
        exams.append({"name": "Exam 2", "url": exam_url("exam2"), "solution_url": exam_solution_url("exam2")})
    if chapter >= 20:
        exams.append({"name": "Exam 3", "url": exam_url("exam3"), "solution_url": exam_solution_url("exam3")})
    if exams:
        refs["exams"] = exams

    fm["references"] = refs

    # 前置章节
    if chapter > 1:
        prereqs = [f"docs/00-银层核心课程/MIT-18.06-线性代数/Ch{chapter-1:02d}-*.md"]
        fm["prerequisites"] = prereqs

    return fm


def ensure_references_section(body: str, chapter: int):
    """在正文末尾追加或更新参考节（如果不存在）"""
    if re.search(r"##\s+参考|##\s+Reference|##\s+参考文献", body, re.IGNORECASE):
        return body
    lines = []
    lines.append("\n\n---\n")
    lines.append("## 参考与延伸阅读\n")
    lines.append("### 教材\n")
    lines.append(f"- Gilbert Strang, *Introduction to Linear Algebra*, 5th ed., Wellesley-Cambridge Press, 2016. ISBN: 9780980232776. 本章对应 Sections {CHAPTER_STRANG_SECTIONS.get(chapter, '')}.\n")
    lines.append("### MIT OCW 讲座\n")
    for n in CHAPTER_LECTURES.get(chapter, []):
        lines.append(f"- Lecture {n}: [{LECTURE_TITLES[n]}]({lecture_url(n)})\n")
    lines.append("### 习题与考试\n")
    for n in CHAPTER_PROBLEM_SETS.get(chapter, []):
        lines.append(f"- [Problem Set {n}]({problem_set_url(n)})\n")
    if chapter <= 9:
        lines.append(f"- [Exam 1]({exam_url('exam1')}) ([solutions]({exam_solution_url('exam1')}))\n")
    elif chapter <= 19:
        lines.append(f"- [Exam 2]({exam_url('exam2')}) ([solutions]({exam_solution_url('exam2')}))\n")
    else:
        lines.append(f"- [Exam 3]({exam_url('exam3')}) ([solutions]({exam_solution_url('exam3')}))\n")
    return body + "".join(lines)


def main():
    updated = 0
    for md_file in sorted(COURSE_DIR.glob("Ch*.md")):
        text = md_file.read_text(encoding="utf-8", errors="ignore")
        fm, body = parse_frontmatter(text)
        if fm is None:
            print(f"Skip (parse error): {md_file.name}")
            continue
        m = re.search(r"Ch0?(\d+)", md_file.stem)
        if not m:
            continue
        chapter = int(m.group(1))
        fm = update_frontmatter(fm, chapter)
        body = ensure_references_section(body, chapter)
        new_text = "---\n" + yaml.safe_dump(
            fm, allow_unicode=True, sort_keys=False, default_flow_style=False
        ) + "---\n" + body
        md_file.write_text(new_text, encoding="utf-8")
        updated += 1
        print(f"Updated: {md_file.name}")
    print(f"\nTotal updated: {updated}")


if __name__ == "__main__":
    main()
