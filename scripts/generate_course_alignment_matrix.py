#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
生成 5 门银层核心课程的 L1-L6 语义对齐矩阵模板。

用法：
    python scripts/generate_course_alignment_matrix.py
"""

import yaml
import re
from pathlib import Path
from collections import defaultdict

PROJECT_ROOT = Path(__file__).resolve().parents[1]
COURSES_DIR = PROJECT_ROOT / "docs" / "00-银层核心课程"
OUTPUT_DIR = PROJECT_ROOT / "project" / "00-项目进度报告" / "Phase1-Sprint2-五门核心课程对齐矩阵"

COURSES = {
    "MIT-18.06-线性代数": {
        "name_en": "MIT 18.06 Linear Algebra",
        "ocw_url": "https://ocw.mit.edu/courses/mathematics/18-06-linear-algebra-spring-2010/",
        "ocw_ps_url": "https://ocw.mit.edu/courses/mathematics/18-06sc-linear-algebra-fall-2011/pages/resource-index/",
        "textbook": "Strang, Introduction to Linear Algebra, 5th ed.",
        "isbn": "9780980232776",
        "msc_primary": "15",
        "prerequisites": ["docs/00-银层核心课程/MIT-18.02-多变量微积分/"],
    },
    "MIT-18.100A-实分析": {
        "name_en": "MIT 18.100A Real Analysis",
        "ocw_url": "https://ocw.mit.edu/courses/mathematics/18-100a-real-analysis-fall-2020/",
        "ocw_ps_url": "https://ocw.mit.edu/courses/mathematics/18-100a-real-analysis-fall-2020/pages/assignments/",
        "textbook": "Rudin, Principles of Mathematical Analysis, 3rd ed.",
        "isbn": "9780070542358",
        "msc_primary": "26",
        "prerequisites": ["docs/00-银层核心课程/MIT-18.02-多变量微积分/"],
    },
    "MIT-18.701-抽象代数": {
        "name_en": "MIT 18.701 Algebra I",
        "ocw_url": "https://ocw.mit.edu/courses/mathematics/18-701-algebra-i-fall-2010/",
        "ocw_ps_url": "https://ocw.mit.edu/courses/mathematics/18-701-algebra-i-fall-2010/pages/assignments/",
        "textbook": "Artin, Algebra, 2nd ed.",
        "isbn": "9780132413770",
        "msc_primary": "12",
        "prerequisites": ["docs/00-银层核心课程/MIT-18.06-线性代数/"],
    },
    "Harvard-232br-代数几何": {
        "name_en": "Harvard Math 232br Introduction to Algebraic Geometry II",
        "ocw_url": "https://www.math.harvard.edu/course/mathematics-232br/",
        "ocw_ps_url": "https://people.math.harvard.edu/~landesman/notes.html",
        "textbook": "Hartshorne, Algebraic Geometry; Vakil, Foundations of Algebraic Geometry",
        "isbn": "9780387902449",
        "msc_primary": "14",
        "prerequisites": ["docs/00-银层核心课程/MIT-18.701-抽象代数/", "docs/00-银层核心课程/Stanford-FOAG-基础代数几何/"],
    },
    "Stanford-FOAG-基础代数几何": {
        "name_en": "Stanford FOAG Foundations of Algebraic Geometry",
        "ocw_url": "https://math.stanford.edu/~vakil/216blog/",
        "ocw_ps_url": "https://math.stanford.edu/~vakil/216blog/",
        "textbook": "Vakil, The Rising Sea: Foundations of Algebraic Geometry",
        "isbn": "",
        "msc_primary": "14",
        "prerequisites": ["docs/00-银层核心课程/MIT-18.701-抽象代数/"],
    },
}

SECTION_PATTERNS = {
    "定义": r"定义|Definition",
    "定理": r"定理|Theorem",
    "证明": r"证明|Proof",
    "例题": r"例题|Example|例子",
    "习题": r"习题|Exercise|问题|Problem Set|作业",
    "解答": r"解答|Solution|答案",
    "参考": r"参考|Reference|Bibliography|文献",
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


def has_section(body: str, pattern: str):
    return bool(re.search(pattern, body, re.IGNORECASE))


def count_words(body: str):
    text = re.sub(r"```[\s\S]*?```", "", body)
    text = re.sub(r"`[^`]+`", "", text)
    text = re.sub(r"[!-/:-@[-`{-~]", "", text)
    return len(text.replace(" ", "").replace("\n", ""))


def status_for_doc(r):
    if r["word_count"] < 300:
        return "空壳/待合并"
    score = 0
    if r["sections"].get("定义"):
        score += 1
    if r["sections"].get("定理"):
        score += 1
    if r["sections"].get("证明"):
        score += 1
    if r["sections"].get("例题"):
        score += 1
    if r["sections"].get("习题"):
        score += 1
    if r["sections"].get("解答"):
        score += 1
    if r["sections"].get("参考"):
        score += 1
    if score >= 6:
        return "完整"
    if score >= 4:
        return "部分"
    return "缺口大"


def generate_course_matrix(course_key: str, meta: dict):
    course_dir = COURSES_DIR / course_key
    if not course_dir.exists():
        return None

    docs = sorted(
        [p for p in course_dir.rglob("*.md") if not p.name.startswith("INDEX") and "INDEX" not in p.name],
        key=lambda p: p.name,
    )

    rows = []
    for p in docs:
        text = p.read_text(encoding="utf-8", errors="ignore")
        fm, body = parse_frontmatter(text)
        if fm is None:
            fm = {}
        rel = p.relative_to(PROJECT_ROOT).as_posix()
        title = fm.get("title", p.stem)
        chapter = fm.get("chapter", "")
        wc = count_words(body)
        sections = {k: has_section(body, v) for k, v in SECTION_PATTERNS.items()}
        row = {
            "rel": rel,
            "title": title,
            "chapter": chapter,
            "word_count": wc,
            "sections": sections,
        }
        row["status"] = status_for_doc(row)
        rows.append(row)

    lines = []
    lines.append("---")
    lines.append(f"title: {course_key} L1-L6 语义对齐矩阵")
    lines.append("level: meta")
    lines.append(f"msc_primary: {meta['msc_primary']}")
    lines.append("review_status: draft")
    lines.append("---")
    lines.append("")
    lines.append(f"# {course_key} L1-L6 语义对齐矩阵")
    lines.append("")
    lines.append(f"- **英文名称**: {meta['name_en']}")
    lines.append(f"- **OCW/课程主页**: [{meta['ocw_url']}]({meta['ocw_url']})")
    lines.append(f"- **习题/考试资源**: [{meta['ocw_ps_url']}]({meta['ocw_ps_url']})")
    lines.append(f"- **主教材**: {meta['textbook']}")
    if meta.get("isbn"):
        lines.append(f"- **ISBN**: {meta['isbn']}")
    if meta.get("prerequisites"):
        lines.append(f"- **前置课程**: {', '.join(meta['prerequisites'])}")
    lines.append("")

    lines.append("## L1-L2：课程-文档映射")
    lines.append("")
    lines.append("| 章节 | 项目文档 | 字数 | 定义 | 定理 | 证明 | 例题 | 习题 | 解答 | 参考 | 状态 |")
    lines.append("|------|---------|------|------|------|------|------|------|------|------|------|")
    for r in rows:
        sec = r["sections"]
        def mark(k):
            return "✅" if sec.get(k) else "❌"
        lines.append(
            f"| {r['chapter'] or '-'} | [{r['title']}]({r['rel']}) | {r['word_count']} | "
            f"{mark('定义')} | {mark('定理')} | {mark('证明')} | {mark('例题')} | "
            f"{mark('习题')} | {mark('解答')} | {mark('参考')} | {r['status']} |"
        )
    lines.append("")

    # 缺口汇总
    gaps = [r for r in rows if r["status"] != "完整"]
    lines.append("## 缺口汇总")
    lines.append("")
    lines.append(f"- 总文档数：{len(rows)}")
    lines.append(f"- 状态为「完整」：{len(rows) - len(gaps)}")
    lines.append(f"- 状态为「部分/缺口大/空壳」：{len(gaps)}")
    lines.append("")
    if gaps:
        lines.append("### 待补全文档")
        lines.append("")
        for r in gaps:
            lines.append(f"- `{r['rel']}` → {r['status']}")
        lines.append("")

    lines.append("## L3-L6：语义对齐待办")
    lines.append("")
    lines.append("请按以下清单逐章补充：")
    lines.append("")
    lines.append("- [ ] L3 定义等价性：与教材/OCW 定义严格等价")
    lines.append("- [ ] L4 定理完整证明链：核心定理含证明或详细证明思路")
    lines.append("- [ ] L5 习题/作业对齐：补充 MIT OCW Problem Sets / Exams 对应题及解答")
    lines.append("- [ ] L6 思想方法提炼：常见证明技巧、错误模式、教学注解")
    lines.append("")
    lines.append("## 外部资源链接模板")
    lines.append("")
    lines.append("为每篇文档 frontmatter 添加：")
    lines.append("```yaml")
    lines.append("external_ids:")
    lines.append(f"  ocw_url: \"{meta['ocw_url']}\"")
    lines.append("  ocw_lecture: \"Lxx\"")
    lines.append("  ocw_ps: \"PSetxx\"")
    lines.append("  stacks_tag: \"\"      # 仅代数几何相关")
    lines.append("  nlab_url: \"\"")
    lines.append("  wikidata_qid: \"\"")
    lines.append("```")
    lines.append("")

    return "\n".join(lines)


def main():
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    for key, meta in COURSES.items():
        content = generate_course_matrix(key, meta)
        if content is None:
            print(f"Skip {key}: directory not found")
            continue
        out_path = OUTPUT_DIR / f"{key}-L1-L6-对齐矩阵.md"
        out_path.write_text(content, encoding="utf-8")
        print(f"Generated: {out_path}")


if __name__ == "__main__":
    main()
