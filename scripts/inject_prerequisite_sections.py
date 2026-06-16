#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
为核心课程文档注入前置知识小节，将同课程的前面章节以相对链接形式列出。

用法：
    python scripts/inject_prerequisite_sections.py
"""

import re
import yaml
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]

CORE_COURSE_PATTERNS = [
    r"MIT\s*18\.100A",
    r"MIT\s*18\.701",
    r"MIT\s*18\.06",
    r"Harvard\s*232br",
    r"Stanford\s*FOAG",
]

PREREQ_RE = re.compile(r"^#{1,3}\s*(前置|Prerequisite|前置知识)", re.MULTILINE | re.IGNORECASE)
CHAPTER_RE = re.compile(r"第?\s*(\d+)\s*[章\.]?", re.IGNORECASE)


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


def extract_chapter_number(chapter):
    if chapter is None:
        return None
    m = CHAPTER_RE.search(str(chapter))
    if m:
        return int(m.group(1))
    return None


def is_core_course(course: str):
    return any(re.search(pat, course, re.IGNORECASE) for pat in CORE_COURSE_PATTERNS)


def main():
    course_docs = {}
    for p in PROJECT_ROOT.rglob("*.md"):
        if any(x in p.parts for x in ("node_modules", ".git", "00-归档", "归档")):
            continue
        text = p.read_text(encoding="utf-8", errors="ignore")
        fm, body = parse_frontmatter(text)
        if fm is None:
            continue
        course = str(fm.get("course", ""))
        if not course or not is_core_course(course):
            continue
        ch = extract_chapter_number(fm.get("chapter"))
        if ch is None:
            continue
        course_docs.setdefault(course, []).append({
            "path": p,
            "rel": p.relative_to(PROJECT_ROOT).as_posix(),
            "chapter": ch,
            "title": str(fm.get("title", p.stem)),
            "body": body,
            "fm": fm,
            "text": text,
        })

    changed = 0
    for course, docs in course_docs.items():
        docs.sort(key=lambda d: d["chapter"])
        for i, doc in enumerate(docs):
            if PREREQ_RE.search(doc["body"]):
                continue
            # 第一章通常不需要前置知识小节
            if doc["chapter"] <= min(d["chapter"] for d in docs):
                continue
            prev = [d for d in docs if d["chapter"] < doc["chapter"]]
            if not prev:
                continue
            lines = ["", "---", "", "## 前置知识", "", f"学习本章前建议先掌握 **{course}** 的以下内容：", ""]
            for d in prev[-3:]:  # 列出最近 3 章
                lines.append(f"- [{d['title']}]({d['rel']})")
            lines.append("")

            new_body = doc["body"].rstrip() + "\n" + "\n".join(lines)
            new_text = (
                "---\n"
                + yaml.safe_dump(doc["fm"], allow_unicode=True, sort_keys=False, default_flow_style=False)
                + "---\n"
                + new_body
            )
            doc["path"].write_text(new_text, encoding="utf-8")
            changed += 1

    print(f"Injected prerequisite sections into {changed} core course docs.")


if __name__ == "__main__":
    main()
