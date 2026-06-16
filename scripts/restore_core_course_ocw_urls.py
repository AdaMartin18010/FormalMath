#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
恢复银层核心课程文档 frontmatter 中被误替换为 OCW 主页的具体课程页 URL。
"""

import yaml
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]
CORE_DIR = PROJECT_ROOT / "docs" / "00-银层核心课程"

COURSE_URLS = {
    "MIT 18.06 线性代数": "https://ocw.mit.edu/courses/18-06-linear-algebra-spring-2010/",
    "MIT 18.100A 实分析": "https://ocw.mit.edu/courses/18-100a-introduction-to-analysis-fall-2012/",
    "MIT 18.701 抽象代数": "https://ocw.mit.edu/courses/18-701-algebra-i-fall-2010/",
}


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


def restore_doc(path: Path):
    text = path.read_text(encoding="utf-8", errors="ignore")
    fm, body = parse_frontmatter(text)
    if fm is None:
        return False
    course = str(fm.get("course", "")).strip()
    course_url = COURSE_URLS.get(course)
    if not course_url:
        return False

    refs = fm.get("references") or {}
    changed = False

    for key in ("lectures", "exams"):
        items = refs.get(key) or []
        for item in items:
            for k in ("url", "solution_url"):
                val = item.get(k)
                if val == "https://ocw.mit.edu/":
                    item[k] = course_url
                    changed = True

    if not changed:
        return False

    fm["references"] = refs
    new_text = (
        "---\n"
        + yaml.safe_dump(fm, allow_unicode=True, sort_keys=False, default_flow_style=False)
        + "---\n"
        + body
    )
    path.write_text(new_text, encoding="utf-8")
    return True


def main():
    changed = 0
    for path in CORE_DIR.rglob("*.md"):
        if restore_doc(path):
            changed += 1
    print(f"Restored specific OCW course URLs in {changed} core course docs.")


if __name__ == "__main__":
    main()
