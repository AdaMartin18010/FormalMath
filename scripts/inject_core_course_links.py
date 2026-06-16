#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
为核心课程文档注入课程主页 / OCW / 讲义的外部链接。

用法：
    python scripts/inject_core_course_links.py
"""

import re
import yaml
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]

# 课程关键词（不区分大小写） -> external_ids 键与 URL
COURSE_LINKS = [
    {
        "patterns": [r"MIT\s*18\.100A", r"18\.100A\s*实分析", r"18\.100A\s*Real Analysis"],
        "key": "mit_ocw_url",
        "url": "https://ocw.mit.edu/courses/18-100a-real-analysis-fall-2020/",
    },
    {
        "patterns": [r"MIT\s*18\.701", r"18\.701\s*抽象代数", r"18\.701\s*Algebra"],
        "key": "mit_ocw_url",
        "url": "https://ocw.mit.edu/courses/18-701-algebra-i-fall-2010/",
    },
    {
        "patterns": [r"MIT\s*18\.06", r"18\.06\s*线性代数", r"18\.06\s*Linear Algebra"],
        "key": "mit_ocw_url",
        "url": "https://ocw.mit.edu/courses/18-06-linear-algebra-spring-2010/",
    },
    {
        "patterns": [r"MIT\s*18\.02", r"18\.02\s*多元微积分", r"18\.02\s*Multivariable"],
        "key": "mit_ocw_url",
        "url": "https://ocw.mit.edu/courses/18-02sc-multivariable-calculus-fall-2010/",
    },
    {
        "patterns": [r"Stanford\s*FOAG", r"FOAG\s*基础代数几何", r"Foundations of Algebraic Geometry"],
        "key": "course_notes_url",
        "url": "https://math.stanford.edu/~vakil/216blog/",
    },
    {
        "patterns": [r"Harvard\s*232br", r"Harvard\s*Math\s*232br", r"232br\s*代数几何"],
        "key": "course_homepage_url",
        "url": "https://people.math.harvard.edu/~phorne/232Br.html",
    },
]


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


def main():
    changed = 0
    for p in PROJECT_ROOT.rglob("*.md"):
        if any(x in p.parts for x in ("node_modules", ".git", "00-归档", "归档")):
            continue
        text = p.read_text(encoding="utf-8", errors="ignore")
        fm, body = parse_frontmatter(text)
        if fm is None:
            continue
        course = str(fm.get("course", ""))
        title = str(fm.get("title", ""))
        if not course and not title:
            continue
        search_text = f"{course} {title}"

        external_ids = fm.get("external_ids") or {}
        added = False
        for item in COURSE_LINKS:
            if any(re.search(pat, search_text, re.IGNORECASE) for pat in item["patterns"]):
                if not external_ids.get(item["key"]):
                    external_ids[item["key"]] = item["url"]
                    added = True

        if not added:
            continue

        fm["external_ids"] = external_ids
        new_text = (
            "---\n"
            + yaml.safe_dump(fm, allow_unicode=True, sort_keys=False, default_flow_style=False)
            + "---\n"
            + body
        )
        p.write_text(new_text, encoding="utf-8")
        changed += 1

    print(f"Injected core course links into {changed} docs.")


if __name__ == "__main__":
    main()
