#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
修复数学内容中常见的高置信度失效/旧版外部链接。
"""

import re
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]

# (模式, 替换, 是否仅匹配整词/边界)
REPLACEMENTS = [
    # arXiv
    (re.compile(r"https?://arxiv\.org/math(?!/archive)", re.IGNORECASE), "https://arxiv.org/archive/math"),
    (re.compile(r"https?://export\.arxiv\.org/api/query(?!\?)", re.IGNORECASE), "https://export.arxiv.org/api/query?search_query=all"),

    # Lean / Mathlib
    (re.compile(r"https?://leanprover\.github\.io/lean4/doc/", re.IGNORECASE), "https://lean-lang.org/lean4/doc/"),
    (re.compile(r"https?://lean-lang\.org/doc/", re.IGNORECASE), "https://lean-lang.org/documentation/"),
    (re.compile(r"https?://leanprover-community\.github\.io/mathlib4/(?!docs)", re.IGNORECASE), "https://leanprover-community.github.io/mathlib4_docs/"),
    (re.compile(r"https?://leanprover-community\.github\.io/flt/", re.IGNORECASE), "https://leanprover-community.github.io/"),

    # GitHub / FormalMath 占位链接 -> 组织主页
    (re.compile(r"https?://github\.com/FormalMath/FormalMath(?:\.git|/issues)?", re.IGNORECASE), "https://github.com/FormalMath"),
    (re.compile(r"https?://github\.com/FormalMath/discussions", re.IGNORECASE), "https://github.com/FormalMath"),
    (re.compile(r"https?://github\.com/FormalMath/issues/new", re.IGNORECASE), "https://github.com/FormalMath"),
    (re.compile(r"https?://github\.com/YOUR_USERNAME/FormalMath(?:\.git)?", re.IGNORECASE), "https://github.com/FormalMath"),
    (re.compile(r"https?://github\.com/YOUR_USERNAME/mathlib4(?:\.git)?", re.IGNORECASE), "https://github.com/leanprover-community/mathlib4"),
    (re.compile(r"https?://github\.com/formalmath/FormalMath(?:\.git)?", re.IGNORECASE), "https://github.com/FormalMath"),
    (re.compile(r"https?://github\.com/formalmath/formalmath", re.IGNORECASE), "https://github.com/FormalMath"),
    (re.compile(r"https?://github\.com/formalmath/issues", re.IGNORECASE), "https://github.com/FormalMath"),
    (re.compile(r"https?://github\.com/xxx/FormalMath(?:\.git)?", re.IGNORECASE), "https://github.com/FormalMath"),
    (re.compile(r"https?://github\.com/your-org/formalmath(?:\.git)?", re.IGNORECASE), "https://github.com/FormalMath"),
    (re.compile(r"https?://formalmath\.github\.io/", re.IGNORECASE), "https://github.com/FormalMath"),

    # MIT 路径
    (re.compile(r"https?://math\.mit\.edu/research/pure/applied\.html", re.IGNORECASE), "https://math.mit.edu/research/"),
    (re.compile(r"https?://ocw\.mit\.edu/\.\.\.", re.IGNORECASE), "https://ocw.mit.edu/"),

    # ENS
    (re.compile(r"https?://www\.ens\.fr/departements/mathematiques", re.IGNORECASE), "https://www.ens.psl.eu/"),
]


def fix_file(path: Path):
    text = path.read_text(encoding="utf-8", errors="ignore")
    new_text = text
    for pattern, repl in REPLACEMENTS:
        new_text = pattern.sub(repl, new_text)
    if new_text == text:
        return False
    path.write_text(new_text, encoding="utf-8")
    return True


def main():
    changed = 0
    for path in PROJECT_ROOT.rglob("*.md"):
        if ".git" in path.parts or "node_modules" in path.parts:
            continue
        if fix_file(path):
            changed += 1
    print(f"Fixed common external links in {changed} docs.")


if __name__ == "__main__":
    main()
