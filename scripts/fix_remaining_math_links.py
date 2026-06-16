#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
修复数学内容中剩余的高置信度失效链接（第二批）。
"""

import re
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]

REPLACEMENTS = [
    # us.metamath 不存在的 df-XXX 页面 -> 主站
    (re.compile(r"https?://us\.metamath\.org/mpeuni/df-[^\s()<>\[\]{}]+\.html"), "https://us.metamath.org/mpeuni/"),

    # GitHub 占位/失效仓库
    (re.compile(r"https?://github\.com/username/FormalMath(?:\.git)?", re.IGNORECASE), "https://github.com/FormalMath"),
    (re.compile(r"https?://github\.com/leanprover/elan/releases/latest/download/elan-init\.sh", re.IGNORECASE), "https://github.com/leanprover/elan/releases"),
    (re.compile(r"https?://github\.com/leanprover-community/lean-hott", re.IGNORECASE), "https://github.com/leanprover-community"),
    (re.compile(r"https?://github\.com/leanprover-community/lean4-copilot", re.IGNORECASE), "https://github.com/leanprover-community"),

    # 旧版课程/机构主页
    (re.compile(r"https?://ee364a\.github\.io/", re.IGNORECASE), "https://ee364a.stanford.edu/"),
    (re.compile(r"https?://www\.math\.princeton\.edu/[^\s()<>\[\]{}]*", re.IGNORECASE), "https://www.math.princeton.edu/"),
    (re.compile(r"https?://www\.uni-goettingen\.de/de/[^\s()<>\[\]{}]*", re.IGNORECASE), "https://www.uni-goettingen.de/"),

    # 权威数据库/搜索页
    (re.compile(r"https?://www\.numdam\.org/numdam-bin/recherche\?au=Grothendieck"), "https://www.numdam.org/?q=au:Grothendieck"),
    (re.compile(r"https?://arxiv\.org/a/tao_t_1(?:\.html)?"), "https://arxiv.org/search/?searchtype=author&query=Tao%2C+T"),

    # MathWorld 几个已确认失效的词条页 -> 主页
    (re.compile(r"https?://mathworld\.wolfram\.com/(?:Many-ValuedLogic|Optimization|ParallelAlgorithm|SymbolicComputation)\.html", re.IGNORECASE), "https://mathworld.wolfram.com/"),

    # Mathlib4 docs 失效子页 -> 文档根
    (re.compile(r"https?://leanprover-community\.github\.io/mathlib4_docs/Mathlib/Algebra/Homology/", re.IGNORECASE), "https://leanprover-community.github.io/mathlib4_docs/"),
    (re.compile(r"https?://leanprover-community\.github\.io/mathlib4_docs/Mathlib/GroupTheory/Subgroup/Basic\.html", re.IGNORECASE), "https://leanprover-community.github.io/mathlib4_docs/"),

    # 其他权威源修正
    (re.compile(r"https?://www\.ihes\.fr/deligne/", re.IGNORECASE), "https://www.ihes.fr/~deligne/"),
    (re.compile(r"https?://www\.wolframalpha\.com(?!/)"), "https://www.wolframalpha.com/"),
    (re.compile(r"https?://www\.ens\.fr/enseignement/cours/logique-et-theorie-des-ensembles"), "https://www.ens.psl.eu/"),
    (re.compile(r"https?://stacks\.math\.columbia\.edu/tag/XXXX"), "https://stacks.math.columbia.edu/"),
    (re.compile(r"https?://raw\.githubusercontent\.com/formalmath/tools/main/[^\s()<>\[\]{}]+"), "https://github.com/FormalMath"),
    (re.compile(r"https?://www\.youtube\.com/playlist\?example"), "https://www.youtube.com/"),
    (re.compile(r"https?://www\.youtube\.com/c/standupmaths"), "https://www.youtube.com/@standupmaths"),
    (re.compile(r"https?://csrc\.nist\.gov/publications/detail/sp/800-56b/rev-2/final"), "https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-56Br2.pdf"),

    # 高校/机构页面改版 -> 对应可用主页
    (re.compile(r"https?://www\.math\.harvard\.edu/undergraduate/course/[^\s()<>\[\]{}]+"), "https://www.math.harvard.edu/"),
    (re.compile(r"https?://math\.ethz\.ch/studium/[^\s()<>\[\]{}]+"), "https://math.ethz.ch/"),
    (re.compile(r"https?://www\.math\.caltech\.edu/courses"), "http://math.caltech.edu/"),
    (re.compile(r"https?://www\.maths\.cam\.ac\.uk/undergrad/course/ia/numbers-and-sets"), "https://www.maths.cam.ac.uk/undergrad/course/"),
    (re.compile(r"https?://www\.mathunion\.org/icm/"), "https://www.mathunion.org/"),
    (re.compile(r"https?://www\.maa\.org/press/maa-reviews/[^\s()<>\[\]{}]+"), "https://www.maa.org/"),
    (re.compile(r"https?://www\.springer\.com/gp/book/[^\s()<>\[\]{}]+"), "https://www.springer.com/"),

    # 其他
    (re.compile(r"https?://www\.leanprover\.cn/math-in-lean/"), "https://leanprover-community.github.io/mathematics_in_lean/"),
    (re.compile(r"https?://agrothendieck\.github\.io/"), "https://en.wikipedia.org/wiki/Alexander_Grothendieck"),

    # 个人主页/课程页失效 -> 机构主页或相关概念页
    (re.compile(r"https?://math\.mit\.edu/~[^/\s]+/?"), "https://math.mit.edu/"),
    (re.compile(r"https?://math\.mit\.edu/research/pure/applied-sem-future\.html"), "https://math.mit.edu/research/"),
    (re.compile(r"https?://math\.berkeley\.edu/~[^/\s]+/?"), "https://math.berkeley.edu/"),
    (re.compile(r"https?://www\.cs\.cmu\.edu/~[^/\s]+/[^\s()<>\[\]{}]+"), "https://www.cs.cmu.edu/"),
    (re.compile(r"https?://ocw\.mit\.edu/courses/[^\s()<>\[\]{}]+"), "https://ocw.mit.edu/"),
    (re.compile(r"https?://theory\.caltech\.edu/~preskill/ph219/"), "https://www.theory.caltech.edu/"),
    (re.compile(r"https?://www\.brunel\.ac\.uk/randommatrix/"), "https://www.brunel.ac.uk/"),
    (re.compile(r"https?://aimpl\.org/randommatrix/"), "https://aimpl.org/"),
    (re.compile(r"https?://blog\.google/technology/ai/quantum-ai/"), "https://blog.google/"),
    (re.compile(r"https?://archive\.org/details/disquisitionesa00gausgoog"), "https://archive.org/search?query=disquisitiones+arithmeticae+gauss"),
    (re.compile(r"https?://mathshistory\.st-andrews\.ac\.uk/HistTopics/Arithmetization_of_analysis/"), "https://en.wikipedia.org/wiki/Arithmetization_of_analysis"),
    (re.compile(r"https?://stacks\.math\.columbia\.edu/tag/013M"), "https://stacks.math.columbia.edu/tag/01DM"),
    (re.compile(r"https?://www\.abelprize\.no/laureates/2004"), "https://abelprize.no/"),
    (re.compile(r"https?://www\.kaggle\.com/datasets/supply-chain"), "https://www.kaggle.com/datasets"),
    (re.compile(r"https?://www\.turingarchive\.org/"), "https://en.wikipedia.org/wiki/Alan_Turing"),
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
    print(f"Fixed remaining math external links in {changed} docs.")


if __name__ == "__main__":
    main()
