#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
参考文献缺失审计脚本 (P1-T4)
"""

import os
import re
import json
import random
import glob
from collections import defaultdict

# 设置随机种子以保证可重复性（审计需要可复现）
random.seed(20250417)

BRANCHES = {
    "代数结构": "docs/02-代数结构/**/*.md",
    "分析学": "docs/03-分析学/**/*.md",
    "几何与拓扑": "docs/04-几何与拓扑/**/*.md",
    "代数几何": "docs/13-代数几何/**/*.md",
    "格洛腾迪克数学理念": "数学家理念体系/格洛腾迪克数学理念/**/*.md",
    "庞加莱数学理念": "数学家理念体系/庞加莱数学理念/**/*.md",
    "希尔伯特数学理念": "数学家理念体系/希尔伯特数学理念/**/*.md",
}

SAMPLE_SIZES = {
    "代数结构": 20,
    "分析学": 20,
    "几何与拓扑": 20,
    "代数几何": 15,
    "格洛腾迪克数学理念": 15,
    "庞加莱数学理念": 5,
    "希尔伯特数学理念": 5,
}

# 正则表达式
PATTERNS = {
    "doi": re.compile(r'10\.\d{4,}/\S+'),
    "arxiv": re.compile(r'arXiv\s*[:]?\s*\d{4}\.\d{4,}', re.I),
    "zbmath": re.compile(r'zbMATH\s*\d+|Zbl\s*\d+', re.I),
    "mathscinet": re.compile(r'MR\s*\d{6,}|MathSciNet', re.I),
    # 期刊卷号页码：匹配类似 "Ann. Math. 123 (2020), 45-67." 或 "J. Algebra, Vol. 12, No. 3, pp. 45-67"
    "journal_citation": re.compile(
        r'([A-Z][a-zA-Z\s\.&]+\d{1,4}|'
        r'Vol\.?\s*\d+|'
        r'No\.?\s*\d+|'
        r'pp\.?\s*\d+\s*[-–—]\s*\d+|'
        r'\(\d{4}\)\s*,\s*\d+\s*[-–—]\s*\d+)'
    ),
    # 精确教材引用：章节、页码、定理编号
    "textbook_precise": re.compile(
        r'(Ch\.?\s*\d+|Chapter\s+\d+|'
        r'第[一二三四五六七八九十\d]+章|'
        r'第[一二三四五六七八九十\d]+节|'
        r'Thm\.?\s*\d+([\.\d]+)?|Theorem\s+\d+([\.\d]+)?|'
        r'Prop\.?\s*\d+([\.\d]+)?|Proposition\s+\d+([\.\d]+)?|'
        r'pp\.?\s*\d+\s*[-–—]\s*\d+|'
        r'page\s+\d+|'
        r'第\s*\d+\s*[-–—]?\s*\d*\s*页)',
        re.I
    ),
    # 粗略引用：仅书名或人名（常见教材作者/书名）
    "textbook_rough": re.compile(
        r'(Atiyah|Macdonald|Hartshorne|Rudin|Folland|'
        r'Lang|Dummit\s+and\s+Foote|Artin|Munkres|'
        r'Hatcher|Rotman|Weibel|Gowers|'
        r'《[^》]+》|'
        r'EGA|SGA|Stacks\s+Project|nLab)',
        re.I
    ),
    # 完全无任何引用迹象：检查是否包含 "参考"、"文献"、"Bibliography"、"References"
    "ref_section": re.compile(r'参考|文献|Bibliography|References|bibliography|references|引用|来源'),
}


def check_file(filepath):
    try:
        with open(filepath, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
    except Exception as e:
        return {
            "path": filepath,
            "error": str(e),
            "has_doi": False,
            "has_arxiv": False,
            "has_zbmath": False,
            "has_mathscinet": False,
            "has_journal_citation": False,
            "has_textbook_precise": False,
            "has_textbook_rough": False,
            "has_ref_section": False,
            "word_count": 0,
        }

    word_count = len(content.split())

    has_doi = bool(PATTERNS["doi"].search(content))
    has_arxiv = bool(PATTERNS["arxiv"].search(content))
    has_zbmath = bool(PATTERNS["zbmath"].search(content))
    has_mathscinet = bool(PATTERNS["mathscinet"].search(content))
    has_journal_citation = bool(PATTERNS["journal_citation"].search(content))
    has_textbook_precise = bool(PATTERNS["textbook_precise"].search(content))
    has_textbook_rough = bool(PATTERNS["textbook_rough"].search(content))
    has_ref_section = bool(PATTERNS["ref_section"].search(content))

    return {
        "path": filepath,
        "has_doi": has_doi,
        "has_arxiv": has_arxiv,
        "has_zbmath": has_zbmath,
        "has_mathscinet": has_mathscinet,
        "has_journal_citation": has_journal_citation,
        "has_textbook_precise": has_textbook_precise,
        "has_textbook_rough": has_textbook_rough,
        "has_ref_section": has_ref_section,
        "word_count": word_count,
    }


def main():
    results = []
    branch_files = {}

    for branch, pattern in BRANCHES.items():
        files = glob.glob(pattern, recursive=True)
        # 过滤掉非常小的文件（如索引、README有时只是导航）但保留以真实反映
        files = [f for f in files if f.lower().endswith('.md')]
        branch_files[branch] = files

    sampled = []
    for branch, n in SAMPLE_SIZES.items():
        files = branch_files[branch]
        if len(files) <= n:
            chosen = files
        else:
            chosen = random.sample(files, n)
        for f in chosen:
            sampled.append((branch, f))

    # 对每个样本检查
    for branch, filepath in sampled:
        info = check_file(filepath)
        info["branch"] = branch
        results.append(info)

    # 统计
    total = len(results)
    has_any_precise = sum(
        1 for r in results
        if r["has_doi"] or r["has_arxiv"] or r["has_zbmath"]
        or r["has_mathscinet"] or r["has_journal_citation"]
        or r["has_textbook_precise"]
    )
    has_doi = sum(1 for r in results if r["has_doi"])
    has_textbook_precise = sum(1 for r in results if r["has_textbook_precise"])
    no_refs = sum(
        1 for r in results
        if not r["has_ref_section"] and not r["has_doi"] and not r["has_arxiv"]
        and not r["has_textbook_precise"] and not r["has_textbook_rough"]
        and not r["has_journal_citation"]
    )
    only_rough = sum(
        1 for r in results
        if not r["has_doi"] and not r["has_arxiv"] and not r["has_zbmath"]
        and not r["has_mathscinet"] and not r["has_journal_citation"]
        and not r["has_textbook_precise"] and r["has_textbook_rough"]
    )

    # 按分支统计
    branch_stats = defaultdict(lambda: {
        "total": 0,
        "has_any_precise": 0,
        "has_doi": 0,
        "has_textbook_precise": 0,
        "no_refs": 0,
        "only_rough": 0,
    })

    for r in results:
        b = r["branch"]
        branch_stats[b]["total"] += 1
        if r["has_doi"] or r["has_arxiv"] or r["has_zbmath"] or r["has_mathscinet"] or r["has_journal_citation"] or r["has_textbook_precise"]:
            branch_stats[b]["has_any_precise"] += 1
        if r["has_doi"]:
            branch_stats[b]["has_doi"] += 1
        if r["has_textbook_precise"]:
            branch_stats[b]["has_textbook_precise"] += 1
        if not r["has_ref_section"] and not r["has_doi"] and not r["has_arxiv"] and not r["has_textbook_precise"] and not r["has_textbook_rough"] and not r["has_journal_citation"]:
            branch_stats[b]["no_refs"] += 1
        if not r["has_doi"] and not r["has_arxiv"] and not r["has_zbmath"] and not r["has_mathscinet"] and not r["has_journal_citation"] and not r["has_textbook_precise"] and r["has_textbook_rough"]:
            branch_stats[b]["only_rough"] += 1

    output = {
        "sampled_files": results,
        "overall": {
            "total": total,
            "has_any_precise": has_any_precise,
            "has_any_precise_pct": round(has_any_precise / total * 100, 2) if total else 0,
            "has_doi": has_doi,
            "has_doi_pct": round(has_doi / total * 100, 2) if total else 0,
            "has_textbook_precise": has_textbook_precise,
            "has_textbook_precise_pct": round(has_textbook_precise / total * 100, 2) if total else 0,
            "no_refs": no_refs,
            "no_refs_pct": round(no_refs / total * 100, 2) if total else 0,
            "only_rough": only_rough,
            "only_rough_pct": round(only_rough / total * 100, 2) if total else 0,
        },
        "branch_stats": {k: dict(v) for k, v in branch_stats.items()},
    }

    os.makedirs("output", exist_ok=True)
    with open("output/reference_audit_raw.json", "w", encoding="utf-8") as f:
        json.dump(output, f, ensure_ascii=False, indent=2)

    print(f"Audit complete. Total sampled: {total}")
    print(json.dumps(output["overall"], ensure_ascii=False, indent=2))
    print("\nBranch breakdown:")
    for b, s in output["branch_stats"].items():
        print(f"  {b}: {s}")


if __name__ == "__main__":
    main()
