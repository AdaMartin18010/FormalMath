#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
清理内容完全相同的 Markdown 文档副本。

策略：
- 计算文件内容 SHA256
- 对每组哈希重复文件，只保留一份
- 优先保留：路径更深/更有分类语义的文件；文件名与 frontmatter title 匹配的文件
- 删除的副本记录到报告

用法：
    python scripts/deduplicate_exact_copies.py
"""

import yaml
import hashlib
from pathlib import Path
from collections import defaultdict

PROJECT_ROOT = Path(__file__).resolve().parents[1]
REPORT_PATH = PROJECT_ROOT / "project" / "00-项目进度报告" / "Phase1-重复文档清理报告.md"


def parse_frontmatter(text: str):
    if text.startswith("---"):
        end = text.find("---", 3)
        if end != -1:
            fm_text = text[3:end].strip()
            try:
                return yaml.safe_load(fm_text) or {}
            except yaml.YAMLError:
                return {}
    return {}


def compute_hash(path: Path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def choose_keeper(paths):
    """从重复路径中选择保留项"""
    def score(p: Path):
        # 路径越深、文件名与 title 越一致，分数越高
        text = p.read_text(encoding="utf-8", errors="ignore")
        fm = parse_frontmatter(text)
        title = fm.get("title", "")
        base = p.stem
        s = len(p.parts) * 10  # 路径深度
        if title and title in base:
            s += 100
        if base in str(title):
            s += 50
        return s
    return max(paths, key=score)


def main():
    files = []
    for p in PROJECT_ROOT.rglob("*.md"):
        if any(x in p.parts for x in ("node_modules", ".git", "00-归档", "归档")):
            continue
        if p.name.startswith("_"):
            continue
        files.append(p)

    # 按 resolve 去重，避免软链接/硬链接重复
    seen = set()
    unique = []
    for f in files:
        rp = f.resolve()
        if rp not in seen:
            seen.add(rp)
            unique.append(f)

    hash_to_paths = defaultdict(list)
    for f in unique:
        h = compute_hash(f)
        hash_to_paths[h].append(f)

    duplicates = {h: paths for h, paths in hash_to_paths.items() if len(paths) > 1}
    removed = []

    for h, paths in duplicates.items():
        keeper = choose_keeper(paths)
        for p in paths:
            if p != keeper:
                p.unlink()
                removed.append((str(p.relative_to(PROJECT_ROOT)), str(keeper.relative_to(PROJECT_ROOT))))

    # 生成报告
    lines = []
    lines.append("---")
    lines.append("title: Phase 1 重复文档清理报告")
    lines.append("level: meta")
    lines.append("msc_primary: 00A99")
    lines.append("---")
    lines.append("")
    lines.append("# Phase 1 重复文档清理报告")
    lines.append("")
    lines.append(f"- 发现重复组：{len(duplicates)}")
    lines.append(f"- 删除副本数：{len(removed)}")
    lines.append("")
    if removed:
        lines.append("| 删除文件 | 保留文件 |")
        lines.append("|---------|---------|")
        for deleted, kept in removed:
            lines.append(f"| `{deleted}` | `{kept}` |")
    else:
        lines.append("未发现重复文档。")
    lines.append("")

    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Removed {len(removed)} duplicate files. Report: {REPORT_PATH}")


if __name__ == "__main__":
    main()
