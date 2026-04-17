#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
扫描并归档数学家理念体系中的空壳/注水文档。
规则：
  A类：文件大小 < 600 字节，或正文（去除frontmatter后）< 250 字符
  B类：frontmatter 后正文 < 800 字符，且数学关键词密度极低
  C类：高度模板化（"历史发展"+"哲学动机"+"革命性意义"+"思维过程" 同时出现且正文 < 1500 字符）
"""

import os
import shutil
import re
from pathlib import Path
from datetime import datetime

BASE_DIR = Path("e:/_src/FormalMath/数学家理念体系")
ARCHIVE_DIR = BASE_DIR / "00-归档-2026年4月-其他数学家"
EXCLUDE_DIRS = {"格洛腾迪克数学理念", "00-归档-2026年4月", "00-归档-2026年4月-其他数学家", "00-归档"}

TEMPLATE_KEYWORDS = ["历史发展", "哲学动机", "革命性意义", "思维过程", "表征方式"]
MATH_KEYWORDS = ["定理", "证明", "定义", "引理", "命题", "推论", "例子", "反例", "公式", "$", "\\("]

def strip_frontmatter(text: str) -> str:
    if text.startswith("---"):
        end = text.find("---", 3)
        if end != -1:
            return text[end+3:].strip()
    return text.strip()

def classify_file(filepath: Path) -> str | None:
    size = filepath.stat().st_size
    if size < 600:
        return "A"
    try:
        text = filepath.read_text(encoding="utf-8")
    except Exception:
        return None
    body = strip_frontmatter(text)
    body_len = len(body)
    if body_len < 250:
        return "A"
    if body_len < 800:
        math_hits = sum(1 for kw in MATH_KEYWORDS if kw in body)
        if math_hits < 3:
            return "B"
    if body_len < 1500:
        tmpl_hits = sum(1 for kw in TEMPLATE_KEYWORDS if kw in body)
        if tmpl_hits >= 3:
            return "C"
    return None

def main():
    ARCHIVE_DIR.mkdir(parents=True, exist_ok=True)
    stats = {"A": 0, "B": 0, "C": 0, "total_scanned": 0}
    per_math = {}
    manifest_lines = [f"# 其他数学家空壳文档归档清单\n\n生成时间: {datetime.now().isoformat()}\n\n"]

    for math_dir in sorted(BASE_DIR.iterdir()):
        if not math_dir.is_dir():
            continue
        if math_dir.name in EXCLUDE_DIRS:
            continue

        local = {"A": 0, "B": 0, "C": 0, "total": 0}
        for md_file in math_dir.rglob("*.md"):
            stats["total_scanned"] += 1
            local["total"] += 1
            cls = classify_file(md_file)
            if cls:
                local[cls] += 1
                stats[cls] += 1
                rel_path = md_file.relative_to(math_dir)
                target_dir = ARCHIVE_DIR / math_dir.name / rel_path.parent
                target_dir.mkdir(parents=True, exist_ok=True)
                shutil.move(str(md_file), str(target_dir / md_file.name))
                manifest_lines.append(f"- [{cls}] `{math_dir.name}/{rel_path}` -> `00-归档-2026年4月-其他数学家/{math_dir.name}/{rel_path}`\n")

        per_math[math_dir.name] = local

    # 写入清单
    manifest_path = ARCHIVE_DIR / "_归档清单.md"
    manifest_path.write_text("".join(manifest_lines), encoding="utf-8")

    # 生成统计报告
    report_lines = [
        "# 其他数学家理念体系空壳文档清理报告\n\n",
        f"扫描时间: {datetime.now().isoformat()}\n\n",
        "## 总体统计\n\n",
        f"- 扫描数学家目录数: {len(per_math)}\n",
        f"- 扫描文档总数: {stats['total_scanned']}\n",
        f"- A类归档（纯空/极小）: {stats['A']}\n",
        f"- B类归档（正文过短且缺乏数学内容）: {stats['B']}\n",
        f"- C类归档（高度模板化）: {stats['C']}\n",
        f"- 归档总数: {stats['A'] + stats['B'] + stats['C']}\n",
        f"- 保留文档数: {stats['total_scanned'] - (stats['A'] + stats['B'] + stats['C'])}\n\n",
        "## 按数学家统计（Top 20 归档数量）\n\n",
        "| 数学家 | 总数 | A类 | B类 | C类 | 归档数 | 保留数 |\n",
        "|--------|------|-----|-----|-----|--------|--------|\n",
    ]

    sorted_math = sorted(per_math.items(), key=lambda x: x[1]["A"]+x[1]["B"]+x[1]["C"], reverse=True)
    for name, data in sorted_math[:20]:
        archived = data["A"] + data["B"] + data["C"]
        kept = data["total"] - archived
        report_lines.append(f"| {name} | {data['total']} | {data['A']} | {data['B']} | {data['C']} | {archived} | {kept} |\n")

    report_lines.append("\n## 归档规则\n\n")
    report_lines.append("- A类: 文件 < 600 字节，或去 frontmatter 后正文 < 250 字符\n")
    report_lines.append("- B类: 去 frontmatter 后正文 < 800 字符，且数学关键词出现 < 3 次\n")
    report_lines.append("- C类: 去 frontmatter 后正文 < 1500 字符，且同时出现 3 个及以上模板关键词（历史发展/哲学动机/革命性意义/思维过程/表征方式）\n\n")
    report_lines.append(f"归档目录: `{ARCHIVE_DIR}`\n")

    report_path = Path("e:/_src/FormalMath/output/00-其他数学家空壳清理报告.md")
    report_path.write_text("".join(report_lines), encoding="utf-8")
    print(f"Done. Scanned {stats['total_scanned']} files.")
    print(f"Archived: A={stats['A']}, B={stats['B']}, C={stats['C']}, Total archived={stats['A']+stats['B']+stats['C']}")

if __name__ == "__main__":
    main()
