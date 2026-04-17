#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
数学家理念体系深度清理脚本 v2。
针对高度模板化的 AI 生成文档进行更激进的归档。
"""

import os
import shutil
import re
from pathlib import Path
from datetime import datetime

BASE_DIR = Path("e:/_src/FormalMath/数学家理念体系")
ARCHIVE_DIR = BASE_DIR / "00-归档-2026年4月-其他数学家"
EXCLUDE_DIRS = {"格洛腾迪克数学理念", "00-归档-2026年4月", "00-归档-2026年4月-其他数学家", "00-归档"}

# 模板化关键词（出现越多越可疑）
TEMPLATE_KEYWORDS = [
    "历史发展", "哲学动机", "革命性意义", "思维过程", "表征方式",
    "思维导图", "概念矩阵", "决策树", "证明树",
    "彻底改变了数学的面貌", "影响了整个", "奠定了基础", "具有重要意义",
    "为理解...奠定了基础", "在...等领域有重要应用"
]

# 数学实质指标
MATH_INDICATORS = [
    "定理", "证明", "定义", "引理", "命题", "推论",
    "设", "若", "则", "证毕", "Q.E.D.", "∎",
    "$", "\\(", "\\[", "\begin{equation}", "\begin{align}",
    "存在", "唯一", "满足", "使得", "映射", "同构", "同态"
]

def strip_frontmatter(text: str) -> str:
    if text.startswith("---"):
        end = text.find("---", 3)
        if end != -1:
            return text[end+3:].strip()
    return text.strip()

def is_shell(filepath: Path) -> tuple[bool, str]:
    """返回 (是否空壳, 类别)"""
    size = filepath.stat().st_size
    if size < 600:
        return True, "A"
    try:
        text = filepath.read_text(encoding="utf-8")
    except Exception:
        return False, ""
    body = strip_frontmatter(text)
    body_len = len(body)

    # 极小正文
    if body_len < 400:
        return True, "A"

    # 计算指标
    tmpl_hits = sum(1 for kw in TEMPLATE_KEYWORDS if kw in body)
    math_hits = sum(1 for ind in MATH_INDICATORS if ind in body)
    math_density = math_hits / (body_len / 1000 + 1)  # 每千字命中数

    # 强模板化判定
    if tmpl_hits >= 4 and math_density < 8 and body_len < 2500:
        return True, "C-strong"

    # 思维表征专类文档（目录结构但正文极少）
    if ("思维导图" in body or "概念矩阵" in body or "决策树" in body) and math_density < 5:
        return True, "C-vis"

    # 中短篇且数学内容极度稀薄
    if body_len < 1500 and math_density < 4:
        return True, "B"

    # 超长目录+重复结构（目录行占比过高）
    toc_lines = sum(1 for line in body.splitlines() if line.strip().startswith("- [") or line.strip().startswith("  - ["))
    total_lines = len([l for l in body.splitlines() if l.strip()])
    if total_lines > 10 and toc_lines / total_lines > 0.4 and math_density < 6:
        return True, "C-toc"

    return False, ""

def main():
    ARCHIVE_DIR.mkdir(parents=True, exist_ok=True)
    stats = {"A": 0, "B": 0, "C-strong": 0, "C-vis": 0, "C-toc": 0, "total_scanned": 0}
    per_math = {}
    manifest_lines = [f"# 其他数学家空壳文档归档清单 v2\n\n生成时间: {datetime.now().isoformat()}\n\n"]

    math_dirs = [d for d in sorted(BASE_DIR.iterdir()) if d.is_dir() and d.name not in EXCLUDE_DIRS]

    for math_dir in math_dirs:
        local = {"A": 0, "B": 0, "C-strong": 0, "C-vis": 0, "C-toc": 0, "total": 0}
        for md_file in math_dir.rglob("*.md"):
            stats["total_scanned"] += 1
            local["total"] += 1
            is_shell_doc, cls = is_shell(md_file)
            if is_shell_doc:
                local[cls] += 1
                stats[cls] += 1
                rel_path = md_file.relative_to(math_dir)
                target_dir = ARCHIVE_DIR / math_dir.name / rel_path.parent
                target_dir.mkdir(parents=True, exist_ok=True)
                shutil.move(str(md_file), str(target_dir / md_file.name))
                manifest_lines.append(f"- [{cls}] `{math_dir.name}/{rel_path}`\n")

        per_math[math_dir.name] = local

    # 清单
    manifest_path = ARCHIVE_DIR / "_归档清单_v2.md"
    manifest_path.write_text("".join(manifest_lines), encoding="utf-8")

    total_archived = sum(stats[k] for k in stats if k != "total_scanned")

    # 报告
    report_lines = [
        "# 其他数学家理念体系空壳文档清理报告 v2\n\n",
        f"扫描时间: {datetime.now().isoformat()}\n\n",
        "## 总体统计\n\n",
        f"- 扫描数学家目录数: {len(math_dirs)}\n",
        f"- 扫描文档总数: {stats['total_scanned']}\n",
        f"- A类（纯空/极小）: {stats['A']}\n",
        f"- B类（数学稀薄）: {stats['B']}\n",
        f"- C-strong（强模板化）: {stats['C-strong']}\n",
        f"- C-vis（纯可视化框架）: {stats['C-vis']}\n",
        f"- C-toc（目录占比过高）: {stats['C-toc']}\n",
        f"- 归档总数: {total_archived}\n",
        f"- 保留文档数: {stats['total_scanned'] - total_archived}\n",
        f"- 归档比例: {total_archived / stats['total_scanned'] * 100:.1f}%\n\n",
        "## 按数学家统计（Top 20 归档数量）\n\n",
        "| 数学家 | 总数 | 归档数 | 保留数 | 归档率 |\n",
        "|--------|------|--------|--------|--------|\n",
    ]

    sorted_math = sorted(per_math.items(), key=lambda x: sum(v for k,v in x[1].items() if k!="total"), reverse=True)
    for name, data in sorted_math[:20]:
        archived = sum(v for k,v in data.items() if k!="total")
        kept = data["total"] - archived
        rate = archived / data["total"] * 100 if data["total"] else 0
        report_lines.append(f"| {name} | {data['total']} | {archived} | {kept} | {rate:.1f}% |\n")

    report_lines.append("\n## 归档规则说明\n\n")
    report_lines.append("- A类: 文件 < 600 字节，或去 frontmatter 后正文 < 400 字符\n")
    report_lines.append("- B类: 正文 < 1500 字符，且数学密度 < 4 次/千字\n")
    report_lines.append("- C-strong: 同时出现 ≥4 个模板关键词，数学密度 < 8，正文 < 2500 字符\n")
    report_lines.append("- C-vis: 包含'思维导图/概念矩阵/决策树'且数学密度 < 5\n")
    report_lines.append("- C-toc: 目录行占比 > 40%，数学密度 < 6\n\n")
    report_lines.append(f"归档目录: `{ARCHIVE_DIR}`\n")

    report_path = Path("e:/_src/FormalMath/output/00-其他数学家空壳清理报告-v2.md")
    report_path.write_text("".join(report_lines), encoding="utf-8")
    print(f"Done. Scanned {stats['total_scanned']} files.")
    print(f"Archived total: {total_archived} ({total_archived/stats['total_scanned']*100:.1f}%)")
    print(f"Breakdown: A={stats['A']}, B={stats['B']}, C-strong={stats['C-strong']}, C-vis={stats['C-vis']}, C-toc={stats['C-toc']}")

if __name__ == "__main__":
    main()
