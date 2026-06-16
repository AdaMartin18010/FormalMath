#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
基于人工精选的 Stacks Tag → 现有文档路径映射，批量更新对齐映射表并注入精确 Stacks Tag。

用法：
    python scripts/expand_stacks_tag_alignment.py
"""

import yaml
import re
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]
MAPPING_FILE = PROJECT_ROOT / "ref" / "Stacks-Project-Tag-对齐映射表.md"

# 人工精选映射：Stacks Tag -> 实际存在的 FormalMath 文档路径
TAG_TO_PATH = {
    # 层上同调 / Cech 上同调
    "01DZ": "docs/13-代数几何/Stacks-Project-金层对齐/02-层的上同调与Cech上同调.md",
    "01ED": "docs/13-代数几何/05-Čech上同调.md",
    "01EO": "docs/12-代数拓扑/06-Mayer-Vietoris序列.md",
    "01ER": "docs/13-代数几何/05-Čech上同调.md",
    "03FD": "docs/13-代数几何/06-层上同调基本定理.md",

    # 导出范畴 / 同调代数
    "01F5": "docs/15-同调代数/16-导出范畴概念.md",
    "05QI": "docs/15-同调代数/16-导出范畴概念.md",
    "013N": "docs/02-代数结构/02-核心理论/同调代数深化-扩展/05-三角范畴与导出范畴.md",
    "013P": "docs/02-代数结构/02-核心理论/同调代数深化-扩展/01-同调代数基础.md",
    "05R0": "docs/15-同调代数/16-导出范畴概念.md",
    "05R1": "docs/15-同调代数/16-导出范畴概念.md",
    "05R2": "docs/15-同调代数/16-导出范畴概念.md",
    "05T7": "docs/15-同调代数/16-导出范畴概念.md",
    "05T8": "docs/15-同调代数/16-导出范畴概念.md",
    "073P": "docs/02-代数结构/02-核心理论/同调代数深化-扩展/01-同调代数基础.md",
    "013D": "docs/02-代数结构/02-核心理论/同调代数深化-扩展/01-同调代数基础.md",
    "013E": "docs/02-代数结构/02-核心理论/同调代数深化-扩展/01-同调代数基础.md",
    "013F": "docs/02-代数结构/02-核心理论/同调代数深化-扩展/01-同调代数基础.md",

    # 谱序列
    "01FP": "docs/15-同调代数/04-谱序列/01-谱序列基础.md",
    "013M": "docs/15-同调代数/13-Leray谱序列.md",
    "013O": "docs/15-同调代数/14-Grothendieck谱序列.md",

    # 概形上同调
    "01XI": "docs/15-同调代数/08-凝聚层与上同调/01-凝聚层与上同调.md",
    "01X8": "docs/13-代数几何/06-层上同调基本定理.md",
    "02O3": "docs/13-代数几何/04-除子与线丛/03-Riemann-Roch定理-深度版.md",

    # Étale 上同调
    "03Q5": "docs/02-代数结构/02-核心理论/代数几何/etale上同调-深度版.md",
    "03QZ": "docs/02-代数结构/02-核心理论/代数几何/etale上同调-深度版.md",
    "09ZQ": "docs/13-代数几何/Stacks-Project-金层对齐/02-层的上同调与Cech上同调.md",

    # 交换代数
    "00DV": "docs/00-核心概念理解三问/11-核心定理多表征/79-Nakayama引理-五种表征.md",
    "00E0": "docs/00-习题示例反例库/代数/ALG-113-素谱与Zariski拓扑.md",
    "00E1": "docs/visualizations/思维导图/概念/素理想.md",
    "00E2": "docs/visualizations/思维导图/概念/极大理想.md",
    "00GH": "docs/02-代数结构/交换代数/03-整闭包与Dedekind整环.md",
    "00GV": "docs/00-习题示例反例库/代数/ALG-107-Noether正规化定理.md",
    "00KD": "docs/02-代数结构/交换代数/05-维数理论.md",
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


def update_mapping_table():
    content = MAPPING_FILE.read_text(encoding="utf-8", errors="ignore")
    lines = content.splitlines()
    updated = []
    table_changed = []
    for line in lines:
        stripped = line.strip()
        if not stripped.startswith("|") or "Stacks Tag" in stripped or "---" in stripped:
            updated.append(line)
            continue
        cells = [c.strip() for c in stripped.strip("|").split("|")]
        if len(cells) < 5:
            updated.append(line)
            continue
        tag = cells[0]
        if tag not in TAG_TO_PATH:
            updated.append(line)
            continue
        new_path = TAG_TO_PATH[tag]
        cells[3] = f"`{new_path}`"
        if cells[4] in ("⏳", "⏳待对齐", "🔄 对齐中"):
            cells[4] = "✅ 已对齐"
        updated.append("| " + " | ".join(cells) + " |")
        table_changed.append((tag, new_path))
    MAPPING_FILE.write_text("\n".join(updated), encoding="utf-8")
    return table_changed


def inject_tag(doc_path: Path, tag: str):
    if not doc_path.exists():
        return False
    text = doc_path.read_text(encoding="utf-8", errors="ignore")
    fm, body = parse_frontmatter(text)
    if fm is None:
        return False

    external_ids = fm.get("external_ids") or {}
    existing = external_ids.get("stacks_tag")
    if isinstance(existing, dict) and existing.get("tag") == tag:
        return False
    if existing == tag:
        return False

    external_ids["stacks_tag"] = {"tag": tag, "url": f"https://stacks.math.columbia.edu/tag/{tag}"}
    fm["external_ids"] = external_ids

    refs = fm.get("references") or {}
    databases = refs.get("databases") or []
    if not any(db.get("id") == "stacks_project" for db in databases):
        databases.append({
            "id": "stacks_project",
            "type": "database",
            "name": "Stacks Project",
            "entry_url": "https://stacks.math.columbia.edu/tag/{tag}",
            "consulted_at": "2026-04-17",
        })
        refs["databases"] = databases
        fm["references"] = refs

    new_text = (
        "---\n"
        + yaml.safe_dump(fm, allow_unicode=True, sort_keys=False, default_flow_style=False)
        + "---\n"
        + body
    )
    doc_path.write_text(new_text, encoding="utf-8")
    return True


def main():
    table_changed = update_mapping_table()
    print(f"Updated {len(table_changed)} rows in {MAPPING_FILE.name}")

    injected = 0
    for tag, rel_path in TAG_TO_PATH.items():
        doc_path = PROJECT_ROOT / rel_path
        if inject_tag(doc_path, tag):
            injected += 1
            print(f"  {rel_path} <- {tag}")
    print(f"\nInjected stacks_tag into {injected} docs.")


if __name__ == "__main__":
    main()
