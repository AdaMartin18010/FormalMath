#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
合并参考文献到已有 frontmatter 的文件中。
使用 PyYAML 解析和写入，保留现有格式尽量不变。
"""

import yaml
from pathlib import Path

# 定义要补充的数据库模板
DB_NLAB = {
    "id": "nlab",
    "type": "database",
    "name": "nLab",
    "entry_url": "https://ncatlab.org/nlab/show/{entry}",
    "consulted_at": "2026-04-17",
}
DB_STACKS = {
    "id": "stacks_project",
    "type": "database",
    "name": "Stacks Project",
    "entry_url": "https://stacks.math.columbia.edu/tag/{tag}",
    "consulted_at": "2026-04-17",
}
DB_ZBMATH = {
    "id": "zbmath",
    "type": "database",
    "name": "zbMATH Open",
    "entry_url": "https://zbmath.org/?q=an:{zb_id}",
    "consulted_at": "2026-04-17",
}

def load_frontmatter(text):
    if not text.startswith("---"):
        return None, text
    end = text.find("\n---", 3)
    if end == -1:
        return None, text
    fm_text = text[3:end]
    rest = text[end + 4:]
    data = yaml.safe_load(fm_text)
    return data, rest

def dump_frontmatter(data):
    # 使用 default_flow_style=False, allow_unicode=True, sort_keys=False
    return yaml.dump(data, allow_unicode=True, sort_keys=False, default_flow_style=False)

def merge_databases(existing_dbs, required_ids):
    existing_ids = {db.get("id") for db in existing_dbs if isinstance(db, dict)}
    templates = {
        "nlab": DB_NLAB,
        "stacks_project": DB_STACKS,
        "zbmath": DB_ZBMATH,
    }
    result = list(existing_dbs)
    for rid in required_ids:
        if rid not in existing_ids:
            result.append(templates[rid])
    return result

def process_real_analysis_file(path):
    text = path.read_text(encoding="utf-8")
    data, rest = load_frontmatter(text)
    if data is None:
        print(f"[跳过] 无 frontmatter: {path}")
        return
    refs = data.setdefault("references", {})
    dbs = refs.setdefault("databases", [])
    refs["databases"] = merge_databases(dbs, ["stacks_project", "zbmath"])
    new_fm = "---\n" + dump_frontmatter(data) + "---" + rest
    path.write_text(new_fm, encoding="utf-8")
    print(f"[已合并] {path}")

def process_mit1806_file(path):
    text = path.read_text(encoding="utf-8")
    data, rest = load_frontmatter(text)
    if data is None:
        print(f"[跳过] 无 frontmatter: {path}")
        return
    refs = data.setdefault("references", {})
    textbooks = refs.setdefault("textbooks", [])
    # 为现有 Strang 条目补充标准字段（若缺失）
    for tb in textbooks:
        if isinstance(tb, dict) and "Introduction to Linear Algebra" in tb.get("title", ""):
            tb["id"] = "strang_la"
            tb["type"] = "textbook"
            # 将 author 转为 authors 列表
            if "author" in tb and "authors" not in tb:
                tb["authors"] = [tb.pop("author")]
            tb.setdefault("publisher", "Wellesley-Cambridge Press")
            tb.setdefault("year", 2016)
            tb.setdefault("isbn", "978-0980232776")
            tb.setdefault("msc", "15-01")
            tb.setdefault("url", None)
    dbs = refs.setdefault("databases", [])
    refs["databases"] = merge_databases(dbs, ["nlab", "stacks_project", "zbmath"])
    new_fm = "---\n" + dump_frontmatter(data) + "---" + rest
    path.write_text(new_fm, encoding="utf-8")
    print(f"[已合并] {path}")

if __name__ == "__main__":
    # 1) 实分析 7 篇试点文档
    ra_files = [
        "docs/03-分析学/01-实分析/01-实分析.md",
        "docs/03-分析学/01-实分析/01-实分析-增强版.md",
        "docs/03-分析学/01-实分析/01-实分析-深度扩展版.md",
        "docs/03-分析学/01-实分析/01-实分析-习题补充.md",
        "docs/03-分析学/01-实分析/02-Lebesgue积分-深度扩展版.md",
        "docs/03-分析学/01-实分析/一致收敛与函数项级数-深度版.md",
        "docs/03-分析学/01-实分析/实数完备性等价定理-深度版.md",
    ]
    for p in ra_files:
        process_real_analysis_file(Path(p))

    # 2) MIT-18.06 线性代数 6 篇文档
    la_files = [
        "docs/02-代数结构/线性代数与矩阵理论/MIT-18.06/01-线性方程组的几何与消元法.md",
        "docs/02-代数结构/线性代数与矩阵理论/MIT-18.06/02-向量空间与四大基本子空间.md",
        "docs/02-代数结构/线性代数与矩阵理论/MIT-18.06/03-正交性投影与最小二乘.md",
        "docs/02-代数结构/线性代数与矩阵理论/MIT-18.06/04-特征值特征向量与对角化.md",
        "docs/02-代数结构/线性代数与矩阵理论/MIT-18.06/05-奇异值分解.md",
        "docs/02-代数结构/线性代数与矩阵理论/MIT-18.06/06-行列式与克拉默法则.md",
    ]
    for p in la_files:
        process_mit1806_file(Path(p))
