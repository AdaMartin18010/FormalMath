#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
为 concept/ 和 数学家理念体系/ 中的孤岛文档批量建立交叉引用链接。
"""

import argparse
import os
import re
from collections import Counter
from datetime import datetime
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
CONCEPT_DIR = PROJECT_ROOT / "concept"
MATH_DIR = PROJECT_ROOT / "数学家理念体系"
DOCS_DIR = PROJECT_ROOT / "docs"
INDEX_MD = PROJECT_ROOT / "INDEX.md"
REPORT_PATH = DOCS_DIR / "00-交叉引用补全报告.md"

# 关键词 -> docs/ 子目录名
KEYWORD_MAP = {
    # 代数结构
    "环": "02-代数结构",
    "群": "02-代数结构",
    "域": "02-代数结构",
    "模": "02-代数结构",
    "理想": "02-代数结构",
    "Galois": "02-代数结构",
    "伽罗瓦": "02-代数结构",
    "交换代数": "02-代数结构",
    "代数结构": "02-代数结构",
    # 几何与拓扑
    "拓扑": "04-几何与拓扑",
    "几何": "04-几何与拓扑",
    "流形": "04-几何与拓扑",
    "微分几何": "04-几何与拓扑",
    "代数拓扑": "12-代数拓扑",
    # 分析学
    "分析": "03-分析学",
    "微积分": "03-分析学",
    "极限": "03-分析学",
    "连续": "03-分析学",
    "导数": "03-分析学",
    "积分": "03-分析学",
    "级数": "03-分析学",
    "微分": "03-分析学",
    "测度": "03-分析学",
    "泛函": "03-分析学",
    # 数论
    "数论": "05-数论",
    "素数": "05-数论",
    "同余": "05-数论",
    "费马": "05-数论",
    # 概率统计
    "概率": "06-概率论与统计",
    "统计": "06-概率论与统计",
    "随机": "06-概率论与统计",
    "分布": "06-概率论与统计",
    # 数理逻辑
    "逻辑": "07-数理逻辑",
    "公理": "07-数理逻辑",
    "集合论": "07-数理逻辑",
    "证明论": "07-数理逻辑",
    "递归论": "07-数理逻辑",
    "模型论": "07-数理逻辑",
    # 计算数学 / 数值分析
    "计算": "08-计算数学",
    "数值": "07-数值分析",
    "算法": "08-计算数学",
    # 形式化证明
    "形式化": "09-形式化证明",
    "Lean": "09-形式化证明",
    "证明": "09-形式化证明",
    # 语义模型 / 范畴论
    "范畴": "10-语义模型",
    "函子": "10-语义模型",
    "自然变换": "10-语义模型",
    "Topos": "10-语义模型",
    # 代数几何
    "代数几何": "13-代数几何",
    "概形": "13-代数几何",
    # 同调代数
    "同调": "15-同调代数",
    "同伦": "15-同调代数",
    "上同调": "15-同调代数",
    # 基础数学
    "集合": "01-基础数学",
    "函数": "01-基础数学",
    "向量": "01-基础数学",
    "线性": "01-基础数学",
    "矩阵": "01-基础数学",
    "映射": "01-基础数学",
    "自然数": "01-基础数学",
    "整数": "01-基础数学",
    "有理数": "01-基础数学",
    "实数": "01-基础数学",
    "复数": "01-基础数学",
    # 微分方程
    "微分方程": "05-微分方程",
    "偏微分": "05-微分方程",
    "常微分": "05-微分方程",
    # 组合与离散
    "组合": "09-组合数学与离散数学",
    "离散": "09-组合数学与离散数学",
    "图论": "09-组合数学与离散数学",
    # 应用/其他
    "优化": "21-最优化",
    "控制论": "22-控制论",
    "信息论": "23-信息论",
    "密码": "24-密码学",
    "金融数学": "25-金融数学",
    "生物数学": "26-生物数学",
    "数据科学": "29-数据科学",
    "数学物理": "11-数学物理",
    "最优化": "21-最优化",
}


def get_mathematician_names():
    """动态扫描 数学家理念体系/ 下的数学家目录名前缀。"""
    names = set()
    if MATH_DIR.exists():
        for d in MATH_DIR.iterdir():
            if d.is_dir() and d.name.endswith("数学理念"):
                names.add(d.name.replace("数学理念", ""))
    return names


def build_concept_index():
    """建立概念文件名 -> 相对路径的索引，用于数学家文档反向引用。"""
    index = {}
    if not CONCEPT_DIR.exists():
        return index
    for f in CONCEPT_DIR.rglob("*.md"):
        rel = f.relative_to(PROJECT_ROOT)
        stem = f.stem
        index[stem] = rel
        simple = re.sub(r"^\d+-", "", stem)
        if simple and simple != stem:
            index[simple] = rel
    return index


def make_rel_dir(from_file: Path, to_dir: Path) -> str:
    """计算从 from_file 到 to_dir 的相对路径（带末尾斜杠）。"""
    rel = os.path.relpath(to_dir, start=from_file.parent).replace("\\", "/")
    if not rel.endswith("/"):
        rel += "/"
    return rel


def make_rel_link(from_file: Path, to_file: Path) -> str:
    """计算从 from_file 到 to_file 的相对路径。"""
    return os.path.relpath(to_file, start=from_file.parent).replace("\\", "/")


def has_related_links(content: str) -> bool:
    return "## 相关链接" in content or "## 相关链接与延伸阅读" in content


def is_island(content: str) -> bool:
    """不含任何相对内部链接视为孤岛。"""
    return "](../" not in content and "](./" not in content


def match_keywords(text: str):
    """根据关键词返回匹配的 (显示名, 目录名) 列表，最多 3 个。"""
    text_lower = text.lower()
    results = []
    seen = set()
    # 按关键词长度降序，保证多词优先匹配
    for keyword, dir_name in sorted(KEYWORD_MAP.items(), key=lambda x: -len(x[0])):
        if keyword.lower() in text_lower and dir_name not in seen:
            results.append((dir_name, dir_name))
            seen.add(dir_name)
        if len(results) >= 3:
            break
    return results


def process_concept(dry_run: bool, mathematicians: set, concept_index: dict):
    modified = []
    skipped_existing = 0
    skipped_not_island = 0

    for md_file in sorted(CONCEPT_DIR.rglob("*.md"), key=lambda p: str(p)):
        try:
            content = md_file.read_text(encoding="utf-8")
        except Exception as e:
            print(f"  警告: 读取失败 {md_file}: {e}")
            continue

        if has_related_links(content):
            skipped_existing += 1
            continue

        if not is_island(content):
            skipped_not_island += 1
            continue

        stem = md_file.stem
        snippet = stem + " " + content[:500]
        matched_dirs = match_keywords(snippet)

        lines = ["\n", "## 相关链接与延伸阅读", ""]

        if matched_dirs:
            for dname, dpath in matched_dirs:
                target = DOCS_DIR / dpath
                if target.exists():
                    rel = make_rel_dir(md_file, target)
                    lines.append(f"- [{dname}]({rel})")
                else:
                    rel = make_rel_dir(md_file, DOCS_DIR / dpath)
                    lines.append(f"- [{dname}]({rel})")

        # 检查文件名是否含数学家名
        math_hits = []
        for name in sorted(mathematicians, key=len, reverse=True):
            if name in stem:
                target_dir = MATH_DIR / f"{name}数学理念"
                if target_dir.exists():
                    rel = make_rel_dir(md_file, target_dir)
                    math_hits.append(f"- [{name}数学理念]({rel})")
                break  # 通常一个文件名只对应一个数学家

        if math_hits:
            lines.extend(["", "### 数学家相关"] + math_hits)

        # 通用链接
        lines.append(f"\n- [FormalMath 总索引]({make_rel_link(md_file, INDEX_MD)})")
        if not matched_dirs:
            lines.append(f"- [数学文档库]({make_rel_dir(md_file, DOCS_DIR)})")

        new_content = content.rstrip("\n") + "\n" + "\n".join(lines) + "\n"

        if not dry_run:
            md_file.write_text(new_content, encoding="utf-8")
        modified.append(str(md_file.relative_to(PROJECT_ROOT)))

    return modified, skipped_existing, skipped_not_island


def process_math(dry_run: bool, mathematicians: set, concept_index: dict):
    modified = []
    skipped_existing = 0
    skipped_not_island = 0

    for md_file in sorted(MATH_DIR.rglob("*.md"), key=lambda p: str(p)):
        try:
            content = md_file.read_text(encoding="utf-8")
        except Exception as e:
            print(f"  警告: 读取失败 {md_file}: {e}")
            continue

        if has_related_links(content):
            skipped_existing += 1
            continue

        if not is_island(content):
            skipped_not_island += 1
            continue

        parts = md_file.relative_to(MATH_DIR).parts
        mathematician = ""
        if parts:
            first_dir = parts[0]
            if first_dir.endswith("数学理念"):
                mathematician = first_dir.replace("数学理念", "")

        stem = md_file.stem
        snippet = stem + " " + content[:500]
        matched_dirs = match_keywords(snippet)

        lines = ["\n", "## 相关链接", ""]

        if matched_dirs:
            for dname, dpath in matched_dirs:
                target = DOCS_DIR / dpath
                if target.exists():
                    rel = make_rel_dir(md_file, target)
                    lines.append(f"- [{dname}]({rel})")
                else:
                    rel = make_rel_dir(md_file, DOCS_DIR / dpath)
                    lines.append(f"- [{dname}]({rel})")

        # 尝试匹配 concept/ 中的相关文档
        simple_stem = re.sub(r"^\d+-", "", stem)
        concept_matches = []
        for key, rel_path in concept_index.items():
            # 简单匹配：key 是 simple_stem 的子串或 simple_stem 是 key 的子串
            if key == simple_stem or key in simple_stem or simple_stem in key:
                concept_matches.append((key, rel_path))
                if len(concept_matches) >= 3:
                    break

        if concept_matches:
            lines.append("")
            lines.append("### 相关概念")
            for key, rel_path in concept_matches:
                rel = make_rel_link(md_file, PROJECT_ROOT / rel_path)
                lines.append(f"- [{key}]({rel})")

        # 数学家主页面
        if mathematician:
            readme_path = MATH_DIR / f"{mathematician}数学理念" / "README.md"
            if readme_path.exists():
                rel = make_rel_link(md_file, readme_path)
                lines.append(f"\n- [{mathematician}主页面]({rel})")

        lines.append(f"- [FormalMath 总索引]({make_rel_link(md_file, INDEX_MD)})")
        lines.append(f"- [核心概念库]({make_rel_dir(md_file, CONCEPT_DIR)})")

        new_content = content.rstrip("\n") + "\n" + "\n".join(lines) + "\n"

        if not dry_run:
            md_file.write_text(new_content, encoding="utf-8")
        modified.append(str(md_file.relative_to(PROJECT_ROOT)))

    return modified, skipped_existing, skipped_not_island


def generate_report(dry_run: bool, concept_modified, math_modified, c_existing, c_island, m_existing, m_island):
    lines = [
        "# 交叉引用补全报告",
        f"生成时间: {datetime.now().isoformat()}",
        f"执行模式: {'预览 (dry-run)' if dry_run else '实际修改'}",
        "",
        "## 统计摘要",
        f"- **concept/ 修改数**: {len(concept_modified)}",
        f"- **数学家理念体系/ 修改数**: {len(math_modified)}",
        f"- **修改的文件总数**: {len(concept_modified) + len(math_modified)}",
        f"- concept/ 跳过（已有相关链接）: {c_existing}",
        f"- concept/ 跳过（非孤岛）: {c_island}",
        f"- 数学家理念体系/ 跳过（已有相关链接）: {m_existing}",
        f"- 数学家理念体系/ 跳过（非孤岛）: {m_island}",
        "",
        "## concept/ 目录修改分布",
    ]
    c_dirs = Counter([Path(p).parent.as_posix() for p in concept_modified])
    for d, cnt in c_dirs.most_common():
        lines.append(f"- `{d}`: {cnt} 个文件")

    lines.extend(["", "## 数学家理念体系/ 目录修改分布（前 50）"])
    m_dirs = Counter([Path(p).parent.as_posix() for p in math_modified])
    for d, cnt in m_dirs.most_common(50):
        lines.append(f"- `{d}`: {cnt} 个文件")
    if len(m_dirs) > 50:
        lines.append(f"- ... 还有 {len(m_dirs) - 50} 个其他目录")

    lines.extend(["", "## 特殊案例与说明"])
    lines.append("- 所有被修改的文件均原为空链接的“孤岛文档”（不含 `](../` 或 `](./` 相对链接）。")
    lines.append("- 已包含 `## 相关链接` 或 `## 相关链接与延伸阅读` 标题的文档被主动跳过，避免重复追加。")
    lines.append("- 链接基于文件名及正文前 500 字符的关键词匹配自动推断生成。")
    if not dry_run:
        lines.append("- 本次为实际写入操作，文档末尾已追加交叉引用区块。")
    else:
        lines.append("- 本次为预览模式，未执行实际写入。")

    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"报告已生成: {REPORT_PATH}")


def main():
    parser = argparse.ArgumentParser(description="为孤岛文档批量建立交叉引用链接")
    parser.add_argument("--dry-run", action="store_true", help="仅统计，不实际修改文件")
    args = parser.parse_args()

    print("正在扫描目录结构...")
    mathematicians = get_mathematician_names()
    concept_index = build_concept_index()
    print(f"发现数学家目录: {len(mathematicians)} 个")
    print(f"发现概念文档索引: {len(concept_index)} 条")

    print("\n正在处理 concept/ ...")
    c_mod, c_exist, c_island = process_concept(args.dry_run, mathematicians, concept_index)
    print(f"  修改/待修改: {len(c_mod)}, 跳过(已有链接): {c_exist}, 跳过(非孤岛): {c_island}")

    print("\n正在处理 数学家理念体系/ ...")
    m_mod, m_exist, m_island = process_math(args.dry_run, mathematicians, concept_index)
    print(f"  修改/待修改: {len(m_mod)}, 跳过(已有链接): {m_exist}, 跳过(非孤岛): {m_island}")

    generate_report(args.dry_run, c_mod, m_mod, c_exist, c_island, m_exist, m_island)
    print("\n完成。")


if __name__ == "__main__":
    main()
