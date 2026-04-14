#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
生成项目统计报告
扫描核心目录的 .md 文件，输出结构化 Markdown 报告
"""

import os
import re
from datetime import datetime
from pathlib import Path

PROJECT_ROOT = Path("e:/_src/FormalMath")
TARGET_DIRS = {
    "docs": PROJECT_ROOT / "docs",
    "concept": PROJECT_ROOT / "concept",
    "数学家理念体系": PROJECT_ROOT / "数学家理念体系",
    "project": PROJECT_ROOT / "project",
}

REPORT_PATH = PROJECT_ROOT / "docs" / "00-项目统计总览-v2.md"


def count_chars_and_words(text: str) -> tuple[int, int]:
    """
    返回 (字符数, 字数)
    - 字符数：UTF-8 解码后的总字符长度
    - 字数：中文字符数 + 英文单词数（按空白分隔的字母序列）
    """
    chars = len(text)
    # 中文字符
    chinese = len(re.findall(r"[\u4e00-\u9fff]", text))
    # 英文单词
    english_words = len(re.findall(r"[a-zA-Z]+", text))
    words = chinese + english_words
    return chars, words


def scan_md_files(directory: Path) -> list[Path]:
    """递归扫描目录下所有 .md 文件（排除 .git 等隐藏目录）"""
    if not directory.exists():
        return []
    return [
        p
        for p in directory.rglob("*.md")
        if not any(part.startswith(".") for part in p.relative_to(directory).parts)
    ]


def collect_basic_stats(files: list[Path]) -> dict:
    """计算文档基础统计"""
    total_chars = 0
    total_words = 0
    for f in files:
        try:
            text = f.read_text(encoding="utf-8")
            c, w = count_chars_and_words(text)
            total_chars += c
            total_words += w
        except Exception:
            pass
    return {
        "count": len(files),
        "chars": total_chars,
        "words": total_words,
    }


def docs_subgroup_stats(docs_dir: Path) -> dict[str, int]:
    """按 docs 一级子目录分组统计文档数"""
    stats = {}
    if not docs_dir.exists():
        return stats
    for subdir in sorted(docs_dir.iterdir()):
        if subdir.is_dir() and not subdir.name.startswith("."):
            count = len(scan_md_files(subdir))
            stats[subdir.name] = count
    return stats


def mathematician_subdir_count(math_dir: Path) -> int:
    """统计数学家理念体系下的数学家子目录数量（排除 00-归档 等特殊目录）"""
    if not math_dir.exists():
        return 0
    count = 0
    for subdir in sorted(math_dir.iterdir()):
        if subdir.is_dir() and not subdir.name.startswith("."):
            # 排除纯数字编号或"00-归档"类管理目录
            if subdir.name == "00-归档":
                continue
            count += 1
    return count


def project_course_mapping_count(project_dir: Path) -> int:
    """统计 project 目录下课程映射文件数量"""
    keywords = ["course-mapping", "alignment", "课程对齐"]
    files = scan_md_files(project_dir)
    count = 0
    for f in files:
        lower_name = f.name.lower()
        if any(kw in lower_name for kw in keywords):
            count += 1
    return count


def docs_suffix_stats(docs_dir: Path) -> dict[str, int]:
    """统计 docs 目录下特定后缀的文件数量"""
    suffixes = ["-基础版.md", "-增强版.md", "-深度扩展版.md", "-国际标准版.md"]
    files = scan_md_files(docs_dir)
    stats = {s: 0 for s in suffixes}
    for f in files:
        for s in suffixes:
            if f.name.endswith(s):
                stats[s] += 1
                break
    return stats


def docs_readme_check(docs_dir: Path) -> tuple[list[str], list[str]]:
    """检查 docs 一级子目录是否有 README.md"""
    has_readme = []
    no_readme = []
    if not docs_dir.exists():
        return has_readme, no_readme
    for subdir in sorted(docs_dir.iterdir()):
        if subdir.is_dir() and not subdir.name.startswith("."):
            readme = subdir / "README.md"
            if readme.exists():
                has_readme.append(subdir.name)
            else:
                no_readme.append(subdir.name)
    return has_readme, no_readme


def format_number(n: int) -> str:
    return f"{n:,}"


def generate_report() -> str:
    # 1. 扫描四个核心目录
    all_files = {name: scan_md_files(path) for name, path in TARGET_DIRS.items()}
    basic_stats = {name: collect_basic_stats(files) for name, files in all_files.items()}

    # 3. docs 一级子目录分组
    docs_subgroups = docs_subgroup_stats(TARGET_DIRS["docs"])

    # 4. 数学家子目录数量
    mathematician_count = mathematician_subdir_count(TARGET_DIRS["数学家理念体系"])

    # 5. project 课程映射文件
    course_mapping_count = project_course_mapping_count(TARGET_DIRS["project"])

    # 6. docs 特定后缀统计
    suffix_stats = docs_suffix_stats(TARGET_DIRS["docs"])

    # 7. docs README.md 检查
    has_readme, no_readme = docs_readme_check(TARGET_DIRS["docs"])

    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

    lines = []
    lines.append("# 项目统计总览 v2\n")
    lines.append("> **数据来源**：自动化扫描  ")
    lines.append(f"> **扫描时间**：{timestamp}\n")

    # 一、核心目录总体统计
    lines.append("## 一、核心目录总体统计\n")
    lines.append("| 目录 | 文档数 | 总字符数 | 总字数 |")
    lines.append("|------|--------|----------|--------|")
    for name in ["docs", "concept", "数学家理念体系", "project"]:
        st = basic_stats[name]
        lines.append(
            f"| {name} | {format_number(st['count'])} | {format_number(st['chars'])} | {format_number(st['words'])} |"
        )
    lines.append("")

    # 二、docs 一级子目录文档分布
    lines.append("## 二、docs 一级子目录文档分布\n")
    lines.append("| 子目录 | 文档数 |")
    lines.append("|--------|--------|")
    for subdir, count in sorted(docs_subgroups.items(), key=lambda x: -x[1]):
        lines.append(f"| {subdir} | {format_number(count)} |")
    lines.append(f"| **合计** | **{format_number(sum(docs_subgroups.values()))}** |")
    lines.append("")

    # 三、数学家理念体系子目录统计
    lines.append("## 三、数学家理念体系子目录统计\n")
    lines.append(f"- **数学家子目录数量**：{format_number(mathematician_count)}")
    total_math_docs = basic_stats["数学家理念体系"]["count"]
    lines.append(f"- **总文档数**：{format_number(total_math_docs)}")
    lines.append("")

    # 四、project 课程映射文件统计
    lines.append("## 四、project 课程映射文件统计\n")
    lines.append(f"- **课程映射文件数量**：{format_number(course_mapping_count)}")
    total_project_docs = basic_stats["project"]["count"]
    lines.append(f"- **project 总文档数**：{format_number(total_project_docs)}")
    lines.append("")

    # 五、docs 版本后缀文件统计
    lines.append("## 五、docs 版本后缀文件统计\n")
    lines.append("| 后缀 | 文件数量 |")
    lines.append("|------|----------|")
    suffix_labels = {
        "-基础版.md": "-基础版.md",
        "-增强版.md": "-增强版.md",
        "-深度扩展版.md": "-深度扩展版.md",
        "-国际标准版.md": "-国际标准版.md",
    }
    for suffix, label in suffix_labels.items():
        lines.append(f"| {label} | {format_number(suffix_stats[suffix])} |")
    lines.append(f"| **合计** | **{format_number(sum(suffix_stats.values()))}** |")
    lines.append("")

    # 六、docs 子目录 README.md 检查
    lines.append("## 六、docs 子目录 README.md 检查\n")
    lines.append(f"- **有 README.md 的子目录数**：{format_number(len(has_readme))}")
    lines.append(f"- **无 README.md 的子目录数**：{format_number(len(no_readme))}\n")

    lines.append("### 有 README.md 的子目录\n")
    lines.append("```")
    for name in has_readme:
        lines.append(name)
    lines.append("```\n")

    lines.append("### 无 README.md 的子目录\n")
    lines.append("```")
    for name in no_readme:
        lines.append(name)
    lines.append("```\n")

    lines.append("---\n")
    lines.append("*报告由 `tools/generate_project_stats.py` 自动生成*\n")

    return "\n".join(lines)


def main():
    report = generate_report()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    REPORT_PATH.write_text(report, encoding="utf-8")
    print(f"报告已生成：{REPORT_PATH}")


if __name__ == "__main__":
    main()
