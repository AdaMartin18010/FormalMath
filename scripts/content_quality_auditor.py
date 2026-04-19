#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalMath 内容质量审核脚本
扫描全项目 .md 文件，计算实质内容得分，生成分级报告
"""

import os
import re
import glob
from datetime import datetime
from collections import defaultdict

# ========== 配置 ==========
PROJECT_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
EXCLUDE_DIRS = {".git", ".lake", "node_modules", "00-归档", "__pycache__", ".venv", "venv", "dist", "build"}
OUTPUT_FILE = os.path.join(PROJECT_ROOT, "output", f"content_quality_audit_{datetime.now().strftime('%Y-%m-%d')}.md")

# 关键词权重
KEYWORDS = {
    "定理": 2, "Theorem": 2, "证明": 2, "Proof": 2,
    "定义": 2, "Definition": 2, "例子": 1, "Example": 1,
    "引理": 2, "Lemma": 2, "推论": 2, "Corollary": 2,
    "命题": 2, "Proposition": 2, "注记": 1, "Remark": 1,
    "性质": 1, "Property": 1, "公理": 2, "Axiom": 2,
    "构造": 1, "Construction": 1, "算法": 2, "Algorithm": 2,
}

# 分支映射
BRANCH_MAP = {
    "FormalMath-Enhanced": "Enhanced",
    "FormalMath-Interactive": "Interactive",
    "concept": "Concept",
    "docs": "Docs",
    "research": "Research",
    "project": "Project",
    "tools": "Tools",
    "数学家理念体系": "Mathematicians",
    "deploy": "Deploy",
    "k8s": "K8s",
    "tests": "Tests",
    "ref": "Ref",
}


def get_branch(filepath):
    """根据文件路径确定所属分支"""
    rel = os.path.relpath(filepath, PROJECT_ROOT)
    parts = rel.split(os.sep)
    if not parts:
        return "Root"
    first = parts[0]
    return BRANCH_MAP.get(first, first)


def should_exclude(path):
    """判断路径是否应该被排除"""
    parts = path.split(os.sep)
    for part in parts:
        if part in EXCLUDE_DIRS:
            return True
    return False


def remove_frontmatter(content):
    """移除 YAML frontmatter"""
    if content.startswith("---"):
        end = content.find("---", 3)
        if end != -1:
            return content[end + 3:]
    return content


def calculate_score(filepath, content):
    """
    计算文件实质内容得分（0-100）
    """
    score = 0
    details = []

    # 1. 去掉 frontmatter
    body = remove_frontmatter(content)

    # 2. 去掉 markdown 标题行
    body_no_headers = re.sub(r'^#+\s.*$', '', body, flags=re.MULTILINE)

    # 3. 去掉空行和空白字符，计算实际字数（中文字符 + 英文单词）
    text = body_no_headers.strip()
    chinese_chars = len(re.findall(r'[\u4e00-\u9fff]', text))
    english_words = len(re.findall(r'[a-zA-Z]+', text))
    total_words = chinese_chars + english_words

    # 字数得分：最多 50 分
    word_score = min(50, total_words / 20)  # 每20字1分，最高50
    score += word_score
    details.append(f"字数得分: {word_score:.1f} (字/词: {total_words})")

    # 4. 数学公式密度得分：最多 20 分
    inline_math = len(re.findall(r'(?<!\$)\$(?!\$)[^$]+\$(?!\$)', text))
    display_math = len(re.findall(r'\$\$[\s\S]*?\$\$', text))
    math_score = min(20, (inline_math + display_math * 3) * 1.5)
    score += math_score
    details.append(f"公式得分: {math_score:.1f} (行内: {inline_math}, 行间: {display_math})")

    # 5. 关键词得分：最多 15 分
    keyword_score = 0
    keyword_counts = {}
    for kw, weight in KEYWORDS.items():
        count = len(re.findall(rf'\b{re.escape(kw)}\b', text, re.IGNORECASE))
        if count > 0:
            keyword_counts[kw] = count
            keyword_score += min(count * weight, 5)  # 每个关键词最多贡献5分
    keyword_score = min(15, keyword_score)
    score += keyword_score
    details.append(f"关键词得分: {keyword_score:.1f} ({len(keyword_counts)}类关键词)")

    # 6. 代码块得分：最多 10 分
    code_blocks = len(re.findall(r'```[\s\S]*?```', text))
    code_score = min(10, code_blocks * 3)
    score += code_score
    details.append(f"代码块得分: {code_score:.1f} (块数: {code_blocks})")

    # 7. 表格得分：最多 3 分
    tables = len(re.findall(r'\|.*\|.*\|', text))
    table_score = min(3, tables)
    score += table_score
    details.append(f"表格得分: {table_score:.1f} (行数: {tables})")

    # 8. 交叉引用链接得分：最多 2 分
    links = len(re.findall(r'\[([^\]]+)\]\(([^)]+)\)', text))
    link_score = min(2, links * 0.5)
    score += link_score
    details.append(f"链接得分: {link_score:.1f} (链接数: {links})")

    final_score = min(100, max(0, round(score)))
    return final_score, details, {
        "total_words": total_words,
        "inline_math": inline_math,
        "display_math": display_math,
        "code_blocks": code_blocks,
        "tables": tables,
        "links": links,
        "keyword_counts": keyword_counts,
    }


def get_grade(score):
    if score >= 80:
        return "A"
    elif score >= 50:
        return "B"
    elif score >= 20:
        return "C"
    else:
        return "D"


def get_suggestion(score, stats):
    if score >= 80:
        return "质量良好，无需处理"
    elif score >= 50:
        return "内容有基础，建议补充更多数学公式、证明或例子"
    elif score >= 20:
        return "内容薄弱，建议重写：增加实质性数学内容、定理证明或代码示例"
    else:
        suggestions = []
        if stats["total_words"] < 50:
            suggestions.append("严重缺乏文字内容")
        if stats["inline_math"] + stats["display_math"] == 0:
            suggestions.append("无数学公式")
        if stats["code_blocks"] == 0:
            suggestions.append("无代码块")
        if stats["keyword_counts"] == 0:
            suggestions.append("无数学关键词")
        return "必须重写：" + "；".join(suggestions) if suggestions else "内容严重不足，建议删除或完全重写"


def scan_project():
    """扫描项目中的所有 .md 文件"""
    results = []
    pattern = os.path.join(PROJECT_ROOT, "**", "*.md")
    files = glob.glob(pattern, recursive=True)

    for filepath in files:
        if should_exclude(filepath):
            continue
        try:
            with open(filepath, "r", encoding="utf-8") as f:
                content = f.read()
        except Exception as e:
            print(f"警告：无法读取文件 {filepath}: {e}")
            continue

        score, details, stats = calculate_score(filepath, content)
        grade = get_grade(score)
        branch = get_branch(filepath)
        rel_path = os.path.relpath(filepath, PROJECT_ROOT)

        results.append({
            "path": rel_path,
            "absolute_path": filepath,
            "branch": branch,
            "score": score,
            "grade": grade,
            "details": details,
            "stats": stats,
            "suggestion": get_suggestion(score, stats),
        })

    return results


def generate_report(results):
    """生成审计报告"""
    os.makedirs(os.path.dirname(OUTPUT_FILE), exist_ok=True)

    # 统计
    grade_counts = defaultdict(int)
    branch_grade_counts = defaultdict(lambda: defaultdict(int))
    total_score = 0

    for r in results:
        grade_counts[r["grade"]] += 1
        branch_grade_counts[r["branch"]][r["grade"]] += 1
        total_score += r["score"]

    avg_score = total_score / len(results) if results else 0

    # D级和C级文件
    d_files = [r for r in results if r["grade"] == "D"]
    c_files = [r for r in results if r["grade"] == "C"]
    d_files_sorted = sorted(d_files, key=lambda x: x["score"])
    c_files_sorted = sorted(c_files, key=lambda x: x["score"])[:50]

    lines = []
    lines.append("# FormalMath 内容质量审计报告")
    lines.append(f"\n**生成时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    lines.append(f"**扫描文件总数**: {len(results)}")
    lines.append(f"**整体平均得分**: {avg_score:.1f}/100")
    lines.append("")

    # 1. 整体分级统计
    lines.append("## 一、整体分级统计\n")
    lines.append("| 等级 | 分数范围 | 文件数量 | 占比 | 说明 |")
    lines.append("|------|----------|----------|------|------|")
    total = len(results)
    for grade, label, desc in [("A", "80-100", "高质量，无需处理"), ("B", "50-79", "有内容但可深化"), ("C", "20-49", "内容薄弱，建议重写"), ("D", "0-19", "无实质内容，必须重写")]:
        count = grade_counts.get(grade, 0)
        pct = count / total * 100 if total else 0
        lines.append(f"| {grade} | {label} | {count} | {pct:.1f}% | {desc} |")
    lines.append("")

    # 2. 各分支统计
    lines.append("## 二、各分支分级统计\n")
    lines.append("| 分支 | A级 | B级 | C级 | D级 | 总计 | 平均分 |")
    lines.append("|------|-----|-----|-----|-----|------|--------|")
    for branch in sorted(branch_grade_counts.keys()):
        counts = branch_grade_counts[branch]
        total_branch = sum(counts.values())
        branch_scores = [r["score"] for r in results if r["branch"] == branch]
        avg = sum(branch_scores) / len(branch_scores) if branch_scores else 0
        lines.append(f"| {branch} | {counts.get('A', 0)} | {counts.get('B', 0)} | {counts.get('C', 0)} | {counts.get('D', 0)} | {total_branch} | {avg:.1f} |")
    lines.append("")

    # 3. D级文件完整列表
    lines.append(f"## 三、D级文件完整列表（共 {len(d_files_sorted)} 个）\n")
    lines.append("> **必须重写**：这些文件几乎无实质内容\n")
    if d_files_sorted:
        lines.append("| 序号 | 文件路径 | 得分 | 字数 | 公式 | 代码块 | 建议 |")
        lines.append("|------|----------|------|------|------|--------|------|")
        for i, r in enumerate(d_files_sorted, 1):
            stats = r["stats"]
            lines.append(f"| {i} | `{r['path']}` | {r['score']} | {stats['total_words']} | {stats['inline_math'] + stats['display_math']} | {stats['code_blocks']} | {r['suggestion']} |")
    else:
        lines.append("✅ 未发现 D 级文件")
    lines.append("")

    # 4. C级文件 Top 50
    lines.append(f"## 四、C级文件 Top 50（共 {len(c_files)} 个，展示最低分50个）\n")
    lines.append("> **建议重写**：内容薄弱，需补充实质性内容\n")
    if c_files_sorted:
        lines.append("| 序号 | 文件路径 | 得分 | 字数 | 公式 | 代码块 | 建议 |")
        lines.append("|------|----------|------|------|------|--------|------|")
        for i, r in enumerate(c_files_sorted, 1):
            stats = r["stats"]
            lines.append(f"| {i} | `{r['path']}` | {r['score']} | {stats['total_words']} | {stats['inline_math'] + stats['display_math']} | {stats['code_blocks']} | {r['suggestion']} |")
    else:
        lines.append("✅ 未发现 C 级文件")
    lines.append("")

    # 5. 整体质量评分与建议
    lines.append("## 五、整体质量评估\n")
    if avg_score >= 70:
        overall = "良好"
        color = "🟢"
    elif avg_score >= 50:
        overall = "中等"
        color = "🟡"
    elif avg_score >= 30:
        overall = "较差"
        color = "🟠"
    else:
        overall = "严重"
        color = "🔴"

    lines.append(f"- **整体评级**: {color} {overall}（平均分 {avg_score:.1f}）")
    lines.append(f"- **高质量文件(A+B)占比**: {(grade_counts.get('A', 0) + grade_counts.get('B', 0)) / total * 100:.1f}%")
    lines.append(f"- **需重写文件(C+D)占比**: {(grade_counts.get('C', 0) + grade_counts.get('D', 0)) / total * 100:.1f}%")
    lines.append("")
    lines.append("### 优先处理建议\n")
    if d_files_sorted:
        lines.append(f"1. **立即处理 D 级文件**：共 {len(d_files_sorted)} 个，这些文件几乎没有实质内容，建议删除或完全重写")
    if c_files:
        lines.append(f"2. **逐步改进 C 级文件**：共 {len(c_files)} 个，优先处理低分文件，补充数学公式、证明或代码示例")
    if grade_counts.get("B", 0) > 0:
        lines.append(f"3. **深化 B 级文件**：共 {grade_counts.get('B', 0)} 个，可通过增加定理证明和交叉引用提升质量")
    lines.append("")

    # 附录：评分细则
    lines.append("## 附录：评分算法说明\n")
    lines.append("| 维度 | 最高分 | 计算方式 |")
    lines.append("|------|--------|----------|")
    lines.append("| 字数（中文字符+英文单词） | 50 | 每20字1分，最高50 |")
    lines.append("| 数学公式（$...$ / $$...$$） | 20 | 行内公式1.5分/个，行间公式4.5分/个，最高20 |")
    lines.append("| 数学关键词 | 15 | 定理/证明/定义等，每类最高5分，最高15 |")
    lines.append("| 代码块 | 10 | 每块3分，最高10 |")
    lines.append("| 表格 | 3 | 每行1分，最高3 |")
    lines.append("| 交叉引用链接 | 2 | 每个0.5分，最高2 |")
    lines.append("")

    with open(OUTPUT_FILE, "w", encoding="utf-8") as f:
        f.write("\n".join(lines))

    return OUTPUT_FILE


def main():
    print("=" * 60)
    print("FormalMath 内容质量审核")
    print("=" * 60)
    print(f"项目根目录: {PROJECT_ROOT}")
    print("开始扫描 .md 文件...")

    results = scan_project()
    print(f"扫描完成，共 {len(results)} 个文件")

    report_path = generate_report(results)
    print(f"\n报告已生成: {report_path}")

    # 打印摘要
    grade_counts = defaultdict(int)
    for r in results:
        grade_counts[r["grade"]] += 1

    print("\n分级摘要:")
    for g in ["A", "B", "C", "D"]:
        print(f"  {g}级: {grade_counts.get(g, 0)} 个")

    print("\n完成!")


if __name__ == "__main__":
    main()
