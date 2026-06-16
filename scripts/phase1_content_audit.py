#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Phase 1 内容质量抽样审计脚本

目标：
1. 对全库 Markdown 文档进行分层抽样审计
2. 检查 frontmatter 完整性、结构要素、参考文献质量、外部对齐标识
3. 识别重复/空壳文档
4. 生成 Phase 1 内容质量审计报告

用法：
    python scripts/phase1_content_audit.py
"""

import yaml
import re
import hashlib
import random
from pathlib import Path
from collections import Counter, defaultdict
from datetime import datetime

PROJECT_ROOT = Path(__file__).resolve().parents[1]
DOCS_DIR = PROJECT_ROOT / "docs"
CONCEPT_DIR = PROJECT_ROOT / "concept"
MATH_DIR = PROJECT_ROOT / "数学家理念体系"
REPORT_PATH = PROJECT_ROOT / "project" / "00-项目进度报告" / "Phase1-内容质量审计报告.md"

# 抽样配置
SAMPLE_SIZE = 300
STRATA = {
    "silver_courses": (DOCS_DIR / "00-银层核心课程", 80),
    "concept": (CONCEPT_DIR, 60),
    "mathematicians": (MATH_DIR, 80),
    "other_docs": (DOCS_DIR, 80),
}

# 结构要素关键词
SECTION_PATTERNS = {
    "definition": r"定义|Definition",
    "theorem": r"定理|Theorem",
    "proof": r"证明|Proof",
    "example": r"例题|Example|例子|Example\(s\)",
    "exercise": r"习题|Exercise|问题|Problem Set|作业",
    "solution": r"解答|Solution|答案|Proof \(continued\)",
    "motivation": r"动机|Motivation|直观|Intuition|为什么",
    "prerequisite": r"前置|Prerequisite|前置知识|先修",
    "common_mistake": r"常见误区|常见错误|误区|Mistake|Error",
    "references": r"参考|Reference|Bibliography|文献",
}

# 引用标识符
IDENTIFIER_PATTERNS = {
    "doi": r"\b(10\.\d{4,9}/[-._;()/:A-Za-z0-9]+)\b",
    "isbn": r"ISBN[\s:-]*(\d[\d\s-]{8,}X?)",
    "arxiv": r"arXiv:\s*([\d\.]+(?:\s*\[[^\]]+\])?)",
    "mr": r"MR\s*(\d{6,})",
    "zbmath": r"zbmath\.org/\?q=(an|au):[^\s\)\]\>\"\'\`]+?",
    "wikidata": r"wikidata\.org/entity/(Q\d+)",
    "stacks_tag": r"stacks\.math\.columbia\.edu/tag/[A-Z0-9]{4}",
    "mactutor": r"mathshistory\.st-andrews\.ac\.uk/Biographies/[^/\s]+",
}


def find_markdown_files(root: Path, exclude_archived=True):
    """查找所有 Markdown 文件，排除 node_modules、.git、归档目录"""
    if not root.exists():
        return []
    files = []
    for p in root.rglob("*.md"):
        # 排除隐藏目录、node_modules、归档
        parts = set(p.parts)
        if any(x in parts for x in ("node_modules", ".git", "00-归档", "归档")):
            continue
        if p.name.startswith("_"):
            continue
        files.append(p)
    return files


def parse_frontmatter(text: str):
    """解析 YAML frontmatter，返回 (metadata, body)"""
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


def has_section(body: str, pattern: str):
    """检查正文是否包含某类结构要素"""
    return bool(re.search(pattern, body, re.IGNORECASE))


def count_identifiers(body: str):
    """统计各类精确引用标识符数量"""
    counts = {}
    for key, pat in IDENTIFIER_PATTERNS.items():
        counts[key] = len(re.findall(pat, body, re.IGNORECASE))
    return counts


def get_word_count(body: str):
    """估算中文字数（字符数）"""
    # 去除标点、代码块后统计字符
    text = re.sub(r"```[\s\S]*?```", "", body)
    text = re.sub(r"`[^`]+`", "", text)
    text = re.sub(r"[!-/:-@[-`{-~]", "", text)
    return len(text.replace(" ", "").replace("\n", ""))


def compute_hash(content: str):
    return hashlib.sha256(content.encode("utf-8")).hexdigest()[:16]


def stratified_sample(all_files_by_strata: dict):
    """按层抽样"""
    sampled = []
    for stratum, files in all_files_by_strata.items():
        target = STRATA[stratum][1]
        if len(files) <= target:
            chosen = files
        else:
            chosen = random.sample(files, target)
        for f in chosen:
            sampled.append((stratum, f))
    random.shuffle(sampled)
    return sampled


def audit_document(path: Path):
    """审计单个文档，返回结果字典"""
    rel = path.relative_to(PROJECT_ROOT).as_posix()
    text = path.read_text(encoding="utf-8", errors="ignore")
    meta, body = parse_frontmatter(text)
    if meta is None:
        return {
            "rel": rel,
            "error": "frontmatter_parse_error",
            "word_count": 0,
        }

    wc = get_word_count(body)
    sections = {k: has_section(body, v) for k, v in SECTION_PATTERNS.items()}
    id_counts = count_identifiers(text)
    ref_density = sum(id_counts.values()) / (wc / 1000) if wc > 0 else 0

    # frontmatter 字段检查
    required = ["title"]
    missing_fields = [f for f in required if not meta.get(f)]
    if meta.get("level") == "silver":
        for f in ["course", "chapter", "msc_primary"]:
            if not meta.get(f):
                missing_fields.append(f)

    external_ids = meta.get("external_ids") or {}
    has_external_ids = bool(external_ids)

    return {
        "rel": rel,
        "title": meta.get("title", ""),
        "level": meta.get("level", ""),
        "course": meta.get("course", ""),
        "chapter": meta.get("chapter", ""),
        "msc_primary": meta.get("msc_primary", ""),
        "word_count": wc,
        "sections": sections,
        "id_counts": id_counts,
        "ref_density": ref_density,
        "missing_fields": missing_fields,
        "has_external_ids": has_external_ids,
        "hash": compute_hash(text),
    }


def generate_report(results: list, all_files_unique: list, duplicates: dict):
    """生成审计报告"""
    total = len(results)
    silver = [r for r in results if r.get("level") == "silver"]
    copper = [r for r in results if r.get("level") == "copper"]
    gold = [r for r in results if r.get("level") == "gold"]

    # 结构要素统计
    section_stats = {k: sum(1 for r in results if r.get("sections", {}).get(k)) for k in SECTION_PATTERNS}

    # 引用标识符统计
    id_totals = Counter()
    density_sum = 0
    density_count = 0
    for r in results:
        if "id_counts" in r:
            for k, v in r["id_counts"].items():
                id_totals[k] += v
            if r["word_count"] > 100:
                density_sum += r["ref_density"]
                density_count += 1
    avg_density = density_sum / density_count if density_count else 0

    # frontmatter 问题
    parse_errors = [r for r in results if "error" in r]
    missing_field_docs = [r for r in results if r.get("missing_fields")]
    external_id_docs = [r for r in results if r.get("has_external_ids")]

    # 短文档（疑似空壳）
    short_docs = [r for r in results if r.get("word_count", 0) < 300]

    lines = []
    lines.append("---")
    lines.append("title: FormalMath Phase 1 内容质量审计报告")
    lines.append("level: meta")
    lines.append(f"processed_at: '{datetime.now().isoformat()}'")
    lines.append("review_status: draft")
    lines.append("---")
    lines.append("")
    lines.append("# FormalMath Phase 1 内容质量审计报告")
    lines.append("")
    lines.append(f"**生成日期**: {datetime.now().strftime('%Y年%m月%d日')}  ")
    lines.append(f"**审计范围**: 全库分层抽样 {total} 篇 Markdown 文档  ")
    lines.append(f"**全库文档估算**: {len(all_files_unique)} 篇 Markdown  ")
    lines.append("")

    lines.append("## 一、抽样分布")
    lines.append("")
    lines.append("| 分层 | 抽样数量 | 全库估算 |")
    lines.append("|------|---------|---------|")
    strata_counts = Counter(s for s, _ in STRATA.items())  # placeholder
    # 重新统计实际抽样的分层
    actual_strata = Counter(r["stratum"] for r in results if "stratum" in r)
    for s, target in STRATA.items():
        all_count = len(find_markdown_files(target[0]))
        lines.append(f"| {s} | {actual_strata.get(s, 0)} | {all_count} |")
    lines.append("")

    lines.append("## 二、文档层级分布（样本内）")
    lines.append("")
    lines.append("| 层级 | 数量 | 占比 |")
    lines.append("|------|------|------|")
    lines.append(f"| 银层 (silver) | {len(silver)} | {len(silver)/total*100:.1f}% |")
    lines.append(f"| 铜层 (copper) | {len(copper)} | {len(copper)/total*100:.1f}% |")
    lines.append(f"| 金层 (gold) | {len(gold)} | {len(gold)/total*100:.1f}% |")
    lines.append(f"| 未标注 | {total - len(silver) - len(copper) - len(gold)} | {(total - len(silver) - len(copper) - len(gold))/total*100:.1f}% |")
    lines.append("")

    lines.append("## 三、结构要素覆盖率（样本内）")
    lines.append("")
    lines.append("| 结构要素 | 覆盖文档数 | 覆盖率 |")
    lines.append("|---------|-----------|-------|")
    for k, v in section_stats.items():
        lines.append(f"| {k} | {v} | {v/total*100:.1f}% |")
    lines.append("")

    lines.append("## 四、参考文献质量")
    lines.append("")
    lines.append("| 标识符类型 | 出现次数 |")
    lines.append("|-----------|---------|")
    for k, v in id_totals.items():
        lines.append(f"| {k.upper()} | {v} |")
    lines.append("")
    lines.append(f"- 平均引用密度：{avg_density:.2f} 条精确标识符 / 千字")
    lines.append(f"- 含外部对齐标识（external_ids）的文档：{len(external_id_docs)} / {total} ({len(external_id_docs)/total*100:.1f}%)")
    lines.append("")

    lines.append("## 五、Frontmatter 与元数据问题")
    lines.append("")
    lines.append(f"- Frontmatter 解析错误：{len(parse_errors)} 篇")
    lines.append(f"- 缺少必要字段的文档：{len(missing_field_docs)} 篇")
    lines.append(f"- 疑似空壳文档（<300 字）：{len(short_docs)} 篇")
    lines.append("")
    if missing_field_docs:
        lines.append("### 缺少必要字段示例（前 20）")
        lines.append("")
        for r in missing_field_docs[:20]:
            lines.append(f"- `{r['rel']}`: {', '.join(r['missing_fields'])}")
        lines.append("")

    lines.append("## 六、重复/相似文档")
    lines.append("")
    lines.append(f"- 发现内容哈希重复组：{len(duplicates)} 组")
    lines.append(f"- 涉及文档数：{sum(len(v) for v in duplicates.values())} 篇")
    lines.append("")
    if duplicates:
        lines.append("### 重复组示例（前 10）")
        lines.append("")
        for i, (h, paths) in enumerate(list(duplicates.items())[:10], 1):
            lines.append(f"**组 {i}** (hash: {h})")
            for p in paths:
                lines.append(f"- `{p}`")
            lines.append("")

    lines.append("## 七、关键发现与建议")
    lines.append("")
    # 自动生成一些发现
    low_def = section_stats.get("definition", 0) / total * 100
    low_proof = section_stats.get("proof", 0) / total * 100
    low_ex = section_stats.get("exercise", 0) / total * 100
    lines.append(f"1. **定义覆盖率**: {low_def:.1f}% 的样本文档包含「定义」，达到银层要求需接近 100%。")
    lines.append(f"2. **证明覆盖率**: {low_proof:.1f}% 的样本文档包含「证明」，核心课程需大幅提升。")
    lines.append(f"3. **习题覆盖率**: {low_ex:.1f}% 的样本文档包含「习题」，银层课程需每章配套习题。")
    lines.append(f"4. **引用密度**: 平均 {avg_density:.2f} 条/千字，远低于目标 2~3 条/千字。")
    lines.append(f"5. **外部对齐**: 仅 {len(external_id_docs)/total*100:.1f}% 文档含 external_ids，语义对齐任重道远。")
    lines.append(f"6. **空壳文档**: {len(short_docs)} 篇样本（{len(short_docs)/total*100:.1f}%）字数少于 300，建议合并或归档。")
    lines.append("")

    lines.append("## 八、下一阶段行动")
    lines.append("")
    lines.append("1. 对 5 门核心课程逐章进行 L1-L6 语义对齐，补齐定义、定理证明、习题解答。")
    lines.append("2. 为银层文档补充精确引用（DOI/ISBN/arXiv ID/MR Number）。")
    lines.append("3. 清理并合并空壳/重复文档，冻结铜层大规模扩张。")
    lines.append("4. 在 frontmatter 中注入 `external_ids`，建立与 MIT OCW / Stacks / nLab / Wikidata 的语义链接。")
    lines.append("")

    return "\n".join(lines)


def main():
    random.seed(42)

    # 收集各层文件
    all_files_by_strata = {}
    all_files = []
    for stratum, (root, target) in STRATA.items():
        files = find_markdown_files(root)
        all_files_by_strata[stratum] = files
        all_files.extend(files)

    # 去重：基于全库内容哈希（先按 resolve 路径去重，避免不同抽样层重复遍历同一文件）
    seen_paths = set()
    unique_files = []
    for f in all_files:
        rp = f.resolve()
        if rp not in seen_paths:
            seen_paths.add(rp)
            unique_files.append(f)

    hash_to_paths = defaultdict(list)
    for f in unique_files:
        content = f.read_text(encoding="utf-8", errors="ignore")
        h = compute_hash(content)
        hash_to_paths[h].append(f.relative_to(PROJECT_ROOT).as_posix())
    duplicates = {h: paths for h, paths in hash_to_paths.items() if len(set(paths)) > 1}

    # 抽样
    sampled = stratified_sample(all_files_by_strata)

    # 审计
    results = []
    for stratum, path in sampled:
        r = audit_document(path)
        r["stratum"] = stratum
        results.append(r)

    # 生成报告
    report = generate_report(results, unique_files, duplicates)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    REPORT_PATH.write_text(report, encoding="utf-8")
    print(f"Audit complete. Sampled {len(results)} docs.")
    print(f"Report written to: {REPORT_PATH}")


if __name__ == "__main__":
    main()
