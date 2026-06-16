#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
为 Stacks Project Tag 对齐映射表中的失效路径寻找现有文件，并更新映射表。

用法：
    python scripts/realign_stacks_mapping_paths.py
"""

import re
import yaml
from pathlib import Path
from collections import Counter

PROJECT_ROOT = Path(__file__).resolve().parents[1]
MAPPING_FILE = PROJECT_ROOT / "ref" / "Stacks-Project-Tag-对齐映射表.md"


def parse_frontmatter_title(path: Path):
    text = path.read_text(encoding="utf-8", errors="ignore")
    if not text.startswith("---"):
        return ""
    end = text.find("---", 3)
    if end == -1:
        return ""
    try:
        fm = yaml.safe_load(text[3:end].strip()) or {}
    except yaml.YAMLError:
        return ""
    return fm.get("title", "")


def collect_candidate_docs():
    candidates = []
    for p in (PROJECT_ROOT / "docs").rglob("*.md"):
        if any(x in p.parts for x in ("node_modules", ".git", "00-归档", "归档")):
            continue
        if p.name.startswith("00-"):
            continue
        rel = p.relative_to(PROJECT_ROOT).as_posix()
        # 排除明显非数学内容的目录
        if any(seg in rel for seg in ("00-FAQ", "00-习题示例反例库", "00-工作示例库", "00-核心概念理解三问", "00-表征实例库")):
            continue
        title = parse_frontmatter_title(p)
        candidates.append((p, rel, title))
    return candidates


def extract_keywords(text: str):
    # 提取中英文关键词：去掉常见停用词和标点
    stop = {"the", "of", "and", "to", "a", "in", "for", "is", "on", " lemma", " theorem", " definition", " section", " proposition"}
    words = re.findall(r"[A-Za-z]+|[\u4e00-\u9fff]+", text)
    filtered = []
    for w in words:
        wl = w.lower()
        if wl in stop or len(w) <= 1:
            continue
        filtered.append(w)
    return filtered


def score(doc_rel: str, title: str, keywords: list):
    text = (doc_rel + " " + title).lower()
    score = 0
    for kw in keywords:
        if kw.lower() in text:
            score += 1
    # 路径越短越通用，稍微加分
    if score > 0:
        score += 1.0 / (len(doc_rel.split("/")) + 1)
    return score


def find_best_match(current_path: str, title: str, candidates: list):
    if current_path:
        p = PROJECT_ROOT / current_path
        if p.exists():
            return current_path, "exists"

    keywords = extract_keywords(title)
    if not keywords:
        return "", "no_keywords"

    best = None
    best_score = 0
    for _, rel, doc_title in candidates:
        s = score(rel, doc_title, keywords)
        if s > best_score:
            best_score = s
            best = rel

    # 阈值：至少命中 2 个关键词
    if best_score >= 2:
        return best, f"matched_score_{best_score:.2f}"
    return "", "no_good_match"


def update_mapping_table(candidates: list):
    content = MAPPING_FILE.read_text(encoding="utf-8", errors="ignore")
    lines = content.splitlines()
    updated = []
    changes = []
    for line in lines:
        stripped = line.strip()
        if not stripped.startswith("|") or "Stacks Tag" in stripped or "---" in stripped:
            updated.append(line)
            continue
        cells = [c.strip() for c in stripped.strip("|").split("|")]
        if len(cells) < 5:
            updated.append(line)
            continue
        tag, typ, title, doc_ref, status = cells[:5]
        if status == "❌ 暂不适用":
            updated.append(line)
            continue
        current = ""
        m = re.search(r"`([^`]+\.(?:md|lean))`", doc_ref)
        if m:
            current = m.group(1)
        new_path, reason = find_best_match(current, title, candidates)
        if new_path and new_path != current:
            new_ref = f"`{new_path}`"
            cells[3] = new_ref
            if status in ("⏳", "⏳待对齐"):
                cells[4] = "🔄 对齐中"
            updated.append("| " + " | ".join(cells) + " |")
            changes.append((tag, title, current, new_path, reason))
        else:
            updated.append(line)

    MAPPING_FILE.write_text("\n".join(updated), encoding="utf-8")
    return changes


def main():
    candidates = collect_candidate_docs()
    print(f"Collected {len(candidates)} candidate docs.")
    changes = update_mapping_table(candidates)
    print(f"Updated {len(changes)} mappings.")
    for tag, title, old, new, reason in changes:
        print(f"  {tag}: {title}")
        print(f"      {old or '(none)'} -> {new} ({reason})")


if __name__ == "__main__":
    main()
