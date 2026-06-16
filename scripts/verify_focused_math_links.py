#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
聚焦数学内容的外部链接可访问性校验。

扫描 docs/、concept/、数学家理念体系/、FormalMath-v2/、FormalMathLean4/
以及 project/ 中除 node_modules 等以外的 Markdown，输出：
    project/00-项目进度报告/Phase1-数学内容外部链接校验报告.md
"""

import json
import urllib.parse
from pathlib import Path
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime

import verify_all_external_links as base

PROJECT_ROOT = Path(__file__).resolve().parents[1]
REPORT_PATH = PROJECT_ROOT / "project" / "00-项目进度报告" / "Phase1-数学内容外部链接校验报告.md"
CACHE_PATH = PROJECT_ROOT / ".test_cache" / "focused_math_link_cache.json"

FOCUSED_PREFIXES = [
    "docs/",
    "concept/",
    "数学家理念体系/",
    "FormalMath-v2/",
    "FormalMathLean4/",
    "project/",
]


def load_cache():
    if CACHE_PATH.exists():
        try:
            return json.loads(CACHE_PATH.read_text(encoding="utf-8"))
        except Exception:
            return {}
    return {}


def save_cache(seen: dict):
    CACHE_PATH.parent.mkdir(parents=True, exist_ok=True)
    CACHE_PATH.write_text(json.dumps(seen, ensure_ascii=False, indent=2), encoding="utf-8")


def doc_category(doc_rel: str) -> str:
    for prefix in FOCUSED_PREFIXES:
        if doc_rel.startswith(prefix):
            return prefix.rstrip("/")
    return "other"


UNCERTAIN_404_DOMAINS = {"plato.stanford.edu", "doi.org", "dx.doi.org"}


def classify(code, url: str = ""):
    if isinstance(code, int):
        domain = ""
        try:
            domain = urllib.parse.urlparse(url).netloc.lower()
        except Exception:
            pass
        if code == 404 and domain in UNCERTAIN_404_DOMAINS:
            return "uncertain"
        if code == 404 or (400 <= code < 500 and code not in (403, 429, 408, 412, 418)):
            return "broken"
        if code >= 500 or code in (403, 429, 408, 412, 418):
            return "uncertain"
        return "ok"
    s = str(code).lower()
    if any(k in s for k in ("timed out", "timeout", "ssl", "eof", "connection", "reset", "refused")):
        return "uncertain"
    return "broken"


def should_skip_path(path: Path) -> bool:
    if any(part in base.EXCLUDE_DIR_PARTS for part in path.parts):
        return True
    rel = path.relative_to(PROJECT_ROOT).as_posix()
    skip_patterns = (
        "docs/管理员手册/",
        "docs/链接维护指南.md",
        "docs/应急预案.md",
        "project/00-项目进度报告/",
        "project/v2-quality-rewrite/workspaces/",
    )
    return any(rel.startswith(p) for p in skip_patterns)


def main():
    CACHE_PATH.parent.mkdir(parents=True, exist_ok=True)
    seen = load_cache()
    checked, broken, tasks = [], [], []

    print("Collecting URLs from focused math Markdown documents...")
    for prefix in FOCUSED_PREFIXES:
        root = PROJECT_ROOT / prefix
        if not root.exists():
            continue
        for md in root.rglob("*.md"):
            if should_skip_path(md):
                continue
            text = md.read_text(encoding="utf-8", errors="ignore")
            doc_rel = md.relative_to(PROJECT_ROOT).as_posix()
            for url in base.extract_urls(text):
                if "{" in url or "}" in url:
                    continue
                if "wikidata.org/entity/" in url:
                    continue
                if url in seen:
                    code, final = seen[url]
                    checked.append((doc_rel, url, code, final))
                    if classify(code, url) != "ok":
                        broken.append((doc_rel, url, code, final))
                else:
                    tasks.append((doc_rel, url))

    total_unique = len({url for _, url in tasks})
    print(f"Found {len(tasks)} URL occurrences ({total_unique} unique) to check.")

    max_workers = min(30, max(4, total_unique // 20 + 1))
    completed = 0
    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        future_to_task = {executor.submit(base.check_url, url, 8): (doc_rel, url) for doc_rel, url in tasks}
        for future in as_completed(future_to_task):
            doc_rel, url = future_to_task[future]
            try:
                code, final = future.result(timeout=12)
            except Exception as e:
                code, final = str(e)[:120], url
            seen[url] = (code, final)
            checked.append((doc_rel, url, code, final))
            if classify(code, url) != "ok":
                broken.append((doc_rel, url, code, final))
            completed += 1
            if completed % 100 == 0:
                print(f"  checked {completed}/{len(tasks)} ...")
                save_cache(seen)

    save_cache(seen)

    uncertain = [(d, u, c, f) for d, u, c, f in broken if classify(c, u) == "uncertain"]
    confirmed = [(d, u, c, f) for d, u, c, f in broken if classify(c, u) == "broken"]

    domain_counter = Counter()
    for _, url, _, _ in confirmed:
        try:
            domain = urllib.parse.urlparse(url).netloc
            domain_counter[domain] += 1
        except Exception:
            domain_counter["[parse-error]"] += 1

    cat_stats = Counter()
    cat_broken = Counter()
    cat_uncertain = Counter()
    for doc, url, code, _ in checked:
        cat = doc_category(doc)
        cat_stats[cat] += 1
        if classify(code, url) == "broken":
            cat_broken[cat] += 1
        elif classify(code, url) == "uncertain":
            cat_uncertain[cat] += 1

    top_confirmed = sorted(confirmed, key=lambda x: (x[1], x[0]))[:500]
    top_uncertain = sorted(uncertain, key=lambda x: (x[1], x[0]))[:200]

    lines = [
        "---",
        "title: Phase 1 数学内容外部链接校验报告",
        "level: meta",
        f"processed_at: '{datetime.now().isoformat()}'",
        "review_status: draft",
        "---",
        "",
        "# Phase 1 数学内容外部链接校验报告",
        "",
        f"**校验时间**: {datetime.now().strftime('%Y年%m月%d日 %H:%M')}",
        f"**校验范围**: docs/、concept/、数学家理念体系/、FormalMath-v2/、FormalMathLean4/、project/（排除 node_modules 等）",
        f"**检查链接总数**: {len(checked)}",
        f"**确认失效链接数**: {len(confirmed)} | **不确定/瞬态链接数**: {len(uncertain)}",
        f"**涉及唯一 URL 数**: {len({u for _, u, _, _ in checked})}",
        "",
        "## 一、按文档分类统计",
        "",
        "| 分类 | 检查链接数 | 确认失效 | 不确定/瞬态 |",
        "|------|-----------|---------|------------|",
    ]
    for cat in sorted(cat_stats.keys(), key=lambda c: -cat_stats[c]):
        lines.append(f"| {cat} | {cat_stats[cat]} | {cat_broken.get(cat, 0)} | {cat_uncertain.get(cat, 0)} |")

    lines += [
        "",
        "## 二、确认失效链接按域名汇总（Top 30）",
        "",
        "| 域名 | 失效数 |",
        "|------|-------|",
    ]
    for domain, count in domain_counter.most_common(30):
        lines.append(f"| {domain} | {count} |")

    lines += [
        "",
        "## 三、确认失效链接清单（前 500 条）",
        "",
        "| 文档路径 | 原链接 | 状态码 | 最终 URL |",
        "|----------|--------|--------|----------|",
    ]
    for doc, url, code, final in top_confirmed:
        lines.append(f"| `{doc}` | {url} | {code} | {final} |")

    lines += [
        "",
        "## 四、不确定/瞬态链接清单（前 200 条）",
        "",
        "| 文档路径 | 原链接 | 状态码 | 最终 URL |",
        "|----------|--------|--------|----------|",
    ]
    for doc, url, code, final in top_uncertain:
        lines.append(f"| `{doc}` | {url} | {code} | {final} |")

    lines += [
        "",
        "## 五、说明",
        "",
        "- **确认失效**：`404`、不可解析主机、非瞬态 `4xx` 等，需要替换或删除。",
        "- **不确定/瞬态**：`403/429` 频率限制、`5xx`、超时、SSL 握手异常等，建议人工复核或稍后重试。",
        "- `301/302` 跳转后的目标若返回 `200`，视为可用。",
        "- Wikidata 实体页因对批量 HEAD 敏感，已跳过校验。",
    ]

    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Checked {len(checked)} links, found {len(confirmed)} confirmed broken, {len(uncertain)} uncertain.")
    print(f"Report: {REPORT_PATH}")


if __name__ == "__main__":
    main()
