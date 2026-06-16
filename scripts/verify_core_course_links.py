#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
校验 5 门核心课程文档中的外部链接可访问性，输出待修复链接报告。

用法：
    python scripts/verify_core_course_links.py
"""

import re
import ssl
import yaml
import json
import urllib.request
from pathlib import Path
from urllib.error import HTTPError, URLError
from datetime import datetime
from concurrent.futures import ThreadPoolExecutor, as_completed

PROJECT_ROOT = Path(__file__).resolve().parents[1]
REPORT_PATH = PROJECT_ROOT / "project" / "00-项目进度报告" / "Phase1-核心课程链接校验报告.md"
CACHE_PATH = PROJECT_ROOT / ".test_cache" / "core_course_link_cache.json"

COURSE_PATTERNS = ["18.100A", "18.701", "18.06", "232br", "Stanford FOAG"]
URL_RE = re.compile(r"https?://[^\s<>\"{}\[\]`]+")

SSL_CTX = ssl._create_unverified_context()
HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) FormalMath-LinkCheck/1.0",
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
}

# 这些域名对 HEAD 支持不稳定，遇到 404 时回退 GET 复核
GET_FALLBACK_DOMAINS = (
    "ocw.mit.edu",
    "math.harvard.edu",
    "people.math.harvard.edu",
)


def parse_frontmatter(text: str):
    if text.startswith("---"):
        end = text.find("---", 3)
        if end != -1:
            try:
                return yaml.safe_load(text[3:end].strip()) or {}
            except yaml.YAMLError:
                return {}
    return {}


def check_url(url: str, timeout: int = 5):
    """对单个 URL 执行 HEAD，必要时回退 GET。返回 (status_code, final_url)。"""
    try:
        req = urllib.request.Request(url, method="HEAD", headers=HEADERS)
        with urllib.request.urlopen(req, timeout=timeout, context=SSL_CTX) as resp:
            return resp.getcode(), resp.geturl()
    except HTTPError as e:
        if e.code in (405, 501, 400):
            return _get_url(url, timeout)
        # 对 HEAD 不友好的域名，404 也回退 GET
        if e.code == 404 and any(d in url for d in GET_FALLBACK_DOMAINS):
            return _get_url(url, timeout)
        return e.code, getattr(e, "url", url)
    except URLError as e:
        return str(e.reason)[:120], url
    except Exception as e:
        return str(e)[:120], url


def _get_url(url: str, timeout: int):
    try:
        req = urllib.request.Request(url, method="GET", headers=HEADERS)
        with urllib.request.urlopen(req, timeout=timeout, context=SSL_CTX) as resp:
            return resp.getcode(), resp.geturl()
    except HTTPError as e:
        return e.code, getattr(e, "url", url)
    except Exception as e:
        return str(e)[:120], url


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


def extract_markdown_link_urls(text: str):
    """提取 Markdown 链接中的 URL，支持 URL 内部平衡的括号。"""
    urls = []
    spans = []
    i = 0
    while i < len(text):
        bracket_close = text.find("](", i)
        if bracket_close == -1:
            break
        # 找到对应的 '['
        start = text.rfind("[", i, bracket_close)
        if start == -1:
            i = bracket_close + 2
            continue
        url_start = bracket_close + 2
        depth = 0
        j = url_start
        while j < len(text):
            ch = text[j]
            if ch == "(":
                depth += 1
            elif ch == ")":
                if depth == 0:
                    break
                depth -= 1
            j += 1
        if j >= len(text):
            i = url_start
            continue
        url_part = text[url_start:j].strip()
        if url_part:
            url = url_part.split()[0]
            if url.startswith("http"):
                urls.append(url)
                spans.append((url_start, j))
        i = j + 1
    return urls, spans


def normalize_url(raw: str) -> str:
    """清洗 URL：平衡括号、去除尾随标点、规范 MIT OCW 路径。"""
    url = raw.rstrip('.,;:!?">')
    # 平衡括号
    open_p = url.count("(")
    close_p = url.count(")")
    if close_p > open_p:
        # 去除多余的尾部 ')'
        diff = close_p - open_p
        while diff > 0 and url.endswith(")"):
            url = url[:-1]
            diff -= 1
    elif open_p > close_p:
        url += ")" * (open_p - close_p)
    # 规范 MIT OCW 旧路径
    if "ocw.mit.edu/courses/mathematics/" in url:
        url = url.replace("ocw.mit.edu/courses/mathematics/", "ocw.mit.edu/courses/")
    return url


def extract_urls(text: str):
    md_urls, md_spans = extract_markdown_link_urls(text)
    urls = set(md_urls)

    # 裸 URL：跳过已识别的 Markdown 链接区间，并跳过后面紧跟 {placeholder} 的情况
    for m in URL_RE.finditer(text):
        start, end = m.span()
        # 跳过 Markdown 链接区间
        if any(start >= s and end <= e for s, e in md_spans):
            continue
        raw = m.group(0)
        # 跳过模板占位前缀，如 https://ncatlab.org/nlab/show/{entry}
        if end < len(text) and text[end] == "{":
            continue
        url = normalize_url(raw)
        if url:
            urls.add(url)
    return urls


def main():
    CACHE_PATH.parent.mkdir(parents=True, exist_ok=True)
    seen = load_cache()
    checked = []
    broken = []
    tasks = []

    print("Collecting URLs from core course documents...")
    for md in PROJECT_ROOT.rglob("*.md"):
        if ".git" in md.parts:
            continue
        text = md.read_text(encoding="utf-8", errors="ignore")
        fm = parse_frontmatter(text)
        course = str(fm.get("course", ""))
        if not any(p in course for p in COURSE_PATTERNS):
            continue
        doc_rel = md.relative_to(PROJECT_ROOT).as_posix()
        for url in extract_urls(text):
            if "{" in url or "}" in url:
                continue
            if url in seen:
                code, final = seen[url]
                checked.append((doc_rel, url, code, final))
                if isinstance(code, int) and code >= 400:
                    broken.append((doc_rel, url, code, final))
                elif isinstance(code, str):
                    broken.append((doc_rel, url, code, final))
            else:
                tasks.append((doc_rel, url))

    total_unique = len({url for _, url in tasks})
    print(f"Found {len(tasks)} URL occurrences ({total_unique} unique) to check.")

    max_workers = min(40, max(4, total_unique // 10 + 1))
    completed = 0
    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        future_to_task = {executor.submit(check_url, url, 5): (doc_rel, url) for doc_rel, url in tasks}
        for future in as_completed(future_to_task):
            doc_rel, url = future_to_task[future]
            try:
                code, final = future.result(timeout=8)
            except Exception as e:
                code, final = str(e)[:120], url
            seen[url] = (code, final)
            checked.append((doc_rel, url, code, final))
            if isinstance(code, int) and code >= 400:
                broken.append((doc_rel, url, code, final))
            elif isinstance(code, str):
                broken.append((doc_rel, url, code, final))
            completed += 1
            if completed % 50 == 0:
                print(f"  checked {completed}/{len(tasks)} ...")
                save_cache(seen)

    save_cache(seen)

    lines = [
        "---",
        "title: Phase 1 核心课程外部链接校验报告",
        "level: meta",
        f"processed_at: '{datetime.now().isoformat()}'",
        "review_status: draft",
        "---",
        "",
        "# Phase 1 核心课程外部链接校验报告",
        "",
        f"**校验时间**: {datetime.now().strftime('%Y年%m月%d日 %H:%M')}",
        f"**校验范围**: 5 门核心课程相关 Markdown 文档",
        f"**检查链接总数**: {len(checked)}",
        f"**疑似失效链接数**: {len(broken)}",
        "",
        "## 一、疑似失效链接清单",
        "",
        "| 文档路径 | 原链接 | 状态码 | 最终 URL |",
        "|----------|--------|--------|----------|",
    ]
    for doc, url, code, final in sorted(broken):
        lines.append(f"| `{doc}` | {url} | {code} | {final} |")

    lines += [
        "",
        "## 二、说明",
        "",
        "- `403/429` 多为访问频率限制或服务器拒绝 HEAD 请求，建议人工复核。",
        "- `404` 表示资源确实缺失，需要替换为有效链接。",
        "- `301/302` 跳转后的目标若返回 `200`，视为可用。",
        "- 本次校验使用并发请求、结果缓存、Markdown 链接精确解析与 MIT OCW 路径规范化。",
    ]

    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Checked {len(checked)} links, found {len(broken)} broken/uncertain.")
    print(f"Report: {REPORT_PATH}")


if __name__ == "__main__":
    main()
