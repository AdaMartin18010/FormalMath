#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
全库外部链接可访问性校验。

输出：
    project/00-项目进度报告/Phase1-全库外部链接校验报告.md
"""

import re
import ssl
import yaml
import json
import urllib.request
import urllib.parse
from pathlib import Path
from urllib.error import HTTPError, URLError
from datetime import datetime
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed

PROJECT_ROOT = Path(__file__).resolve().parents[1]
REPORT_PATH = PROJECT_ROOT / "project" / "00-项目进度报告" / "Phase1-全库外部链接校验报告.md"
CACHE_PATH = PROJECT_ROOT / ".test_cache" / "all_external_link_cache.json"
URL_RE = re.compile(r"https?://[^\s<>\"{}\[\]`]+")

SSL_CTX = ssl._create_unverified_context()
HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) FormalMath-LinkCheck/1.0",
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
}
GET_FALLBACK_DOMAINS = (
    "ocw.mit.edu",
    "math.harvard.edu",
    "people.math.harvard.edu",
    "wikidata.org",
    "zbmath.org",
    "ncatlab.org",
    "en.wikipedia.org",
    "zh.wikipedia.org",
    "stacks.math.columbia.edu",
    "mathshistory.st-andrews.ac.uk",
    "mathoverflow.net",
    "mathworld.wolfram.com",
    "arxiv.org",
    "doi.org",
    "leanprover-community.github.io",
    "leanprover.github.io",
    "us.metamath.org",
)

EXCLUDE_DIR_PARTS = {
    ".git", "node_modules", ".venv", "venv", "__pycache__",
    "dist", "build", "target", "00-归档", "00-项目进度报告",
}

CATEGORY_PREFIXES = [
    ("docs", "docs/"),
    ("concept", "concept/"),
    ("mathematicians", "数学家理念体系/"),
    ("FormalMath-v2", "FormalMath-v2/"),
    ("FormalMathLean4", "FormalMathLean4/"),
    ("FormalMath-Enhanced", "FormalMath-Enhanced/"),
    ("FormalMath-Interactive", "FormalMath-Interactive/"),
    ("project", "project/"),
]


def parse_frontmatter(text: str):
    if text.startswith("---"):
        end = text.find("---", 3)
        if end != -1:
            try:
                return yaml.safe_load(text[3:end].strip()) or {}
            except yaml.YAMLError:
                return {}
    return {}


def prepare_url(url: str) -> str:
    """对含中文/特殊字符的 URL 进行安全编码，避免 ascii codec 错误。"""
    try:
        parsed = urllib.parse.urlparse(url)
        # 主机使用 IDNA 编码
        try:
            netloc = parsed.netloc.encode("idna").decode("ascii")
        except Exception:
            netloc = parsed.netloc
        # 路径、查询、片段已编码的 % 需要保留；nLab 等使用 + 表示空格，也保留
        path_safe = "/%:+()~!$&'*,;="
        query_safe = "&=+%:+()~!$&'*,;="
        return urllib.parse.urlunparse(parsed._replace(
            netloc=netloc,
            path=urllib.parse.quote(parsed.path, safe=path_safe),
            query=urllib.parse.quote(parsed.query, safe=query_safe),
            fragment=urllib.parse.quote(parsed.fragment, safe="%"),
        ))
    except Exception:
        return url


def check_url(url: str, timeout: int = 5):
    safe_url = prepare_url(url)
    req = urllib.request.Request(safe_url, method="HEAD", headers=HEADERS)
    try:
        with urllib.request.urlopen(req, timeout=timeout, context=SSL_CTX) as resp:
            return resp.getcode(), resp.geturl()
    except HTTPError as e:
        # 对 4xx 普遍回退 GET：很多站点拒绝 HEAD 但 GET 正常（如 nLab、Wolfram、NIST 等）
        if e.code in (405, 501, 400, 429, 403, 404):
            return _get_url(url, timeout)
        return e.code, getattr(e, "url", url)
    except URLError as e:
        return str(e.reason)[:120], url
    except Exception as e:
        return str(e)[:120], url


def _get_url(url: str, timeout: int):
    safe_url = prepare_url(url)
    try:
        req = urllib.request.Request(safe_url, method="GET", headers=HEADERS)
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
    urls, spans, link_regions = [], [], []
    i = 0
    while i < len(text):
        bracket_close = text.find("](", i)
        if bracket_close == -1:
            break
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
                # 记录整个 Markdown 链接语法区域，避免裸 URL 正则捕获到链接后的正文
                link_regions.append((bracket_close, j + 1))
        i = j + 1
    return urls, spans, link_regions


def normalize_url(raw: str) -> str:
    # 去除尾随的非 URL 字符（包括中文正文、Markdown 格式符号等）
    allowed = set(
        "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789"
        "%_-+=&?#./:~@!$*(),;'[]{}|\""
    )
    url = raw
    while url and url[-1] not in allowed:
        url = url[:-1]
    # 再去除允许的标点但不应出现在 URL 末尾的字符
    url = url.rstrip('.,;:!?*\'"）】」』｝］')
    # 平衡圆括号
    open_p, close_p = url.count("("), url.count(")")
    if close_p > open_p:
        diff = close_p - open_p
        while diff > 0 and url.endswith(")"):
            url = url[:-1]
            diff -= 1
    elif open_p > close_p:
        url += ")" * (open_p - close_p)
    if "ocw.mit.edu/courses/mathematics/" in url:
        url = url.replace("ocw.mit.edu/courses/mathematics/", "ocw.mit.edu/courses/")
    return url


def extract_urls(text: str):
    md_urls, md_spans, link_regions = extract_markdown_link_urls(text)
    urls = set(md_urls)
    for m in URL_RE.finditer(text):
        start, end = m.span()
        # 跳过位于 Markdown 链接语法区域内的裸 URL 匹配
        if any(start >= s and end <= e for s, e in md_spans):
            continue
        if any(not (end <= s or start >= e) for s, e in link_regions):
            continue
        raw = m.group(0)
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

    def should_skip_path(path: Path) -> bool:
        return any(part in EXCLUDE_DIR_PARTS for part in path.parts)

    print("Collecting URLs from all Markdown documents...")
    for md in PROJECT_ROOT.rglob("*.md"):
        if should_skip_path(md):
            continue
        text = md.read_text(encoding="utf-8", errors="ignore")
        doc_rel = md.relative_to(PROJECT_ROOT).as_posix()
        for url in extract_urls(text):
            if "{" in url or "}" in url:
                continue
            if "wikidata.org/entity/" in url:
                continue
            if url in seen:
                code, final = seen[url]
                checked.append((doc_rel, url, code, final))
                if (isinstance(code, int) and code >= 400) or isinstance(code, str):
                    broken.append((doc_rel, url, code, final))
            else:
                tasks.append((doc_rel, url))

    total_unique = len({url for _, url in tasks})
    print(f"Found {len(tasks)} URL occurrences ({total_unique} unique) to check.")

    max_workers = min(50, max(4, total_unique // 20 + 1))
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
            if (isinstance(code, int) and code >= 400) or isinstance(code, str):
                broken.append((doc_rel, url, code, final))
            completed += 1
            if completed % 200 == 0:
                print(f"  checked {completed}/{len(tasks)} ...")
                save_cache(seen)

    save_cache(seen)

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

    def doc_category(doc_rel: str) -> str:
        for name, prefix in CATEGORY_PREFIXES:
            if doc_rel.startswith(prefix):
                return name
        return "other"

    uncertain = [(d, u, c, f) for d, u, c, f in broken if classify(c, u) == "uncertain"]
    confirmed = [(d, u, c, f) for d, u, c, f in broken if classify(c, u) == "broken"]

    # 按域名汇总（确认失效）
    domain_counter = Counter()
    for _, url, code, _ in confirmed:
        try:
            domain = urllib.parse.urlparse(url).netloc
            domain_counter[domain] += 1
        except Exception:
            domain_counter["[parse-error]"] += 1

    # 按分类汇总
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
        "title: Phase 1 全库外部链接校验报告",
        "level: meta",
        f"processed_at: '{datetime.now().isoformat()}'",
        "review_status: draft",
        "---",
        "",
        "# Phase 1 全库外部链接校验报告",
        "",
        f"**校验时间**: {datetime.now().strftime('%Y年%m月%d日 %H:%M')}",
        f"**校验范围**: 全库 Markdown 文档（排除 node_modules / .git / dist / build / 00-归档 等）",
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
