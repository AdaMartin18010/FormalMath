#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
校验 5 门核心课程文档中的外部链接可访问性，输出待修复链接报告。

用法：
    python scripts/verify_core_course_links.py
"""

import re
import yaml
import urllib.request
from pathlib import Path
from urllib.error import HTTPError, URLError
from datetime import datetime

PROJECT_ROOT = Path(__file__).resolve().parents[1]
REPORT_PATH = PROJECT_ROOT / "project" / "00-项目进度报告" / "Phase1-核心课程链接校验报告.md"

COURSE_PATTERNS = ["18.100A", "18.701", "18.06", "232br", "Stanford FOAG"]
MD_LINK_RE = re.compile(r"!?\[[^\]]*\]\(([^)]+)\)")
URL_RE = re.compile(r"https?://[^\s<>\"{}\[\]`]+")


def parse_frontmatter(text: str):
    if text.startswith("---"):
        end = text.find("---", 3)
        if end != -1:
            try:
                return yaml.safe_load(text[3:end].strip()) or {}
            except yaml.YAMLError:
                return {}
    return {}


def check_url(url: str, timeout=8):
    req = urllib.request.Request(
        url,
        method="HEAD",
        headers={
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) FormalMath-LinkCheck/1.0",
        },
    )
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return resp.getcode(), resp.geturl()
    except HTTPError as e:
        # 某些服务器不支持 HEAD，回退 GET
        if e.code in (405, 501):
            try:
                req = urllib.request.Request(
                    url,
                    method="GET",
                    headers={
                        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) FormalMath-LinkCheck/1.0",
                    },
                )
                with urllib.request.urlopen(req, timeout=timeout) as resp:
                    return resp.getcode(), resp.geturl()
            except Exception as e2:
                return getattr(e2, "code", str(e2)), url
        return e.code, url
    except URLError as e:
        return str(e.reason), url
    except Exception as e:
        return str(e), url


def main():
    broken = []
    checked = []
    seen = {}
    for md in PROJECT_ROOT.rglob("*.md"):
        if ".git" in md.parts:
            continue
        text = md.read_text(encoding="utf-8", errors="ignore")
        fm = parse_frontmatter(text)
        course = str(fm.get("course", ""))
        if not any(p in course for p in COURSE_PATTERNS):
            continue
        urls = set()
        # 先提取 Markdown 链接中的 URL
        for m in MD_LINK_RE.finditer(text):
            candidate = m.group(1).split()[0]
            if candidate.startswith("http"):
                urls.add(candidate)
        # 再提取裸 URL
        for raw in URL_RE.findall(text):
            url = raw.rstrip('.,;:!?">')
            if '(' in url and not url.endswith(')'):
                if raw.endswith(')'):
                    url += ')'
            urls.add(url)
        for url in urls:
            # 跳过模板占位链接
            if '{' in url or '}' in url:
                continue
            if url in seen:
                code, final = seen[url]
            else:
                code, final = check_url(url)
                seen[url] = (code, final)
            checked.append((md.relative_to(PROJECT_ROOT).as_posix(), url, code, final))
            if isinstance(code, int) and code >= 400:
                broken.append((md.relative_to(PROJECT_ROOT).as_posix(), url, code, final))
            elif isinstance(code, str):
                broken.append((md.relative_to(PROJECT_ROOT).as_posix(), url, code, final))

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

    lines += ["", "## 二、说明", "", "- `403/429` 多为访问频率限制或服务器拒绝 HEAD 请求，建议人工复核。", "- `404` 表示资源确实缺失，需要替换为有效链接。", "- `301/302` 跳转后的目标若返回 `200`，视为可用。", ""]

    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Checked {len(checked)} links, found {len(broken)} broken/uncertain.")
    print(f"Report: {REPORT_PATH}")


if __name__ == "__main__":
    main()
