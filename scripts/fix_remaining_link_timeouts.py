#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
修复核心课程链接校验中剩余的 SSL 超时/重定向问题。
"""

import re
import yaml
import urllib.parse
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]
COURSE_PATTERNS = ["18.100A", "18.701", "18.06", "232br", "Stanford FOAG"]

STACKS_QUERY_MAP = {
    "%E5%B1%82": "sheaf",
    "%E6%8B%89%E6%A0%BC%E6%9C%97%E6%97%A5": "Lagrange",
    "%E4%B8%8A%E5%90%8C%E8%B0%83": "cohomology",
    "%E6%A8%A1": "module",
    "%E4%BB%8B%E5%80%BC%E5%AE%9A%E7%90%86": "intermediate+value+theorem",
    "%E6%94%B6%E6%95%9B": "convergence",
    "%E7%9F%A9%E9%98%B5": "matrix",
}


def parse_frontmatter(text: str):
    if text.startswith("---"):
        end = text.find("---", 3)
        if end != -1:
            fm_text = text[3:end].strip()
            body = text[end + 3 :].lstrip("\n")
            try:
                return yaml.safe_load(fm_text) or {}, body, fm_text
            except yaml.YAMLError:
                return None, body, fm_text
    return {}, text, ""


def is_core_course_doc(fm: dict):
    course = str(fm.get("course", ""))
    return any(p in course for p in COURSE_PATTERNS)


def fix_stacks_search_url(url: str):
    if not url.startswith("https://stacks.math.columbia.edu/search?query="):
        return url
    # 提取原始 query 值（已编码）
    m = re.search(r"query=([^&]+)", url)
    if not m:
        return url
    raw = m.group(1)
    decoded = urllib.parse.unquote(raw)
    # 如果解码后仍含中文字符，尝试映射；否则保留
    if any("\u4e00" <= ch <= "\u9fff" for ch in decoded):
        for cn, en in STACKS_QUERY_MAP.items():
            if cn in raw or urllib.parse.unquote(cn) in decoded:
                return f"https://stacks.math.columbia.edu/search?query={en}"
    return url


def fix_doc(path: Path):
    text = path.read_text(encoding="utf-8", errors="ignore")
    fm, body, fm_text = parse_frontmatter(text)
    if fm is None:
        return False
    changed = False

    # 1) MIT 18.06 旧 exam PDF 路径 → resources 路径（含 /mathematics/ 旧路径）
    pdf_pattern = re.compile(
        r"https://ocw\.mit\.edu/courses(?:/mathematics)?/18-06-linear-algebra-spring-2010/exams/(MIT18_06S10_exam2_s10_sol\.pdf)"
    )
    new_pdf = r"https://ocw.mit.edu/courses/18-06-linear-algebra-spring-2010/resources/\1"
    new_text = pdf_pattern.sub(new_pdf, text)
    if new_text != text:
        text = new_text
        changed = True

    # 2) Stacks 中文搜索 URL → 英文搜索 URL（仅核心课程文档）
    if is_core_course_doc(fm):
        ext = fm.get("external_ids") or {}
        key = "stacks_search_url"
        if key in ext and isinstance(ext[key], str):
            new_url = fix_stacks_search_url(ext[key])
            if new_url != ext[key]:
                ext[key] = new_url
                fm["external_ids"] = ext
                changed = True
        # body 中也替换
        new_body = body
        for cn, en in STACKS_QUERY_MAP.items():
            # 替换已编码的中文 query 字符串
            new_body = new_body.replace(cn, en)
        if new_body != body:
            body = new_body
            changed = True

    if not changed:
        return False

    new_text = (
        "---\n"
        + yaml.safe_dump(fm, allow_unicode=True, sort_keys=False, default_flow_style=False)
        + "---\n"
        + body
    )
    path.write_text(new_text, encoding="utf-8")
    return True


def main():
    changed = 0
    for path in PROJECT_ROOT.rglob("*.md"):
        if ".git" in path.parts:
            continue
        if fix_doc(path):
            changed += 1
    print(f"Fixed remaining link timeouts in {changed} docs.")


if __name__ == "__main__":
    main()
