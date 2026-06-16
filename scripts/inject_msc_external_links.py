#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
为所有含 msc_primary 的数学文档注入 AMS MSC 分类外部链接。

用法：
    python scripts/inject_msc_external_links.py
"""

import re
import yaml
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]

REPORT_MARKERS = ["报告", "进度", "日报", "总结", "计划", "索引", "README", "FAQ", "指南", "模板", "清单"]


def parse_frontmatter(text: str):
    if text.startswith("---"):
        end = text.find("---", 3)
        if end != -1:
            fm_text = text[3:end].strip()
            body = text[end + 3 :].lstrip("\n")
            try:
                return yaml.safe_load(fm_text) or {}, body
            except yaml.YAMLError:
                return None, body
    return {}, text


def first_msc_code(msc):
    """从 msc_primary 中提取第一个具体的 5 位 MSC 代码（如 14A15），否则返回两位大类（如 14）。"""
    if msc is None:
        return None
    text = str(msc)
    # 先尝试完整代码
    m = re.search(r"\b(\d{2}[A-Z]\d{2})\b", text)
    if m:
        return m.group(1)
    # 再尝试大类+一位字母
    m = re.search(r"\b(\d{2}[A-Z])\b", text)
    if m:
        return m.group(1)
    # 最后尝试两位大类
    m = re.search(r"\b(\d{2})\b", text)
    if m:
        return m.group(1)
    return None


def is_report_like(title: str, stem: str):
    if stem.startswith("00-"):
        return True
    if any(m in title or m in stem for m in REPORT_MARKERS):
        return True
    return False


def main():
    changed = 0
    for p in PROJECT_ROOT.rglob("*.md"):
        if any(x in p.parts for x in ("node_modules", ".git", "00-归档", "归档")):
            continue
        text = p.read_text(encoding="utf-8", errors="ignore")
        fm, body = parse_frontmatter(text)
        if fm is None:
            continue
        level = str(fm.get("level", "")).lower()
        if level in ("meta", "l0", "project"):
            continue
        title = str(fm.get("title", ""))
        stem = p.stem
        if is_report_like(title, stem):
            continue

        msc = fm.get("msc_primary")
        code = first_msc_code(msc)
        if not code:
            continue

        external_ids = fm.get("external_ids") or {}
        key = "msc_classification_url"
        if external_ids.get(key):
            continue

        url = f"https://mathscinet.ams.org/mathscinet/search/mscdoc.html?code={code}"
        external_ids[key] = url
        fm["external_ids"] = external_ids

        new_text = (
            "---\n"
            + yaml.safe_dump(fm, allow_unicode=True, sort_keys=False, default_flow_style=False)
            + "---\n"
            + body
        )
        p.write_text(new_text, encoding="utf-8")
        changed += 1

    print(f"Injected MSC classification links into {changed} docs.")


if __name__ == "__main__":
    main()
