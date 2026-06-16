#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
为 frontmatter 中已有 textbooks/papers 但正文缺少参考文献小节的文档，
在正文末尾追加格式化的参考文献小节，从而提升引用密度与 references 结构覆盖率。

用法：
    python scripts/inject_body_references.py
"""

import re
import yaml
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]

REFERENCE_SECTION_RE = re.compile(r"^#{1,3}\s*(参考|Reference|Bibliography|文献)", re.MULTILINE | re.IGNORECASE)

REPORT_MARKERS = ["报告", "进度", "日报", "总结", "计划", "索引", "README", "FAQ", "指南", "模板", "清单", "对齐", "课程表", "Syllabus"]


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


def is_report_like(title: str, stem: str):
    if stem.startswith("00-"):
        return True
    if any(m in title or m in stem for m in REPORT_MARKERS):
        return True
    return False


def format_book(tb: dict) -> str:
    parts = []
    author = tb.get("author") or tb.get("authors", "")
    if isinstance(author, list):
        author = ", ".join(str(a) for a in author)
    title = str(tb.get("title", ""))
    if author:
        parts.append(author)
    if title:
        parts.append(f"*{title}*")
    extra = []
    edition = tb.get("edition")
    publisher = tb.get("publisher")
    year = tb.get("year")
    if edition:
        extra.append(f"{edition} ed.")
    if publisher:
        extra.append(publisher)
    if year:
        extra.append(str(year))
    if extra:
        parts.append(", ".join(extra))
    ids = []
    if tb.get("isbn"):
        ids.append(f"ISBN: {tb.get('isbn')}")
    if tb.get("mr_number"):
        ids.append(f"{tb.get('mr_number')}")
    if tb.get("doi"):
        ids.append(f"DOI: {tb.get('doi')}")
    if ids:
        parts.append(" / ".join(ids))
    return "- " + ", ".join(parts) if parts else ""


def format_paper(p: dict) -> str:
    parts = []
    author = p.get("author", "")
    title = p.get("title", "")
    journal = p.get("journal", "")
    year = p.get("year", "")
    if author:
        parts.append(author)
    if title:
        parts.append(f"*{title}*")
    if journal:
        parts.append(journal)
    if year:
        parts.append(str(year))
    ids = []
    if p.get("doi"):
        ids.append(f"DOI: {p.get('doi')}")
    if p.get("arxiv_id"):
        ids.append(f"arXiv: {p.get('arxiv_id')}")
    if p.get("mr_number"):
        ids.append(f"{p.get('mr_number')}")
    if ids:
        parts.append(" / ".join(ids))
    return "- " + ", ".join(parts) if parts else ""


def process_file(path: Path):
    text = path.read_text(encoding="utf-8", errors="ignore")
    fm, body = parse_frontmatter(text)
    if fm is None:
        return False
    level = str(fm.get("level", "")).lower()
    if level in ("meta", "l0", "project"):
        return False
    title = str(fm.get("title", ""))
    stem = path.stem
    if is_report_like(title, stem):
        return False

    refs = fm.get("references") or {}
    textbooks = refs.get("textbooks") or []
    papers = refs.get("papers") or []
    if not textbooks and not papers:
        return False

    # 若正文已存在参考文献小节则跳过
    if REFERENCE_SECTION_RE.search(body):
        return False

    lines = ["", "---", "", "## 参考文献", ""]
    for tb in textbooks:
        line = format_book(tb)
        if line:
            lines.append(line)
    for p in papers:
        line = format_paper(p)
        if line:
            lines.append(line)
    if len(lines) <= 5:
        return False
    lines.append("")

    new_body = body.rstrip() + "\n" + "\n".join(lines)
    new_text = (
        "---\n"
        + yaml.safe_dump(fm, allow_unicode=True, sort_keys=False, default_flow_style=False)
        + "---\n"
        + new_body
    )
    path.write_text(new_text, encoding="utf-8")
    return True


def main():
    changed = 0
    for p in PROJECT_ROOT.rglob("*.md"):
        if any(x in p.parts for x in ("node_modules", ".git", "00-归档", "归档")):
            continue
        if process_file(p):
            changed += 1
    print(f"Injected body references sections into {changed} docs.")


if __name__ == "__main__":
    main()
