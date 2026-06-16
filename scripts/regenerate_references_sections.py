#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
重新生成银层文档正文中的「参考与延伸阅读」节，使其与 frontmatter 同步。

用法：
    python scripts/regenerate_references_sections.py
"""

import yaml
import re
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]


def parse_frontmatter(text: str):
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


def format_textbook(tb: dict):
    title = tb.get("title", "")
    author = tb.get("author") or ", ".join(tb.get("authors", []))
    edition = tb.get("edition", "")
    publisher = tb.get("publisher", "")
    year = tb.get("year", "")
    isbn = tb.get("isbn", "")
    mr = tb.get("mr_number", "")
    chapters = tb.get("chapters", "")
    pages = tb.get("pages", "")
    url = tb.get("url", "")

    parts = []
    if author:
        parts.append(author)
    if title:
        parts.append(f"*{title}*")
    if edition:
        parts.append(f"{edition} ed.")
    if publisher:
        parts.append(publisher)
    if year:
        parts.append(str(year))
    line = ", ".join(parts)
    detail = []
    if chapters:
        detail.append(f"Chapters: {chapters}")
    if pages:
        detail.append(f"Pages: {pages}")
    if isbn:
        detail.append(f"ISBN: {isbn}")
    if mr:
        detail.append(f"MR: {mr}")
    if detail:
        line += " (" + "; ".join(detail) + ")"
    if url:
        line += f" [{url}]({url})"
    return f"- {line}"


def format_database(db: dict):
    name = db.get("name", db.get("id", ""))
    url = db.get("entry_url", db.get("url", ""))
    if url:
        return f"- [{name}]({url})"
    return f"- {name}"


def format_paper(paper: dict):
    title = paper.get("title", "")
    author = paper.get("author") or ", ".join(paper.get("authors", []))
    year = paper.get("year", "")
    journal = paper.get("journal", "")
    doi = paper.get("doi", "")
    arxiv = paper.get("arxiv_id", "")
    url = paper.get("url", "")

    parts = []
    if author:
        parts.append(author)
    if title:
        parts.append(f"*{title}*")
    if journal:
        parts.append(journal)
    if year:
        parts.append(str(year))
    line = ", ".join(parts)
    detail = []
    if doi:
        detail.append(f"DOI: {doi}")
    if arxiv:
        detail.append(f"arXiv: {arxiv}")
    if detail:
        line += " (" + "; ".join(detail) + ")"
    if url:
        line += f" [{url}]({url})"
    return f"- {line}"


def format_external_ids(external_ids: dict):
    lines = []
    for key, url in external_ids.items():
        if not url:
            continue
        key_label = key.replace("_", " ").title()
        lines.append(f"- [{key_label}]({url})")
    return lines


def build_references_section(fm: dict):
    refs = fm.get("references") or {}
    external_ids = fm.get("external_ids") or {}
    lines = ["", "---", "", "## 参考与延伸阅读", ""]

    textbooks = refs.get("textbooks") or []
    if textbooks:
        lines.append("### 教材")
        lines.append("")
        for tb in textbooks:
            lines.append(format_textbook(tb))
        lines.append("")

    papers = refs.get("papers") or []
    if papers:
        lines.append("### 经典论文与原始文献")
        lines.append("")
        for paper in papers:
            lines.append(format_paper(paper))
        lines.append("")

    databases = refs.get("databases") or []
    if databases:
        lines.append("### 数据库与网络资源")
        lines.append("")
        for db in databases:
            lines.append(format_database(db))
        lines.append("")

    ext_lines = format_external_ids(external_ids)
    if ext_lines:
        lines.append("### 课程与外部链接")
        lines.append("")
        lines.extend(ext_lines)
        lines.append("")

    if len(lines) <= 5:
        return None
    return "\n".join(lines)


def process_file(path: Path):
    text = path.read_text(encoding="utf-8", errors="ignore")
    fm, body = parse_frontmatter(text)
    if fm is None or fm.get("level") != "silver":
        return False

    section = build_references_section(fm)
    if not section:
        return False

    # 如果正文中已存在「参考与延伸阅读」节，替换之
    marker = r"\n---\n\n## 参考与延伸阅读\n"
    if re.search(marker, body):
        body = re.split(marker, body, maxsplit=1)[0]
        body = body.rstrip() + section
        changed = True
    else:
        return False

    new_text = (
        "---\n"
        + yaml.safe_dump(fm, allow_unicode=True, sort_keys=False, default_flow_style=False)
        + "---\n"
        + body
    )
    path.write_text(new_text, encoding="utf-8")
    return changed


def main():
    changed = 0
    for p in PROJECT_ROOT.rglob("*.md"):
        if any(x in p.parts for x in ("node_modules", ".git", "00-归档", "归档")):
            continue
        if process_file(p):
            changed += 1
    print(f"Regenerated references sections in {changed} silver docs.")


if __name__ == "__main__":
    main()
