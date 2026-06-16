#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
修复 MacTutor 传记链接中的特殊歧义姓氏（Noether / von Neumann / Scholze 等）。

覆盖范围：全库 Markdown（包括 frontmatter 与正文）。
"""

import re
import yaml
import urllib.parse
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed

PROJECT_ROOT = Path(__file__).resolve().parents[1]
WIKI_RE = re.compile(r"https?://en\.wikipedia\.org/wiki/([^/#?\s]+)")

# 特殊映射：(当前 URL 中的 ID, 判断 Wikipedia 标题包含, 新 ID)
# 若 new_id 为 None，表示需要移除/替换为 Wikipedia
SPECIAL_CASES = [
    ("Noether", "Emmy_Noether", "Noether_Emmy"),
    ("von-Neumann", "John_von_Neumann", "Von_Neumann"),
]

# Scholze 在 MacTutor 暂无条目，直接替换为 Wikipedia
SCHOLZE_WIKI = "https://en.wikipedia.org/wiki/Peter_Scholze"


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


def fix_doc(path: Path):
    text = path.read_text(encoding="utf-8", errors="ignore")
    fm, body, fm_text = parse_frontmatter(text)
    if fm is None:
        return False
    changed = False

    ext = fm.get("external_ids") or {}
    wiki_url = ext.get("wikipedia_url")
    wiki_title = ""
    if wiki_url:
        m = WIKI_RE.search(wiki_url)
        if m:
            wiki_title = m.group(1)

    mac_url = ext.get("mactutor_url")
    if mac_url:
        mac_id = mac_url.rstrip("/").split("/")[-1]
        # Scholze 特例：MacTutor 无条目，替换为 Wikipedia
        if mac_id == "Scholze":
            ext["mactutor_url"] = SCHOLZE_WIKI
            fm["external_ids"] = ext
            refs = fm.get("references") or {}
            dbs = refs.get("databases") or []
            for db in dbs:
                if db.get("id") == "mactutor":
                    db["entry_url"] = SCHOLZE_WIKI
                    db["name"] = "Wikipedia (MacTutor 暂无条目)"
                    db["id"] = "wikipedia"
                    break
            refs["databases"] = dbs
            fm["references"] = refs
            changed = True
        else:
            title = str(fm.get("title", ""))
            for cur_id, wiki_marker, new_id in SPECIAL_CASES:
                if mac_id != cur_id:
                    continue
                # 直接匹配 Wikipedia 标题
                matched = wiki_marker in wiki_title
                # Noether 特例：概念/定理文档常以 Emmy Noether 命名，但 wiki_url 可能是概念页
                if not matched and cur_id == "Noether":
                    matched = (
                        "Emmy" in text
                        or "Noether" in title
                        or "诺特" in title
                        or "诺特" in text[:2000]
                    )
                if matched:
                    new_url = f"https://mathshistory.st-andrews.ac.uk/Biographies/{new_id}/"
                    ext["mactutor_url"] = new_url
                    fm["external_ids"] = ext
                    refs = fm.get("references") or {}
                    dbs = refs.get("databases") or []
                    for db in dbs:
                        if db.get("id") == "mactutor":
                            db["entry_url"] = new_url
                            break
                    refs["databases"] = dbs
                    fm["references"] = refs
                    changed = True
                    break

    # 正文替换
    new_body = body
    # Noether / von-Neumann
    new_body = new_body.replace(
        "https://mathshistory.st-andrews.ac.uk/Biographies/Noether/",
        "https://mathshistory.st-andrews.ac.uk/Biographies/Noether_Emmy/",
    )
    new_body = new_body.replace(
        "https://mathshistory.st-andrews.ac.uk/Biographies/von-Neumann/",
        "https://mathshistory.st-andrews.ac.uk/Biographies/Von_Neumann/",
    )
    # Scholze 裸链接带标记
    new_body = new_body.replace(
        "https://mathshistory.st-andrews.ac.uk/Biographies/Scholze/[需更新]",
        f"[Peter Scholze - Wikipedia]({SCHOLZE_WIKI})",
    )
    if new_body != body:
        changed = True
        body = new_body

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
    skipped = {".git", "node_modules", "00-归档"}
    candidates = []
    for path in PROJECT_ROOT.rglob("*.md"):
        if any(p in path.parts for p in skipped):
            continue
        candidates.append(path)

    print(f"Scanning {len(candidates)} docs for MacTutor link fixes...")
    with ThreadPoolExecutor(max_workers=8) as executor:
        future_to_path = {executor.submit(fix_doc, p): p for p in candidates}
        for future in as_completed(future_to_path):
            path = future_to_path[future]
            try:
                if future.result():
                    changed += 1
                    print(f"  fixed {path.relative_to(PROJECT_ROOT)}")
            except Exception as e:
                print(f"  error {path}: {e}")
    print(f"Fixed MacTutor links in {changed} docs.")


if __name__ == "__main__":
    main()
