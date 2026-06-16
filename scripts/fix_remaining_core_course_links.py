#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
修复核心课程链接校验报告中的已知可修复问题。
"""

import re
import yaml
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]
COURSE_PATTERNS = ["18.100A", "18.701", "18.06", "232br", "Stanford FOAG"]


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


def remove_nlab_url(fm: dict, bad_url: str):
    ext = fm.get("external_ids") or {}
    if ext.get("nlab_url") == bad_url:
        del ext["nlab_url"]
    refs = fm.get("references") or {}
    databases = refs.get("databases") or []
    new_dbs = [db for db in databases if db.get("entry_url") != bad_url]
    if len(new_dbs) != len(databases):
        refs["databases"] = new_dbs
    if not refs.get("databases"):
        refs.pop("databases", None)
    if refs:
        fm["references"] = refs
    elif "references" in fm:
        del fm["references"]


def fix_doc(path: Path):
    text = path.read_text(encoding="utf-8", errors="ignore")
    fm, body, fm_text = parse_frontmatter(text)
    if fm is None:
        return False
    if not is_core_course_doc(fm):
        # 仍然全局修复 Lagrange nLab 链接
        new_text = text.replace(
            "https://ncatlab.org/nlab/show/Lagrange+theorem",
            "https://ncatlab.org/nlab/show/Lagrange%27s+theorem",
        )
        if new_text != text:
            path.write_text(new_text, encoding="utf-8")
            return True
        return False

    fm_changed = False

    # 1) MIT 18.701 Fall 2020 -> Fall 2010
    old_mit = "https://ocw.mit.edu/courses/18-701-algebra-i-fall-2020/"
    new_mit = "https://ocw.mit.edu/courses/18-701-algebra-i-fall-2010/"
    if old_mit in text:
        text = text.replace(old_mit, new_mit)
        fm_changed = True

    # 2) Lagrange theorem nLab 精确化
    if "https://ncatlab.org/nlab/show/Lagrange+theorem" in text:
        text = text.replace(
            "https://ncatlab.org/nlab/show/Lagrange+theorem",
            "https://ncatlab.org/nlab/show/Lagrange%27s+theorem",
        )
        fm_changed = True

    # 3) Serre+theorem nLab 不存在，从 frontmatter 移除
    bad_serre = "https://ncatlab.org/nlab/show/Serre+theorem"
    if bad_serre in text:
        # 重新解析可能被修改过的文本
        fm2, body2, fm_text2 = parse_frontmatter(text)
        if fm2 is not None:
            remove_nlab_url(fm2, bad_serre)
            text = "---\n" + yaml.safe_dump(fm2, allow_unicode=True, sort_keys=False, default_flow_style=False) + "---\n" + body2.replace(bad_serre, "")
            fm_changed = True
        else:
            text = text.replace(bad_serre, "")
            fm_changed = True

    if not fm_changed:
        return False
    path.write_text(text, encoding="utf-8")
    return True


def main():
    changed = 0
    for path in PROJECT_ROOT.rglob("*.md"):
        if ".git" in path.parts:
            continue
        if fix_doc(path):
            changed += 1
    print(f"Fixed remaining core course links in {changed} docs.")


if __name__ == "__main__":
    main()
