#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
修复数学家文档中的 MacTutor 传记链接。

逻辑：
1. 读取已有 mactutor_url 与 wikipedia_url。
2. 若当前 MacTutor 页面 404，且 Wikipedia 标题为 "First Last"（或更多部分），
   尝试使用 "Last_First" 形式的 ID。
3. 验证新 URL 可访问后更新 frontmatter 与 references.databases。
"""

import re
import ssl
import yaml
import urllib.request
import urllib.parse
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed

PROJECT_ROOT = Path(__file__).resolve().parents[1]
MATH_DIR = PROJECT_ROOT / "数学家理念体系"
WIKI_RE = re.compile(r"https?://en\.wikipedia\.org/wiki/([^/#?\s]+)")
SSL_CTX = ssl._create_unverified_context()
HEADERS = {"User-Agent": "Mozilla/5.0 FormalMath-MacTutor-Fix/1.0"}


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


def fetch_code(url: str, method: str = "HEAD", timeout: int = 6):
    try:
        req = urllib.request.Request(url, method=method, headers=HEADERS)
        with urllib.request.urlopen(req, timeout=timeout, context=SSL_CTX) as resp:
            return resp.getcode()
    except urllib.error.HTTPError as e:
        return e.code
    except Exception as e:
        return str(e)[:80]


def derive_alt_id(wiki_title: str, current_id: str):
    """若当前 ID 仅为姓氏，尝试 Last_First。"""
    parts = wiki_title.replace("_", " ").split()
    if len(parts) < 2:
        return None
    # 去除括号注释
    parts = [p for p in parts if not p.startswith("(")]
    if len(parts) < 2:
        return None
    first = parts[0]
    last = parts[-1]
    if current_id != last:
        return None
    return f"{last}_{first}"


def fix_doc(path: Path):
    text = path.read_text(encoding="utf-8", errors="ignore")
    fm, body = parse_frontmatter(text)
    if fm is None:
        return False
    ext = fm.get("external_ids") or {}
    mac_url = ext.get("mactutor_url")
    wiki_url = ext.get("wikipedia_url")
    if not mac_url or not wiki_url:
        return False

    m = WIKI_RE.search(wiki_url)
    if not m:
        return False
    wiki_title = urllib.parse.unquote(m.group(1))

    current_id = mac_url.rstrip("/").split("/")[-1]
    alt_id = derive_alt_id(wiki_title, current_id)
    if not alt_id:
        return False

    alt_url = f"https://mathshistory.st-andrews.ac.uk/Biographies/{alt_id}/"
    # 先快速 HEAD 验证当前是否 404（或不可访问），且新 URL 可用
    if fetch_code(mac_url, "HEAD", 5) != 404:
        return False
    if fetch_code(alt_url, "GET", 6) != 200:
        return False

    ext["mactutor_url"] = alt_url
    fm["external_ids"] = ext

    refs = fm.get("references") or {}
    databases = refs.get("databases") or []
    for db in databases:
        if db.get("id") == "mactutor":
            db["entry_url"] = alt_url
            break
    refs["databases"] = databases
    fm["references"] = refs

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
    skipped = {"00-归档", "00-归档-2026年4月-其他数学家"}
    candidates = []
    for path in MATH_DIR.rglob("*.md"):
        if any(p in path.parts for p in skipped):
            continue
        candidates.append(path)

    print(f"Checking {len(candidates)} mathematician docs for broken MacTutor links...")
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
