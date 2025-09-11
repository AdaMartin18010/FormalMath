#!/usr/bin/env python3
import argparse
import os
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DOCS = ROOT / "docs"


LINK_PATTERN = re.compile(r"\[(?P<text>[^\]]+)\]\((?P<href>[^)]+)\)")


def build_filename_index(base: Path) -> dict:
    index = {}
    for dirpath, _, filenames in os.walk(base):
        for name in filenames:
            if name.lower().endswith((".md", ".yaml", ".yml")):
                key = name.strip()
                index.setdefault(key, []).append(Path(dirpath) / name)
    return index


def is_http(href: str) -> bool:
    return href.startswith("http://") or href.startswith("https://")


def split_anchor(href: str):
    if "#" in href:
        path, anchor = href.split("#", 1)
        return path, "#" + anchor
    return href, ""


def compute_rel(from_file: Path, to_file: Path) -> str:
    rel = os.path.relpath(to_file, start=from_file.parent)
    return rel.replace(os.sep, "/")


def rewrite_links_in_text(text: str, file_path: Path, fname_index: dict):
    changes = []

    def repl(m):
        nonlocal changes
        text_label = m.group("text")
        href = m.group("href").strip()
        # 跳过外链与纯锚点
        if is_http(href) or href.startswith("#"):
            return m.group(0)

        path_part, anchor = split_anchor(href)
        # 已经是存在的相对路径则跳过
        candidate = (file_path.parent / path_part).resolve()
        if candidate.exists():
            return m.group(0)

        # 仅基于文件名在索引中查找同名文件
        filename = Path(path_part).name
        if not filename:
            return m.group(0)

        matches = fname_index.get(filename)
        if not matches:
            return m.group(0)

        # 选取最短相对路径（启发式：距离最近）
        best = min(matches, key=lambda p: len(os.path.relpath(p, start=file_path.parent)))
        new_rel = compute_rel(file_path, best) + anchor
        old = m.group(0)
        new = f"[{text_label}]({new_rel})"
        if old != new:
            changes.append((old, new))
        return new

    new_text = LINK_PATTERN.sub(repl, text)
    return new_text, changes


def iter_md_files(scope: Path):
    for dirpath, _, filenames in os.walk(scope):
        for name in filenames:
            if name.lower().endswith(".md"):
                yield Path(dirpath) / name


def main():
    parser = argparse.ArgumentParser(description="Fix relative links by rewriting to correct paths.")
    parser.add_argument("--scope", default=str(DOCS), help="Directory to scan")
    parser.add_argument("--apply", action="store_true", help="Write changes to files")
    parser.add_argument("--dry_limit", type=int, default=100, help="Limit number of files to show in dry run output")
    args = parser.parse_args()

    scope = Path(args.scope)
    fname_index = build_filename_index(scope)
    changed_files = 0
    total_changes = 0

    for i, path in enumerate(iter_md_files(scope)):
        try:
            text = path.read_text(encoding="utf-8")
        except Exception:
            continue
        new_text, changes = rewrite_links_in_text(text, path, fname_index)
        if changes:
            changed_files += 1
            total_changes += len(changes)
            if args.apply:
                path.write_text(new_text, encoding="utf-8")
            if not args.apply and i < args.dry_limit:
                print(f"FILE: {path}")
                for old, new in changes[:10]:
                    print(f"  - {old} -> {new}")

    print({
        "scope": str(scope),
        "changed_files": changed_files,
        "total_link_rewrites": total_changes,
        "applied": bool(args.apply),
    })


if __name__ == "__main__":
    main()


