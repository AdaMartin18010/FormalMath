#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
batch_add_references.py
批量为 Markdown 文件添加或更新 references YAML frontmatter 字段。
仅使用 Python 标准库，无外部依赖。
"""

import argparse
import json
import os
import sys
from pathlib import Path


def to_yaml(obj, indent=0):
    """将简单 Python 对象序列化为 YAML 字符串（基础实现）。"""
    prefix = "  " * indent
    if obj is None:
        return "~"
    if isinstance(obj, bool):
        return "true" if obj else "false"
    if isinstance(obj, (int, float)):
        return str(obj)
    if isinstance(obj, str):
        # 若包含特殊字符，则加双引号并转义
        if any(c in obj for c in [':', '#', '\n', '"', "'", '[', ']', '{', '}', ',', '&', '*', '!', '|', '>', '%', '@', '`']):
            escaped = obj.replace('\\', '\\\\').replace('"', '\\"')
            return f'"{escaped}"'
        if obj.startswith('- ') or obj.startswith('---'):
            return f'"{obj}"'
        return obj
    if isinstance(obj, list):
        if not obj:
            return "[]"
        lines = []
        for item in obj:
            if isinstance(item, dict):
                first_key = True
                for k, v in item.items():
                    val_yaml = to_yaml(v, indent + 1)
                    if isinstance(v, (list, dict)) and v:
                        if first_key:
                            lines.append(prefix + "- " + k + ":")
                            first_key = False
                        else:
                            lines.append(prefix + "  " + k + ":")
                        lines.append(val_yaml)
                    else:
                        val_stripped = val_yaml.lstrip()
                        if first_key:
                            lines.append(prefix + "- " + k + ": " + val_stripped)
                            first_key = False
                        else:
                            lines.append(prefix + "  " + k + ": " + val_stripped)
            else:
                lines.append(prefix + "- " + to_yaml(item, indent + 1))
        return "\n".join(lines)
    if isinstance(obj, dict):
        if not obj:
            return "{}"
        lines = []
        for k, v in obj.items():
            val_yaml = to_yaml(v, indent + 1)
            if isinstance(v, (list, dict)) and v:
                lines.append(prefix + k + ":")
                lines.append(val_yaml)
            else:
                lines.append(prefix + k + ": " + val_yaml.lstrip())
        return "\n".join(lines)
    return str(obj)


def extract_frontmatter(text):
    """
    提取第一个 frontmatter 块。
    返回 (frontmatter, rest)；若无 frontmatter 则返回 (None, text)。
    """
    if not text.startswith('---'):
        return None, text
    end = text.find('\n---', 3)
    if end == -1:
        return None, text
    fm = text[:end + 4]  # 包含末尾的 \n---
    rest = text[end + 4:]
    return fm, rest


def has_references(frontmatter):
    """检查 frontmatter 中是否已包含 references 字段。"""
    return '\nreferences:' in frontmatter


def build_references_yamls(config, inject_keys):
    """
    根据配置文件和注入 key 列表，生成合并后的 references 子树。
    返回一个 dict：{ 'textbooks': [...], 'papers': [...], 'databases': [...] }
    """
    merged = {}
    snippets = config.get("snippets", {})
    for key in inject_keys:
        key = key.strip()
        if not key:
            continue
        snippet = snippets.get(key)
        if snippet is None:
            print(f"[警告] 配置文件中未找到 snippet key: {key}", file=sys.stderr)
            continue
        if not isinstance(snippet, dict):
            print(f"[警告] snippet key '{key}' 的值不是字典，已跳过", file=sys.stderr)
            continue
        for category, items in snippet.items():
            if not isinstance(items, list):
                continue
            merged.setdefault(category, []).extend(items)
    return merged


def make_empty_references():
    return {
        "textbooks": [],
        "papers": [],
        "databases": []
    }


def inject_references(frontmatter, refs_yaml_str):
    """
    在 frontmatter 的最后一个 \n--- 之前插入 references YAML 字符串。
    """
    end_pos = frontmatter.rfind('\n---')
    if end_pos == -1:
        # 防御性处理：若找不到结束标记，则直接追加
        return frontmatter + "\n" + refs_yaml_str
    before = frontmatter[:end_pos + 1]  # 保留换行
    after = frontmatter[end_pos + 1:]    # ---
    if not refs_yaml_str.endswith('\n'):
        refs_yaml_str += '\n'
    return before + refs_yaml_str + after


def process_file(file_path, refs_dict, dry_run=False, skip_existing=True):
    """
    处理单个 Markdown 文件。
    返回状态字符串：'skipped_existing' | 'added' | 'no_frontmatter' | 'written'
    """
    text = file_path.read_text(encoding='utf-8')
    fm, rest = extract_frontmatter(text)

    if fm is None:
        # 没有 frontmatter：在文件开头新建一个包含 references 的 frontmatter
        refs_yaml = "references:\n" + to_yaml(refs_dict, indent=1)
        new_text = f"---\n{refs_yaml}\n---\n{rest}"
        if not dry_run:
            file_path.write_text(new_text, encoding='utf-8')
        return "added"

    if skip_existing and has_references(fm):
        return "skipped_existing"

    refs_yaml = "references:\n" + to_yaml(refs_dict, indent=1)
    new_fm = inject_references(fm, refs_yaml)
    new_text = new_fm + rest
    if not dry_run:
        file_path.write_text(new_text, encoding='utf-8')
    return "written"


def main():
    parser = argparse.ArgumentParser(
        description="批量为 Markdown 文件添加或更新 references YAML frontmatter 字段。"
    )
    parser.add_argument("--dir", type=str, help="目标目录（递归处理 .md 文件）")
    parser.add_argument("--file", type=str, help="单个目标 Markdown 文件")
    parser.add_argument(
        "--config", type=str, default="scripts/reference_templates.yaml",
        help="模板配置文件路径（默认: scripts/reference_templates.yaml）"
    )
    parser.add_argument(
        "--inject", type=str,
        help="要注入的模板 key，逗号分隔，如 rudin_pma,nlab"
    )
    parser.add_argument(
        "--all", action="store_true",
        help="为所有缺失 references 的文件注入空 references 模板"
    )
    parser.add_argument(
        "--dry-run", action="store_true",
        help="仅预览，不实际修改文件"
    )
    parser.add_argument(
        "--force", action="store_true",
        help="即使已存在 references 字段也覆盖（默认跳过）"
    )

    args = parser.parse_args()

    if not args.dir and not args.file:
        parser.error("必须提供 --dir 或 --file 之一")

    if args.inject:
        inject_keys = [k.strip() for k in args.inject.split(",")]
    else:
        inject_keys = []

    if not inject_keys and not args.all:
        parser.error("必须提供 --inject 或 --all 之一")

    # 读取配置文件
    config_path = Path(args.config)
    if not config_path.exists():
        print(f"[错误] 配置文件不存在: {config_path}", file=sys.stderr)
        sys.exit(1)
    try:
        with config_path.open("r", encoding="utf-8") as f:
            raw_lines = f.readlines()
        # 过滤 YAML 风格的注释行（以 # 开头）以及纯空白行
        filtered = "".join(
            line for line in raw_lines
            if not (line.strip().startswith("#") or line.strip() == "")
        )
        config = json.loads(filtered)
    except json.JSONDecodeError as e:
        print(f"[错误] 配置文件 JSON 解析失败: {e}", file=sys.stderr)
        sys.exit(1)

    # 构建 references 字典
    if inject_keys:
        refs_dict = build_references_yamls(config, inject_keys)
    else:
        refs_dict = make_empty_references()

    # 收集目标文件
    target_files = []
    if args.file:
        target_files.append(Path(args.file))
    else:
        target_dir = Path(args.dir)
        if not target_dir.exists():
            print(f"[错误] 目录不存在: {target_dir}", file=sys.stderr)
            sys.exit(1)
        for p in target_dir.rglob("*.md"):
            target_files.append(p)

    skip_existing = not args.force
    stats = {
        "skipped_existing": 0,
        "added": 0,
        "written": 0,
        "no_frontmatter": 0,
    }

    mode_str = "[DRY-RUN] " if args.dry_run else ""

    cwd = Path.cwd()
    for fp in target_files:
        try:
            rel = fp.relative_to(cwd)
        except ValueError:
            rel = fp
        status = process_file(fp, refs_dict, dry_run=args.dry_run, skip_existing=skip_existing)
        stats[status] += 1
        if status == "skipped_existing":
            print(f"{mode_str}[跳过] {rel} （已存在 references）")
        elif status == "no_frontmatter":
            print(f"{mode_str}[新建] {rel} （无 frontmatter）")
        elif status in ("added", "written"):
            print(f"{mode_str}[更新] {rel}")

    print("\n--- 统计 ---")
    for k, v in stats.items():
        print(f"  {k}: {v}")


if __name__ == "__main__":
    main()
