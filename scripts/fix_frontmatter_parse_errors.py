#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
自动修复常见的 Markdown frontmatter YAML 解析错误。

处理的错误模式：
1. msc_primary 后直接跟列表（缺少 msc_secondary 键）
2. msc_primary 被错误地插入到 references 列表项中间
3. msc: @ 等非法标量
4. 缺失 title 的文档从文件名推断标题
5. 双引号内嵌套双引号导致的解析错误（简单替换为单引号）

用法：
    python scripts/fix_frontmatter_parse_errors.py
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
                return yaml.safe_load(fm_text) or {}, fm_text, body
            except yaml.YAMLError as e:
                return None, fm_text, body
    return {}, "", text


def infer_title(path: Path):
    base = path.stem
    # 去除常见前缀
    base = re.sub(r"^(ANA|TOP|GEO|AG|EX|ETH)-\d+[-_]", "", base)
    base = re.sub(r"^Ch\d+[-_]", "", base)
    base = base.replace("-", " ").replace("_", " ")
    return base.strip()


def fix_msc_primary_list(fm_text: str):
    """修复 msc_primary: value 后直接跟列表的情况"""
    pattern = re.compile(
        r"^(msc_primary:\s*[^\n]+?)\n\n((?:- \d+[A-Z]\d+(?:,\s*\d+[A-Z]\d+)*\n)+)",
        re.MULTILINE,
    )
    return pattern.sub(r"\1\nmsc_secondary:\n\2", fm_text)


def fix_nested_quotes(line: str):
    """简单修复双引号字符串内嵌套双引号"""
    # 仅处理以 key: "..." 形式开头且内部有未转义双引号的行
    m = re.match(r'^(\s*[\w_]+:\s+")([^"]*"[^"]*"[^"]*)"\s*$', line)
    if m:
        prefix = m.group(1)
        content = m.group(2)
        # 将内部双引号替换为单引号
        content = content.replace('"', "'")
        return f'{prefix}{content}"'
    return line


def fix_frontmatter(path: Path):
    text = path.read_text(encoding="utf-8", errors="ignore")
    if not text.startswith("---"):
        return False

    end = text.find("---", 3)
    if end == -1:
        return False

    fm_text = text[3:end].strip()
    body = text[end + 3 :].strip()
    original_fm = fm_text

    # 1. 修复 msc_primary 后接列表
    fm_text = fix_msc_primary_list(fm_text)

    # 2. 修复 msc: @ / msc: ~ 等
    fm_text = re.sub(r"^(\s+msc:\s*)@\s*$", r'\1""', fm_text, flags=re.MULTILINE)

    # 3. 修复嵌套双引号
    fm_lines = fm_text.splitlines()
    fm_lines = [fix_nested_quotes(line) for line in fm_lines]
    fm_text = "\n".join(fm_lines)

    # 4. 处理 msc_primary 被插入到 references 列表项中间的情况
    # 策略：如果 references 块中存在独立的 msc_primary 行，则将其移到最前面
    lines = fm_text.splitlines()
    msc_primary_value = None
    msc_primary_idx = None
    in_references = False
    for idx, line in enumerate(lines):
        if line.startswith("references:"):
            in_references = True
        elif in_references and not line.startswith(" ") and line.strip() != "":
            in_references = False
        if re.match(r"^msc_primary:\s*", line) and in_references:
            m = re.match(r"^msc_primary:\s*(.+)", line)
            if m:
                msc_primary_value = m.group(1).strip()
                msc_primary_idx = idx
            break

    if msc_primary_value is not None and msc_primary_idx is not None:
        # 删除该行
        del lines[msc_primary_idx]
        fm_text = "\n".join(lines)
        # 在开头添加 title 和 msc_primary
        title = infer_title(path)
        fm_text = f"title: {title}\nmsc_primary: {msc_primary_value}\n" + fm_text

    # 5. 尝试解析，如果失败再尝试简单补 title
    try:
        fm = yaml.safe_load(fm_text)
    except yaml.YAMLError:
        # 如果还没有 title，补一个 title 试试
        if "title:" not in fm_text:
            title = infer_title(path)
            fm_text = f"title: {title}\n" + fm_text
        try:
            fm = yaml.safe_load(fm_text)
        except yaml.YAMLError:
            return False

    if fm is None:
        return False

    # 确保有 title
    if not fm.get("title"):
        fm["title"] = infer_title(path)

    # 重新序列化
    new_fm_text = yaml.safe_dump(fm, allow_unicode=True, sort_keys=False, default_flow_style=False)
    new_text = "---\n" + new_fm_text + "---\n" + body

    if new_text != text:
        path.write_text(new_text, encoding="utf-8")
        return True
    return False


def main():
    fixed = 0
    still_broken = []
    for p in PROJECT_ROOT.rglob("*.md"):
        if any(x in p.parts for x in ("node_modules", ".git")):
            continue
        text = p.read_text(encoding="utf-8", errors="ignore")
        parsed, _, _ = parse_frontmatter(text)
        if parsed is not None:
            # 即使没有解析错误，也补充缺失 title
            if not parsed.get("title"):
                if fix_frontmatter(p):
                    fixed += 1
            continue
        if fix_frontmatter(p):
            fixed += 1
        else:
            still_broken.append(str(p.relative_to(PROJECT_ROOT)))

    print(f"Fixed or improved {fixed} files.")
    if still_broken:
        print(f"Still broken: {len(still_broken)}")
        for f in still_broken[:20]:
            print(f"  {f}")


if __name__ == "__main__":
    main()
