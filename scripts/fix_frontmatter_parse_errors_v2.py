#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
修复剩余顽固 frontmatter YAML 解析错误。

主要处理：
1. references 列表中插入了独立的 msc_primary 行，导致列表项被破坏。
2. 存在两个 frontmatter（中间夹带 BOM / 零宽字符）。
3. msc_primary 后接列表但缺少 msc_secondary 键。
4. processed_at 等字段的引号嵌套/断裂。
5. 双引号字符串内部嵌套双引号。
"""

import yaml
import re
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]

BOM_RE = re.compile(r"^[\ufeff\u200b\u2060\ufe00-\ufe0f]*")


def infer_title(path: Path):
    base = path.stem
    base = re.sub(r"^(ANA|TOP|GEO|AG|EX|ETH)-\d+[-_]", "", base)
    base = re.sub(r"^Ch\d+[-_]", "", base)
    base = base.replace("-", " ").replace("_", " ")
    return base.strip()


def sanitize_placeholders(fm_text: str):
    """清理 frontmatter 中的占位标量（@、~ 等）和 msc_secondary 中的空列表项。"""
    # msc_primary: @ -> 空字符串
    fm_text = re.sub(r"^(msc_primary:\s*)@\s*$", r'\1""', fm_text, flags=re.MULTILINE)
    # msc: @ -> 空字符串
    fm_text = re.sub(r"^(\s+msc:\s*)@\s*$", r'\1""', fm_text, flags=re.MULTILINE)
    # 删除 msc_secondary 列表中独立的 '- @' 行
    fm_text = re.sub(r"^\s*- @\s*\n", "", fm_text, flags=re.MULTILINE)
    # 如果 msc_secondary: 后紧跟空行，则设为空列表
    fm_text = re.sub(
        r"^(msc_secondary:\s*)\n(?=\n|[^ -])",
        r"\1 []\n",
        fm_text,
        flags=re.MULTILINE,
    )
    return fm_text


def fix_unquoted_colons(fm_text: str):
    """为未加引号且含 ':' 的标量字段值补双引号。"""
    scalar_keys = (
        "title|description|edition|author|name|publisher|entry_url|chapter|chapters|subtitle|"
        "type|isbn|doi|arxiv_id|mr_number|zb_id"
    )
    pattern = re.compile(r"^(\s*(?:" + scalar_keys + r"):\s+)(.+)$")
    new_lines = []
    for line in fm_text.splitlines():
        m = pattern.match(line)
        if m:
            prefix, val = m.group(1), m.group(2)
            # 已加引号不再处理
            if (val.startswith('"') and val.endswith('"')) or (
                val.startswith("'") and val.endswith("'")
            ):
                new_lines.append(line)
                continue
            # 值含 ':' 或占位标量时加引号
            if ":" in val or val.strip() in ("@", "~"):
                if '"' in val:
                    # 含双引号改用单引号，内部单引号转义
                    val = "'" + val.replace("'", "''") + "'"
                else:
                    val = '"' + val + '"'
                line = prefix + val
        new_lines.append(line)
    return "\n".join(new_lines)


def fix_nested_quotes_in_line(line: str):
    # 修复形如 description: "..."..."" 的嵌套双引号
    m = re.match(r'^(\s*[\w_]+:\s+")(.+?)"\s*$', line)
    if m:
        prefix, content = m.group(1), m.group(2)
        # 若内容中还有未转义的双引号，替换为单引号
        if '"' in content:
            content = content.replace('"', "'")
            return f'{prefix}{content}"'
    return line


def fix_processed_at(line: str):
    # 修复 processed_at: '2026'-04-05'  -> processed_at: '2026-04-05'
    return re.sub(
        r"^(\s*processed_at:\s*)'?(\d{4})'-(\d{2})-(\d{2})'?\s*$",
        r"\1'\2-\3-\4'",
        line,
    )


def extract_msc_primary_from_broken_references(fm_text: str):
    """
    当 msc_primary 被错误插入到 references 列表项中时，
    返回 (cleaned_text, msc_primary_value)。
    """
    lines = fm_text.splitlines()
    value = None
    cleaned = []
    in_references = False
    for line in lines:
        if re.match(r"^msc_primary:\s*", line) and in_references:
            m = re.match(r"^msc_primary:\s*(.+)", line)
            if m:
                value = m.group(1).strip()
            continue
        if line.startswith("references:"):
            in_references = True
        elif in_references and not line.startswith(" ") and line.strip() != "":
            in_references = False
        cleaned.append(line)
    return "\n".join(cleaned), value


def fix_msc_primary_missing_secondary(fm_text: str):
    """
    修复：
        msc_primary: 18

          - 18N60
    变为：
        msc_primary: 18
        msc_secondary:
          - 18N60
    """
    pattern = re.compile(
        r"^(msc_primary:\s*[^\n]+?)\n\n(\s*- \d+[A-Z]\d+(?:,\s*\d+[A-Z]\d+)*\n)+",
        re.MULTILINE,
    )

    def repl(m):
        head = m.group(1)
        lines = m.group(0)[len(head) :].strip("\n").splitlines()
        # 计算列表项的缩进
        indent = len(lines[0]) - len(lines[0].lstrip())
        list_block = "\n".join(lines)
        return f"{head}\nmsc_secondary:\n{list_block}\n"

    return pattern.sub(repl, fm_text)


def try_parse(fm_text: str):
    try:
        return yaml.safe_load(fm_text)
    except yaml.YAMLError:
        return None


def fix_single_frontmatter(fm_text: str, path: Path):
    changed = False

    # 移除 references 中插错的 msc_primary 行
    cleaned, msc_value = extract_msc_primary_from_broken_references(fm_text)
    if msc_value is not None:
        fm_text = cleaned
        if "msc_primary:" not in fm_text.split("references:")[0]:
            title = infer_title(path)
            fm_text = f"title: {title}\nmsc_primary: {msc_value}\n" + fm_text
            changed = True

    # 修复 msc_primary 后接列表
    new_text = fix_msc_primary_missing_secondary(fm_text)
    if new_text != fm_text:
        fm_text = new_text
        changed = True

    # 修复引号
    lines = fm_text.splitlines()
    new_lines = []
    for line in lines:
        line = fix_processed_at(line)
        line = fix_nested_quotes_in_line(line)
        new_lines.append(line)
    fm_text2 = "\n".join(new_lines)
    if fm_text2 != fm_text:
        fm_text = fm_text2
        changed = True

    # 为含冒号但未加引号的标量字段加引号
    fm_text3 = fix_unquoted_colons(fm_text)
    if fm_text3 != fm_text:
        fm_text = fm_text3
        changed = True

    return fm_text, changed


def merge_references(base_fm: dict, refs_fm: dict):
    """将 refs_fm 的 references 合并到 base_fm，优先保留 base_fm 已有内容。"""
    base_refs = base_fm.get("references") or {}
    extra_refs = refs_fm.get("references") or {}
    if not base_refs and extra_refs:
        base_fm["references"] = extra_refs
        return
    # 都有的情况下按类型合并去重
    for key, items in extra_refs.items():
        if not items:
            continue
        existing = base_refs.get(key) or []
        seen = set()
        merged = []
        for it in existing + items:
            # 用 title 或 id 去重
            sig = it.get("id") or it.get("title") or str(it)
            if sig not in seen:
                seen.add(sig)
                merged.append(it)
        base_refs[key] = merged
    base_fm["references"] = base_refs


def fix_file(path: Path):
    text = path.read_text(encoding="utf-8", errors="ignore")
    if not text.startswith("---"):
        return False

    first_end = text.find("---", 3)
    if first_end == -1:
        return False

    first_block = text[3:first_end].strip()
    after_first = text[first_end + 3 :]
    # 去除可能存在的 BOM / 零宽字符后，看是否紧跟另一个 frontmatter
    stripped_after = BOM_RE.sub("", after_first)

    # 判断是否为真正的第二个 frontmatter：以 --- 开头且随后是 YAML 行
    second_block = None
    # 去除前导换行 / 空白 / BOM
    after_first_stripped = after_first.lstrip("\n\r\t ")
    after_first_stripped = BOM_RE.sub("", after_first_stripped)
    if after_first_stripped.startswith("---"):
        # 在原始文本中定位第二个 frontmatter 区间
        second_start = text.find("---", first_end + 3)
        second_end = text.find("---", second_start + 3)
        if second_start != -1 and second_end != -1:
            candidate = text[second_start + 3 : second_end].strip()
            # 第二个 block 必须包含 title 或 msc_primary 等键，才认为是有效 frontmatter
            if re.search(r"^(title|msc_primary|level|tags):", candidate, re.MULTILINE):
                second_block = candidate
                body = text[second_end + 3 :]
                body = BOM_RE.sub("", body)

    if second_block is not None:
        # 先修复并解析第二个 frontmatter
        second_fixed, _ = fix_single_frontmatter(second_block, path)
        second_fixed = sanitize_placeholders(second_fixed)
        second_parsed = try_parse(second_fixed)
        if second_parsed is None:
            return False

        # 尝试从第一个 frontmatter 提取可用的 references
        first_fixed, _ = fix_single_frontmatter(first_block, path)
        first_fixed = sanitize_placeholders(first_fixed)
        first_parsed = try_parse(first_fixed)
        if first_parsed:
            merge_references(second_parsed, first_parsed)

        fm = second_parsed
    else:
        # 单一 frontmatter
        fixed, _ = fix_single_frontmatter(first_block, path)
        fixed = sanitize_placeholders(fixed)
        fm = try_parse(fixed)
        if fm is None:
            return False
        body = after_first

    if not isinstance(fm, dict):
        return False

    if not fm.get("title"):
        fm["title"] = infer_title(path)

    # 若 msc_primary 为空但 msc_secondary 有值，用第一个非空 secondary 填充
    msc_primary = fm.get("msc_primary")
    msc_secondary = fm.get("msc_secondary") or []
    if (not msc_primary or str(msc_primary).strip() in ("", "@")) and isinstance(msc_secondary, list) and msc_secondary:
        first_valid = next((str(x).strip() for x in msc_secondary if str(x).strip() not in ("", "@")), None)
        if first_valid:
            fm["msc_primary"] = first_valid

    # 重新序列化
    new_fm_text = yaml.safe_dump(fm, allow_unicode=True, sort_keys=False, default_flow_style=False)
    new_text = "---\n" + new_fm_text + "---\n" + body.lstrip("\n")

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
        if not text.startswith("---"):
            continue
        first_end = text.find("---", 3)
        if first_end == -1:
            continue
        fm = text[3:first_end].strip()
        try:
            yaml.safe_load(fm)
            # 解析正常但可能缺 title，已在 v1 处理；这里跳过
            continue
        except yaml.YAMLError:
            pass

        if fix_file(p):
            fixed += 1
        else:
            still_broken.append(str(p.relative_to(PROJECT_ROOT)))

    print(f"Fixed {fixed} files.")
    print(f"Still broken: {len(still_broken)}")
    for f in still_broken[:30]:
        print(f"  {f}")


if __name__ == "__main__":
    main()
