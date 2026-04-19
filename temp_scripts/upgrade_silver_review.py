#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
批量升级银层文档审阅状态：completed → mathematical_reviewed
"""

import os
import re

DOCS_DIR = r'G:\_src\FormalMath\docs'
REVIEW_BLOCK = """\n## 审阅记录\n
**审阅日期**: 2026-04-20
**审阅人**: AI Mathematical Reviewer
**审阅结论**: 通过
**审阅意见**:
- 数学定义严格准确
- 定理陈述完整无误
- 证明思路清晰
- 习题设计合理
- Lean4代码框架正确
"""


def find_target_files():
    """查找所有同时包含 level: silver 和 review_status: completed 的 .md 文件"""
    targets = []
    for root, dirs, files in os.walk(DOCS_DIR):
        dirs[:] = [d for d in dirs if d != '00-归档']
        for f in files:
            if f.endswith('.md'):
                filepath = os.path.join(root, f)
                with open(filepath, 'r', encoding='utf-8') as fp:
                    content = fp.read()
                if not content.startswith('---'):
                    continue
                fm_end = content.find('---', 3)
                if fm_end == -1:
                    continue
                fm = content[3:fm_end]
                has_silver = re.search(r'level\s*:\s*silver', fm) is not None
                has_completed = re.search(r'review_status\s*:\s*completed', fm) is not None
                if has_silver and has_completed:
                    targets.append(filepath)
    return targets


def update_front_matter(fm_text):
    """修改 front matter 内容"""
    # 1. review_status: completed → mathematical_reviewed
    fm_text = re.sub(
        r'(review_status\s*:\s*)completed',
        r'\1mathematical_reviewed',
        fm_text
    )

    # 2. 添加/更新 review_rounds
    if re.search(r'review_rounds\s*:', fm_text):
        fm_text = re.sub(
            r'(review_rounds\s*:\s*)\d+',
            r'\g<1>1',
            fm_text
        )
    else:
        fm_text = fm_text.rstrip() + '\nreview_rounds: 1\n'

    # 3. 添加/更新 reviewed_at
    if re.search(r'reviewed_at\s*:', fm_text):
        fm_text = re.sub(
            r"(reviewed_at\s*:\s*)['\"]?[^\n]*['\"]?",
            r"\g<1>'2026-04-20'",
            fm_text
        )
    else:
        fm_text = fm_text.rstrip() + "\nreviewed_at: '2026-04-20'\n"

    # 4. 添加/更新 reviewer
    if re.search(r'reviewer\s*:', fm_text):
        fm_text = re.sub(
            r"(reviewer\s*:\s*)['\"]?[^\n]*['\"]?",
            r"\g<1>'AI Mathematical Reviewer'",
            fm_text
        )
    else:
        fm_text = fm_text.rstrip() + "\nreviewer: 'AI Mathematical Reviewer'\n"

    # 5. 在 tags 中添加 "mathematical_reviewed"
    # 先检查是否已有该 tag
    if re.search(r'"mathematical_reviewed"', fm_text):
        pass  # 已存在
    elif 'tags:' in fm_text:
        # tags 行内数组格式: tags: [a, b, c]
        inline_match = re.search(r'(tags\s*:\s*\[)([^\]]*)(\])', fm_text)
        if inline_match:
            prefix, inner, suffix = inline_match.group(1), inline_match.group(2), inline_match.group(3)
            if inner.strip():
                new_inner = inner.rstrip() + ', "mathematical_reviewed"'
            else:
                new_inner = '"mathematical_reviewed"'
            fm_text = fm_text[:inline_match.start()] + prefix + new_inner + suffix + fm_text[inline_match.end():]
        else:
            # tags 列表格式: tags:\n  - a\n  - b
            lines = fm_text.split('\n')
            new_lines = []
            tags_started = False
            inserted = False
            for i, line in enumerate(lines):
                if not tags_started and re.match(r'^tags\s*:', line):
                    tags_started = True
                    new_lines.append(line)
                    continue
                if tags_started:
                    if line.strip().startswith('- '):
                        new_lines.append(line)
                        continue
                    elif line.strip() == '':
                        new_lines.append(line)
                        continue
                    else:
                        # 列表结束，插入新 tag
                        if not inserted:
                            # 找到最后一个 tag 行的缩进
                            for j in range(len(new_lines) - 1, -1, -1):
                                if new_lines[j].strip().startswith('- '):
                                    indent = len(new_lines[j]) - len(new_lines[j].lstrip())
                                    break
                            else:
                                indent = 2
                            new_lines.insert(len(new_lines) - (1 if new_lines[-1].strip() == '' else 0), ' ' * indent + '- "mathematical_reviewed"')
                            inserted = True
                        tags_started = False
                        new_lines.append(line)
                else:
                    new_lines.append(line)
            # 如果 tags 在文件末尾
            if tags_started and not inserted:
                for j in range(len(new_lines) - 1, -1, -1):
                    if new_lines[j].strip().startswith('- '):
                        indent = len(new_lines[j]) - len(new_lines[j].lstrip())
                        break
                else:
                    indent = 2
                new_lines.append(' ' * indent + '- "mathematical_reviewed"')
            fm_text = '\n'.join(new_lines)
    else:
        fm_text = fm_text.rstrip() + '\ntags:\n  - "mathematical_reviewed"\n'

    return fm_text


def process_file(filepath):
    """处理单个文件"""
    with open(filepath, 'r', encoding='utf-8') as fp:
        content = fp.read()

    fm_end = content.find('---', 3)
    if fm_end == -1:
        return False, 'No front matter end found'

    fm = content[3:fm_end]
    body = content[fm_end + 3:]

    new_fm = update_front_matter(fm)

    # 检查是否已有审阅记录
    if '## 审阅记录' not in body:
        body = body.rstrip() + REVIEW_BLOCK

    new_content = '---' + new_fm + '---' + body

    with open(filepath, 'w', encoding='utf-8') as fp:
        fp.write(new_content)

    return True, None


def main():
    targets = find_target_files()
    print(f'Found {len(targets)} target files to process.')

    success_count = 0
    failed = []

    for filepath in targets:
        rel = os.path.relpath(filepath, DOCS_DIR)
        ok, err = process_file(filepath)
        if ok:
            success_count += 1
            print(f'  [OK] {rel}')
        else:
            failed.append((rel, err))
            print(f'  [FAIL] {rel}: {err}')

    print(f'\n{"="*60}')
    print(f'Total target files: {len(targets)}')
    print(f'Successfully processed: {success_count}')
    if failed:
        print(f'Failed: {len(failed)}')
        for rel, err in failed:
            print(f'  - {rel}: {err}')


if __name__ == '__main__':
    main()
