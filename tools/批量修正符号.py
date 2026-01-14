#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalMath项目批量修正符号脚本
批量修正符号不一致项：\\ne -> \\neq, \\le -> \\leq, \\ge -> \\geq
"""

import os
import re
import shutil
from pathlib import Path

# 修正规则 - 使用负向前瞻确保不会误替换 \neq, \leq, \geq
CORRECTION_RULES = {
    r'\\ne(?!q)': r'\\neq',
    r'\\le(?!q)': r'\\leq',
    r'\\ge(?!q)': r'\\geq',
}

# 排除的目录和文件模式
EXCLUDE_PATTERNS = [
    r'00-归档',
    r'99-归档',
    r'node_modules',
    r'\.git',
    r'\.bak$',
    r'^00-',
    r'tools',
]

def should_exclude(filepath):
    """检查文件是否应该被排除"""
    path_str = str(filepath)
    for pattern in EXCLUDE_PATTERNS:
        if re.search(pattern, path_str, re.IGNORECASE):
            return True
    return False

def fix_symbols_in_file(filepath, backup=True):
    """修正单个文件中的符号"""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()

        original_content = content
        modified = False

        # 应用修正规则
        for pattern, replacement in CORRECTION_RULES.items():
            if re.search(pattern, content):
                content = re.sub(pattern, replacement, content)
                modified = True

        if modified:
            if backup:
                backup_path = str(filepath) + '.bak'
                shutil.copy2(filepath, backup_path)

            with open(filepath, 'w', encoding='utf-8') as f:
                f.write(content)

            return True, content != original_content

        return False, False
    except Exception as e:
        print(f"错误处理文件 {filepath}: {e}")
        return False, False

def main():
    base_path = Path(__file__).parent.parent
    fixed_count = 0
    skipped_count = 0
    error_count = 0

    print(f"开始批量修正符号不一致项...")
    print(f"基础路径: {base_path}")
    print(f"修正规则: {CORRECTION_RULES}")
    print()

    # 获取所有Markdown文件
    all_files = list(base_path.rglob('*.md'))

    print(f"找到 {len(all_files)} 个Markdown文件")

    for filepath in all_files:
        if should_exclude(filepath):
            skipped_count += 1
            continue

        try:
            modified, success = fix_symbols_in_file(filepath, backup=True)
            if modified:
                fixed_count += 1
                relative_path = filepath.relative_to(base_path)
                if fixed_count % 50 == 0:
                    print(f"已处理 {fixed_count} 个文件...")
        except Exception as e:
            error_count += 1
            print(f"处理文件 {filepath} 时出错: {e}")

    print()
    print("修正完成:")
    print(f"  已修正: {fixed_count} 个文件")
    print(f"  已跳过: {skipped_count} 个文件")
    print(f"  错误: {error_count} 个文件")

if __name__ == '__main__':
    main()
