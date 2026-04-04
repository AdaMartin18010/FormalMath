#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
修复重复的YAML元数据头
"""

import os
import re
from pathlib import Path
from datetime import datetime

DOCS_DIR = Path(r"g:\_src\FormalMath\docs")
IGNORE_DIRS = {'.git', '__pycache__', 'node_modules', 'venv', '.venv', '00-归档', '99-归档文档', '归档'}


def fix_duplicate_yaml(content):
    """修复重复的YAML头"""
    # 检查是否有重复的YAML头
    yaml_pattern = r'^(---\s*\n.*?\n---\s*\n)'
    match = re.match(yaml_pattern, content, re.DOTALL)
    
    if not match:
        return content, False
    
    first_yaml = match.group(1)
    remaining = content[len(first_yaml):]
    
    # 检查剩余部分是否还有YAML头
    second_match = re.match(yaml_pattern, remaining, re.DOTALL)
    if second_match:
        # 移除第二个YAML头
        remaining = remaining[len(second_match.group(1)):]
        return first_yaml + remaining, True
    
    return content, False


def process_file(filepath):
    """处理单个文件"""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
        
        new_content, fixed = fix_duplicate_yaml(content)
        
        if fixed:
            with open(filepath, 'w', encoding='utf-8') as f:
                f.write(new_content)
            return True
        return False
    except Exception as e:
        print(f"Error processing {filepath}: {e}")
        return False


def get_all_md_files():
    """获取所有Markdown文件"""
    md_files = []
    for root, dirs, files in os.walk(DOCS_DIR):
        dirs[:] = [d for d in dirs if d not in IGNORE_DIRS]
        for file in files:
            if file.endswith('.md'):
                md_files.append(os.path.join(root, file))
    return md_files


def main():
    print("=" * 60)
    print("修复重复YAML元数据头")
    print("=" * 60)
    
    md_files = get_all_md_files()
    print(f"\n找到 {len(md_files)} 个Markdown文件")
    
    fixed_count = 0
    for i, filepath in enumerate(md_files, 1):
        if i % 500 == 0:
            print(f"   已处理 {i}/{len(md_files)} 个文件...")
        
        if process_file(filepath):
            fixed_count += 1
    
    print(f"\n✅ 完成！修复了 {fixed_count} 个文件的重复YAML头")


if __name__ == '__main__':
    main()
