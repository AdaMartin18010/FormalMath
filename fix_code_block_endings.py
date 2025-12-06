#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
修复代码块结尾：将 ```text 结尾改为 ```
只修复结尾，不修改开头
"""

import re
from pathlib import Path

def fix_code_block_endings(content):
    """修复代码块结尾：```text 改为 ```"""
    # 只替换行尾的 ```text，保留开头的 ```text
    # 使用多行模式，只匹配行尾
    content = re.sub(r'```text\s*$', '```', content, flags=re.MULTILINE)
    return content

def process_file(file_path):
    """处理单个文件"""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        original = content
        content = fix_code_block_endings(content)
        
        if content != original:
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(content)
            return True
        return False
    except Exception as e:
        print(f"Error processing {file_path}: {e}")
        return False

def main():
    """主函数"""
    base_dir = Path(r'e:\_src\FormalMath\数学家理念体系')
    
    total_files = 0
    fixed_files = 0
    
    for md_file in base_dir.rglob('*.md'):
        total_files += 1
        if process_file(md_file):
            fixed_files += 1
            print(f"Fixed: {md_file}")
    
    print(f"\nTotal files: {total_files}")
    print(f"Fixed files: {fixed_files}")

if __name__ == '__main__':
    main()
