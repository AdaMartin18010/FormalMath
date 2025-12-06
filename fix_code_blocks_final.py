#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
修复代码块格式：
1. 代码块开头：单独的 ``` 改为 ```text
2. 代码块结尾：```text 改为 ```
"""

import re
from pathlib import Path

def fix_code_blocks(content):
    """修复代码块格式"""
    lines = content.split('\n')
    result = []
    in_code_block = False
    code_block_started = False
    
    for i, line in enumerate(lines):
        stripped = line.strip()
        
        # 检查代码块开始
        if stripped == '```':
            # 单独的 ```，需要添加 text
            result.append('```text')
            in_code_block = True
            code_block_started = True
        elif stripped.startswith('```text'):
            result.append(line)
            in_code_block = True
            code_block_started = True
        elif stripped.startswith('```') and not stripped.startswith('```text'):
            # 已经有其他语言标识符，保持不变
            result.append(line)
            in_code_block = True
            code_block_started = True
        # 检查代码块结束
        elif stripped == '```text' and in_code_block:
            # 错误的 ```text 结尾，改为 ```
            result.append('```')
            in_code_block = False
            code_block_started = False
        elif stripped == '```' and in_code_block:
            # 正确的 ``` 结尾
            result.append('```')
            in_code_block = False
            code_block_started = False
        else:
            result.append(line)
    
    return '\n'.join(result)

def process_file(file_path):
    """处理单个文件"""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        original = content
        content = fix_code_blocks(content)
        
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
