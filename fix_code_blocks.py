#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
修复代码块格式：将单独的 ``` 改为 ```text
"""

import re
from pathlib import Path

def fix_code_blocks(content):
    """修复代码块：单独的 ``` 改为 ```text"""
    lines = content.split('\n')
    result = []
    in_code_block = False
    
    for i, line in enumerate(lines):
        stripped = line.strip()
        
        # 检查代码块开始
        if stripped == '```':
            # 单独的 ```，需要添加 text
            result.append('```text')
            in_code_block = True
        elif stripped.startswith('```') and not stripped.startswith('```text'):
            # 已经有其他语言标识符，保持不变
            result.append(line)
            in_code_block = True
        elif stripped.startswith('```text'):
            result.append(line)
            in_code_block = True
        # 检查代码块结束
        elif stripped == '```' and in_code_block:
            result.append('```')
            in_code_block = False
        else:
            result.append(line)
    
    return '\n'.join(result)

def main():
    """主函数"""
    base_dir = Path(r'e:\_src\FormalMath\数学家理念体系')
    
    total_files = 0
    fixed_files = 0
    
    for md_file in base_dir.rglob('*.md'):
        total_files += 1
        try:
            with open(md_file, 'r', encoding='utf-8') as f:
                content = f.read()
            
            original = content
            content = fix_code_blocks(content)
            
            if content != original:
                with open(md_file, 'w', encoding='utf-8') as f:
                    f.write(content)
                fixed_files += 1
                print(f"Fixed: {md_file}")
        except Exception as e:
            print(f"Error processing {md_file}: {e}")
    
    print(f"\nTotal files: {total_files}")
    print(f"Fixed files: {fixed_files}")

if __name__ == '__main__':
    main()
