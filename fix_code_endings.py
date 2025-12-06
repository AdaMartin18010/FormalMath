#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
修复代码块结尾：将所有 ```text 结尾改为 ```
"""

import re
from pathlib import Path

def fix_code_endings(content):
    """修复代码块结尾：```text 改为 ```"""
    # 使用正则表达式替换行尾的 ```text
    content = re.sub(r'```text\s*$', '```', content, flags=re.MULTILINE)
    return content

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
            content = fix_code_endings(content)
            
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
