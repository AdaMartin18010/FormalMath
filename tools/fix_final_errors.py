#!/usr/bin/env python3
# -*- coding: utf-8 -*-
import os
import re
from pathlib import Path

docs_dir = Path(r"g:\_src\FormalMath\docs")

files_to_fix = [
    ('00-实战问题解决/00-实战问题质量提升完成报告.md', ['yaml']),
    ('concept-mindmaps/mathphys-02-quantum-mechanics.md', ['yaml']),
    ('decision-trees/00-决策树质量报告.md', ['yaml', 'headings']),
    ('decision-trees/02-代数学学习路径决策.md', ['headings']),
    ('decision-trees/03-几何学习路径决策.md', ['headings']),
    ('decision-trees/06-极限求解方法决策.md', ['headings']),
    ('generated/references/快速引用速查表.md', ['yaml']),
]

yaml_header = "---\nmsc_primary: \"00A99\"\nmsc_secondary: ['00-XX']\n---\n\n"

def fix_file(rel_path, fix_types):
    filepath = docs_dir / rel_path
    if not filepath.exists():
        return False, '文件不存在'
    
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
        
        original = content
        fixes = []
        
        # 1. 添加YAML头
        if 'yaml' in fix_types and not content.startswith('---'):
            content = yaml_header + content
            fixes.append('添加YAML头')
        
        # 2. 修复标题层级跳跃
        if 'headings' in fix_types:
            lines = content.split('\n')
            new_lines = []
            prev_level = 0
            
            for line in lines:
                heading_match = re.match(r'^(#{1,6})\s+(.+)$', line)
                if heading_match:
                    level = len(heading_match.group(1))
                    text = heading_match.group(2)
                    
                    if prev_level > 0 and level > prev_level + 1:
                        new_level = prev_level + 1
                        line = '#' * new_level + ' ' + text
                        fixes.append(f'修复层级: H{level}->H{new_level}')
                        level = new_level
                    
                    prev_level = level
                
                new_lines.append(line)
            
            content = '\n'.join(new_lines)
        
        if content != original:
            with open(filepath, 'w', encoding='utf-8') as f:
                f.write(content)
            return True, fixes
        return False, '无需修复'
    except Exception as e:
        return False, str(e)

def main():
    for rel_path, fix_types in files_to_fix:
        fixed, msg = fix_file(rel_path, fix_types)
        status = '✅' if fixed else '⏭️'
        print(f'{status} {rel_path}: {msg}')

if __name__ == '__main__':
    main()
