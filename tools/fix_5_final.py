#!/usr/bin/env python3
# -*- coding: utf-8 -*-
import re
from pathlib import Path

docs_dir = Path(r"g:\_src\FormalMath\docs")

files_to_fix = [
    ('concept-mindmaps/07-傅里叶级数.md', ['yaml']),
    ('decision-trees/02-代数学学习路径决策.md', ['headings']),
    ('decision-trees/03-几何学习路径决策.md', ['headings']),
    ('decision-trees/06-极限求解方法决策.md', ['headings']),
    ('generated/references/README.md', ['yaml']),
]

yaml_header = "---\nmsc_primary: \"00A99\"\nmsc_secondary: ['00-XX']\n---\n\n"

for rel_path, fix_types in files_to_fix:
    filepath = docs_dir / rel_path
    if not filepath.exists():
        continue
    
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # 添加YAML
    if 'yaml' in fix_types and not content.startswith('---'):
        content = yaml_header + content
    
    # 修复标题层级
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
                    level = new_level
                
                prev_level = level
            
            new_lines.append(line)
        
        content = '\n'.join(new_lines)
    
    with open(filepath, 'w', encoding='utf-8') as f:
        f.write(content)
    print(f'✅ {rel_path}')
