#!/usr/bin/env python3
# -*- coding: utf-8 -*-
import re
from pathlib import Path

docs_dir = Path(r"g:\_src\FormalMath\docs")

files = [
    'concept-mindmaps/mathphys-03-statistical-mechanics.md',
    'concept-mindmaps/mathphys-05-general-relativity.md',
    'decision-trees/02-代数学学习路径决策.md',
    'decision-trees/03-几何学习路径决策.md',
    'decision-trees/06-极限求解方法决策.md',
    'generated/references/00-参考文献完善执行摘要.md',
    'inference-trees/00-推理树数学精确性提升完成报告.md',
]

yaml_header = "---\nmsc_primary: \"00A99\"\nmsc_secondary: ['00-XX']\n---\n\n"

for rel_path in files:
    filepath = docs_dir / rel_path
    if not filepath.exists():
        print(f'跳过: {rel_path}')
        continue
    
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # 1. 添加YAML头
    if not content.startswith('---'):
        content = yaml_header + content
        print(f'添加YAML: {rel_path}')
    
    # 2. 修复标题层级
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
    print(f'✅ 已修复: {rel_path}')
