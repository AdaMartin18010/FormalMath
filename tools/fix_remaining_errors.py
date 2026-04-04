#!/usr/bin/env python3
# -*- coding: utf-8 -*-
import os
import re
from pathlib import Path

docs_dir = Path(r"g:\_src\FormalMath\docs")

files_to_fix = [
    '00-实战问题解决/00-实战问题分类索引.md',
    '00-实战问题解决/00-实战问题质量提升模板.md',
    'comparison-matrices/16-证明方法-初等vs高等.md',
    'comparison-matrices/17-计算方法-精确vs数值vs符号.md',
    'concept-mindmaps/05-一致收敛.md',
    'concept-mindmaps/06-幂级数.md',
    'concept-mindmaps/11-解析函数.md',
    'concept-mindmaps/topology-topological-space.md',
    'decision-trees/00-高级问题求解决策树索引.md',
    'decision-trees/01-分析学学习路径决策.md',
    'decision-trees/02-代数学学习路径决策.md',
    'decision-trees/03-几何学习路径决策.md',
    'decision-trees/06-极限求解方法决策.md',
    'generated/references/分支文献推荐指南.md',
    'generated/references/参考文献完整性报告.md',
    'inference-trees/01-epsilon-delta-limit.md',
    '00-交叉引用网络/01-导航优化方案.md',
]

yaml_header = "---\nmsc_primary: \"00A99\"\nmsc_secondary: ['00-XX']\n---\n\n"

def fix_file(rel_path):
    filepath = docs_dir / rel_path
    if not filepath.exists():
        return False, '文件不存在'
    
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
        
        original = content
        fixes = []
        
        # 1. 添加YAML头
        if not content.startswith('---'):
            content = yaml_header + content
            fixes.append('添加YAML头')
        
        # 2. 修复标题层级跳跃
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
    for rel_path in files_to_fix:
        fixed, msg = fix_file(rel_path)
        status = '✅' if fixed else '⏭️'
        print(f'{status} {rel_path}: {msg}')

if __name__ == '__main__':
    main()
