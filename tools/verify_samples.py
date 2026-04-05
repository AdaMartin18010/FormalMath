#!/usr/bin/env python3
"""验证样本文件Frontmatter"""
import yaml
import re

files = [
    'concept/核心概念/01-集合.md',
    'concept/核心概念/33-朗兰兹纲领.md',
    '00-MIT课程内容对齐报告.md',
    '00-Wikipedia代数学对齐报告.md'
]

print('=== 样本文件Frontmatter验证 ===\n')

for filepath in files:
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
        
        if content.startswith('---'):
            match = re.search(r'^---\s*\n(.*?)\n---', content, re.DOTALL)
            if match:
                data = yaml.safe_load(match.group(1))
                print(f'✅ {filepath}')
                title = data.get('title', 'MISSING')
                print(f'   title: {title[:50]}...' if len(str(title)) > 50 else f'   title: {title}')
                print(f'   msc_primary: {data.get("msc_primary", "MISSING")}')
                print(f'   processed_at: {data.get("processed_at", "MISSING")}')
                print()
    except Exception as e:
        print(f'❌ {filepath}: {e}\n')
