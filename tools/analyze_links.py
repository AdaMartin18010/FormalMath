#!/usr/bin/env python3
import json
import os
from collections import Counter

with open('output/link_check_report.json', 'r', encoding='utf-8') as f:
    data = json.load(f)

issues = data['issues']

# 分析 'd' 链接的模式
d_issues = [i for i in issues if i['link_target'] == 'd']
print(f"链接到 'd' 的问题数量: {len(d_issues)}")
print('样例:')
for i in d_issues[:10]:
    print(f"  {i['source_file']} -> '{i['link_target']}'")

print()

# 分析术语词典链接
term_issues = [i for i in issues if 'FormalMath术语词典' in i['link_target']]
print(f"术语词典链接问题数量: {len(term_issues)}")
print('样例:')
for i in term_issues[:5]:
    print(f"  {i['source_file']} -> {i['link_target']}")

print()

# 检查是否存在这些术语词典文件
term_files = [
    'docs/FormalMath术语词典-基础数学.md',
    'docs/FormalMath术语词典-代数结构.md',
    'docs/FormalMath术语词典-分析学.md',
]
for tf in term_files:
    exists = os.path.exists(tf)
    print(f'{tf}: {"存在" if exists else "不存在"}')

print()

# 分析目录锚点问题
toc_issues = [i for i in issues if i['link_target'] == '#-目录']
print(f"#-目录 锚点问题数量: {len(toc_issues)}")
print('样例源文件:')
for i in toc_issues[:5]:
    print(f"  {i['source_file']}")
