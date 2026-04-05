#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
链接问题模式分析工具
分析无效链接的类型和模式，为修复提供数据支持
"""

import json
from pathlib import Path
from collections import Counter
import re

def analyze_patterns():
    report_path = Path('output/link_check_report.json')
    
    with open(report_path, 'r', encoding='utf-8') as f:
        data = json.load(f)
    
    issues = data['issues']
    
    print("=" * 60)
    print("链接问题模式分析报告")
    print("=" * 60)
    print(f"\n总问题数: {len(issues)}")
    
    # 按类型统计
    broken_file = [i for i in issues if i['issue_type'] == 'broken_file']
    broken_anchor = [i for i in issues if i['issue_type'] == 'broken_anchor']
    empty_link = [i for i in issues if i['issue_type'] == 'empty_link']
    
    print(f"\n【问题类型分布】")
    print(f"  - 文件不存在: {len(broken_file)} ({len(broken_file)/len(issues)*100:.1f}%)")
    print(f"  - 锚点不存在: {len(broken_anchor)} ({len(broken_anchor)/len(issues)*100:.1f}%)")
    print(f"  - 空链接: {len(empty_link)} ({len(empty_link)/len(issues)*100:.1f}%)")
    
    # 分析文件不存在问题
    print(f"\n【文件不存在问题分析】")
    file_targets = [i['link_target'] for i in broken_file]
    
    # 目录链接
    dir_links = [t for t in file_targets if t.endswith('/')]
    print(f"  - 指向目录的链接: {len(dir_links)}")
    
    # 相对路径链接
    rel_links = [t for t in file_targets if t.startswith(('./', '../'))]
    print(f"  - 相对路径链接: {len(rel_links)}")
    
    # 特殊文件链接
    dot_links = [t for t in file_targets if t == '.' or t == './']
    print(f"  - 当前目录链接(.): {len(dot_links)}")
    
    # 分析锚点问题
    print(f"\n【锚点不存在问题分析】")
    anchor_targets = [i['link_target'] for i in broken_anchor]
    
    # 带文件路径的锚点
    file_anchors = [t for t in anchor_targets if '#' in t and not t.startswith('#')]
    print(f"  - 跨文件锚点: {len(file_anchors)}")
    
    # 仅锚点
    pure_anchors = [t for t in anchor_targets if t.startswith('#')]
    print(f"  - 纯锚点链接: {len(pure_anchors)}")
    
    # 常见锚点模式
    anchor_patterns = Counter()
    for t in anchor_targets:
        # 提取锚点名
        if '#' in t:
            anchor = t.split('#')[-1]
        else:
            anchor = t
        
        # 分类
        if anchor.startswith('-'):
            anchor_patterns['带前导连字符'] += 1
        elif re.match(r'^\d', anchor):
            anchor_patterns['数字开头'] += 1
        elif '--' in anchor:
            anchor_patterns['双连字符'] += 1
        elif re.search(r'[\u4e00-\u9fff]', anchor):
            anchor_patterns['含中文字符'] += 1
        elif anchor.startswith('编号'):
            anchor_patterns['编号前缀'] += 1
        else:
            anchor_patterns['其他'] += 1
    
    print(f"\n【锚点命名模式】")
    for pattern, count in anchor_patterns.most_common():
        print(f"  - {pattern}: {count}")
    
    # 按源文件统计问题数量
    source_counter = Counter(i['source_file'] for i in issues)
    print(f"\n【问题最多的文件 TOP 10】")
    for file, count in source_counter.most_common(10):
        print(f"  - {file}: {count} 个问题")
    
    # 常见错误路径模式
    print(f"\n【常见错误路径模式】")
    path_patterns = Counter()
    for t in file_targets:
        # 提取目录名
        if '/' in t:
            parts = t.split('/')
            if len(parts) >= 2:
                path_patterns['/'.join(parts[:2])] += 1
    
    for path, count in path_patterns.most_common(10):
        print(f"  - {path}/...: {count}")
    
    # 建议的修复策略
    print(f"\n【建议的修复策略】")
    print(f"  1. 自动修复候选:")
    print(f"     - 目录链接 -> 转换为README.md: {len(dir_links)}")
    print(f"     - 当前目录(.) -> 移除或修正: {len(dot_links)}")
    print(f"     - 带前导连字符锚点 -> 移除连字符: {anchor_patterns.get('带前导连字符', 0)}")
    print(f"  2. 需人工确认:")
    print(f"     - 文件移动/重命名: ~{len(rel_links)}")
    print(f"     - 复杂锚点修正: ~{anchor_patterns.get('双连字符', 0) + anchor_patterns.get('其他', 0)}")

if __name__ == '__main__':
    analyze_patterns()
