#!/usr/bin/env python3
"""
扫描并修复FormalMath项目中的断链问题
"""

import os
import re
import json
from pathlib import Path
from collections import defaultdict

WORK_DIR = Path("g:/_src/FormalMath")

# 链接正则表达式
MARKDOWN_LINK_RE = re.compile(r'\[([^\]]+)\]\(([^)]+)\)')
CONCEPT_ID_RE = re.compile(r'concept[:\s]+([A-Z]{2,4}-\d{2,4})', re.IGNORECASE)
CONCEPT_REF_RE = re.compile(r'`([A-Z]{2,4}-\d{2,4})`')
CONCEPT_FILE_RE = re.compile(r'(\d{2}-[A-Z]{2,4}-\d{2,4})\.md')

def get_all_md_files():
    """获取所有markdown文件"""
    md_files = []
    for pattern in ['concept/**/*.md', 'tools/**/*.md', 'tests/**/*.md', '*.md', 'docs/**/*.md']:
        md_files.extend(WORK_DIR.glob(pattern))
    return [f for f in md_files if f.is_file()]

def extract_links(content, file_path):
    """提取文件中的所有链接"""
    links = []
    
    # Markdown链接 [text](path)
    for match in MARKDOWN_LINK_RE.finditer(content):
        text = match.group(1)
        link_path = match.group(2)
        links.append({
            'type': 'markdown',
            'text': text,
            'path': link_path,
            'line': content[:match.start()].count('\n') + 1
        })
    
    return links

def check_link_validity(link, source_file):
    """检查链接是否有效"""
    link_path = link['path']
    
    # 忽略外部链接和锚点
    if link_path.startswith('http://') or link_path.startswith('https://') or \
       link_path.startswith('mailto:'):
        return True, None
    
    # 处理带锚点的链接
    if '#' in link_path:
        link_path = link_path.split('#')[0]
        if not link_path:
            return True, None  # 纯锚点链接
    
    # 解析相对路径
    if link_path.startswith('/'):
        full_path = WORK_DIR / link_path.lstrip('/')
    else:
        full_path = source_file.parent / link_path
    
    try:
        full_path = full_path.resolve()
        if not full_path.exists():
            rel_error = str(full_path.relative_to(WORK_DIR)) if full_path.is_relative_to(WORK_DIR) else str(full_path)
            return False, rel_error
    except Exception as e:
        return False, str(e)
    
    return True, None

def scan_all_links():
    """扫描所有链接"""
    all_files = get_all_md_files()
    broken_links = []
    valid_links = []
    
    print(f"扫描 {len(all_files)} 个文件...")
    
    for i, md_file in enumerate(all_files):
        if i % 500 == 0:
            print(f"  已处理 {i}/{len(all_files)} 个文件...")
        
        try:
            with open(md_file, 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read()
            
            links = extract_links(content, md_file)
            
            for link in links:
                is_valid, error_info = check_link_validity(link, md_file)
                
                link_info = {
                    'source': str(md_file.relative_to(WORK_DIR)),
                    'type': link['type'],
                    'text': link['text'],
                    'path': link['path'],
                    'line': link['line']
                }
                
                if is_valid:
                    valid_links.append(link_info)
                else:
                    link_info['error'] = error_info
                    broken_links.append(link_info)
        except Exception as e:
            print(f"错误处理文件 {md_file}: {e}")
    
    return broken_links, valid_links

def main():
    broken_links, valid_links = scan_all_links()
    
    print(f"\n找到 {len(valid_links)} 个有效链接")
    print(f"找到 {len(broken_links)} 个断链")
    
    # 按源文件分组
    broken_by_source = defaultdict(list)
    for link in broken_links:
        broken_by_source[link['source']].append(link)
    
    # 输出报告
    report = {
        'broken_links_count': len(broken_links),
        'valid_links_count': len(valid_links),
        'broken_links': broken_links,
        'broken_by_source': dict(broken_by_source)
    }
    
    with open(WORK_DIR / 'tmp_broken_links_report.json', 'w', encoding='utf-8') as f:
        json.dump(report, f, ensure_ascii=False, indent=2)
    
    print(f"\n详细报告已保存到 tmp_broken_links_report.json")
    
    # 显示前20个断链
    if broken_links:
        print("\n前20个断链:")
        for link in broken_links[:20]:
            print(f"  - {link['source']}:{link['line']} -> {link['path']}")

if __name__ == '__main__':
    main()
