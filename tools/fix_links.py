#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalMath项目外部链接修复工具
修复策略:
1. 删除本地/测试链接
2. 保留重要链接（国际课程、数学资源、参考文献）
3. 对其他链接添加标记
"""

import re
import os
from pathlib import Path
from collections import defaultdict

# 需要删除的链接模式
DELETE_PATTERNS = [
    r'http://localhost[:/][^\s\)\]\<\>\"\'\`]*',
    r'http://127\.0\.0\.1[:/][^\s\)\]\<\>\"\'\`]*',
    r'http://example\.com[^\s\)\]\<\>\"\'\`]*',
    r'http://10\.\d+\.\d+\.\d+[^\s\)\]\<\>\"\'\`]*',
    r'http://api\.example\.com[^\s\)\]\<\>\"\'\`]*',
    r'http://backend[^\s\)\]\<\>\"\'\`]*',
    r'http://backend-service[^\s\)\]\<\>\"\'\`]*',
]

# 重要链接模式（保留）
KEEP_PATTERNS = [
    r'https?://math\.mit\.edu[^\s\)\]\<\>\"\'\`]*',
    r'https?://ocw\.mit\.edu[^\s\)\]\<\>\"\'\`]*',
    r'https?://math\.harvard\.edu[^\s\)\]\<\>\"\'\`]*',
    r'https?://math\.stanford\.edu[^\s\)\]\<\>\"\'\`]*',
    r'https?://math\.berkeley\.edu[^\s\)\]\<\>\"\'\`]*',
    r'https?://www\.maths\.cam\.ac\.uk[^\s\)\]\<\>\"\'\`]*',
    r'https?://math\.ox\.ac\.uk[^\s\)\]\<\>\"\'\`]*',
    r'https?://math\.princeton\.edu[^\s\)\]\<\>\"\'\`]*',
    r'https?://math\.ethz\.ch[^\s\)\]\<\>\"\'\`]*',
    r'https?://arxiv\.org[^\s\)\]\<\>\"\'\`]*',
    r'https?://oeis\.org[^\s\)\]\<\>\"\'\`]*',
    r'https?://doi\.org[^\s\)\]\<\>\"\'\`]*',
    r'https?://.*wikipedia\.org[^\s\)\]\<\>\"\'\`]*',
    r'https?://www\.ams\.org[^\s\)\]\<\>\"\'\`]*',
    r'https?://www\.maa\.org[^\s\)\]\<\>\"\'\`]*',
    r'https?://mathscinet\.ams\.org[^\s\)\]\<\>\"\'\`]*',
    r'https?://mathworld\.wolfram\.com[^\s\)\]\<\>\"\'\`]*',
    r'https?://ncatlab\.org[^\s\)\]\<\>\"\'\`]*',
    r'https?://lean-lang\.org[^\s\)\]\<\>\"\'\`]*',
    r'https?://leanprover\.github\.io[^\s\)\]\<\>\"\'\`]*',
    r'https?://github\.com[^\s\)\]\<\>\"\'\`]*',
    r'https?://docs\.github\.com[^\s\)\]\<\>\"\'\`]*',
    r'https?://guides\.github\.com[^\s\)\]\<\>\"\'\`]*',
    r'https?://mathoverflow\.net[^\s\)\]\<\>\"\'\`]*',
    r'https?://math\.stackexchange\.com[^\s\)\]\<\>\"\'\`]*',
]

# 统计数据
stats = {
    'files_scanned': 0,
    'files_modified': 0,
    'links_deleted': 0,
    'links_kept': 0,
    'links_marked_for_update': 0,
}


def should_delete(url):
    """判断链接是否应该删除"""
    for pattern in DELETE_PATTERNS:
        if re.match(pattern, url, re.IGNORECASE):
            return True
    return False


def should_keep(url):
    """判断链接是否应该保留"""
    for pattern in KEEP_PATTERNS:
        if re.match(pattern, url, re.IGNORECASE):
            return True
    return False


def find_and_process_links(content):
    """查找并处理链接，返回新内容和处理统计"""
    new_content = content
    modified = False
    local_stats = {
        'deleted': 0,
        'kept': 0,
        'marked': 0,
    }
    
    # 匹配各种链接格式
    # 1. Markdown链接 [text](url)
    md_link_pattern = r'\[([^\]]+)\]\((https?://[^\)]+)\)'
    
    def process_md_link(match):
        nonlocal modified
        text = match.group(1)
        url = match.group(2)
        
        if should_delete(url):
            local_stats['deleted'] += 1
            modified = True
            return text  # 只保留文本，删除链接
        elif should_keep(url):
            local_stats['kept'] += 1
            return match.group(0)  # 保留原样
        else:
            # 其他链接，添加"[需更新]"标记
            local_stats['marked'] += 1
            modified = True
            return f"{match.group(0)}[需更新]"
    
    new_content = re.sub(md_link_pattern, process_md_link, new_content)
    
    # 2. 裸链接
    bare_link_pattern = r'(?<![\[\(])(https?://[^\s\)\]\<\>\"\'\`\,\;]+)'
    
    def process_bare_link(match):
        nonlocal modified
        url = match.group(1)
        
        # 确保不是Markdown链接的一部分
        # 检查前面是否有 [
        pos = match.start()
        if pos > 0 and new_content[pos-1:pos] == '[':
            return match.group(0)
        
        if should_delete(url):
            local_stats['deleted'] += 1
            modified = True
            return ""  # 删除
        elif should_keep(url):
            local_stats['kept'] += 1
            return match.group(0)  # 保留原样
        else:
            # 其他链接，添加"[需更新]"标记
            local_stats['marked'] += 1
            modified = True
            return f"{url}[需更新]"
    
    new_content = re.sub(bare_link_pattern, process_bare_link, new_content)
    
    return new_content, local_stats, modified


def process_file(file_path):
    """处理单个文件"""
    try:
        with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
        
        new_content, local_stats, modified = find_and_process_links(content)
        
        if modified:
            # 创建备份
            backup_path = str(file_path) + '.backup'
            with open(backup_path, 'w', encoding='utf-8') as f:
                f.write(content)
            
            # 写入新内容
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(new_content)
            
            return local_stats
        
        return None
        
    except Exception as e:
        print(f"Error processing {file_path}: {e}")
        return None


def scan_and_fix(project_dir):
    """扫描并修复项目中的链接"""
    project_path = Path(project_dir)
    
    # 要扫描的文件类型
    extensions = ['.md']
    
    # 排除的目录
    exclude_dirs = {'.git', 'node_modules', '__pycache__', '.venv', 'venv', 
                    'dist', 'build', 'vendor', 'tools', 'output'}
    
    # 要扫描的目录
    scan_dirs = ['docs', 'concept', '.']
    
    for scan_dir in scan_dirs:
        target_path = project_path / scan_dir
        if not target_path.exists():
            continue
        
        for ext in extensions:
            for file_path in target_path.rglob(f'*{ext}'):
                # 跳过排除的目录
                if any(excluded in str(file_path) for excluded in exclude_dirs):
                    continue
                
                stats['files_scanned'] += 1
                
                if stats['files_scanned'] % 1000 == 0:
                    print(f"  已扫描 {stats['files_scanned']} 个文件...")
                
                result = process_file(file_path)
                if result:
                    stats['files_modified'] += 1
                    stats['links_deleted'] += result['deleted']
                    stats['links_kept'] += result['kept']
                    stats['links_marked_for_update'] += result['marked']


def main():
    """主函数"""
    project_dir = r"g:\_src\FormalMath"
    
    print("开始修复FormalMath项目中的外部链接...")
    print()
    
    scan_and_fix(project_dir)
    
    print()
    print("=" * 50)
    print("修复完成！")
    print("=" * 50)
    print()
    print(f"文件扫描数: {stats['files_scanned']}")
    print(f"文件修改数: {stats['files_modified']}")
    print(f"链接删除数: {stats['links_deleted']}")
    print(f"链接保留数: {stats['links_kept']}")
    print(f"链接标记为'需更新': {stats['links_marked_for_update']}")
    print()
    print("注意：修改前已创建 .backup 文件备份")


if __name__ == "__main__":
    main()
