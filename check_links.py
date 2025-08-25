#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
检查FormalMath文档中所有本地链接的有效性
"""

import os
import re
import glob
from pathlib import Path
from urllib.parse import urlparse, unquote

def find_markdown_files(root_dir):
    """递归查找所有Markdown文件"""
    pattern = os.path.join(root_dir, "**/*.md")
    files = glob.glob(pattern, recursive=True)
    print(f"在 {root_dir} 中找到 {len(files)} 个Markdown文件")
    return files

def extract_links_from_markdown(file_path):
    """从Markdown文件中提取所有链接"""
    links = []
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # 匹配Markdown链接格式 [text](url)
        link_pattern = r'\[([^\]]+)\]\(([^)]+)\)'
        matches = re.findall(link_pattern, content)
        
        for text, url in matches:
            # 跳过锚点链接和外部链接
            if url.startswith('#') or url.startswith('http'):
                continue
            
            # 解码URL
            decoded_url = unquote(url)
            links.append({
                'text': text,
                'url': decoded_url,
                'line': content[:content.find(f'[{text}]({url})')].count('\n') + 1
            })
    
    except Exception as e:
        print(f"读取文件 {file_path} 时出错: {e}")
    
    return links

def resolve_link_path(base_file, link_url):
    """解析链接路径"""
    base_dir = os.path.dirname(base_file)
    
    # 处理相对路径
    if link_url.startswith('./'):
        link_url = link_url[2:]
    elif link_url.startswith('../'):
        # 计算相对路径
        parts = link_url.split('/')
        up_count = 0
        for part in parts:
            if part == '..':
                up_count += 1
            else:
                break
        
        # 向上导航目录
        current_dir = base_dir
        for _ in range(up_count):
            current_dir = os.path.dirname(current_dir)
        
        # 构建最终路径
        remaining_parts = parts[up_count:]
        resolved_path = os.path.join(current_dir, *remaining_parts)
    else:
        # 相对于当前文件的路径
        resolved_path = os.path.join(base_dir, link_url)
    
    return os.path.normpath(resolved_path)

def check_link_validity(base_file, link_info):
    """检查链接是否有效"""
    resolved_path = resolve_link_path(base_file, link_info['url'])
    
    # 检查文件是否存在
    if os.path.exists(resolved_path):
        return True, resolved_path
    
    # 检查是否有对应的目录
    if os.path.isdir(resolved_path):
        return True, resolved_path
    
    return False, resolved_path

def main():
    docs_dir = "docs"
    
    if not os.path.exists(docs_dir):
        print(f"错误: {docs_dir} 目录不存在")
        return
    
    print("开始检查FormalMath文档中的本地链接...")
    print("=" * 60)
    
    markdown_files = find_markdown_files(docs_dir)
    print(f"找到 {len(markdown_files)} 个Markdown文件")
    
    all_links = []
    broken_links = []
    
    for file_path in markdown_files:
        print(f"处理文件: {os.path.relpath(file_path, docs_dir)}")
        links = extract_links_from_markdown(file_path)
        print(f"  找到 {len(links)} 个本地链接")
        
        for link in links:
            link['source_file'] = file_path
            all_links.append(link)
            
            is_valid, resolved_path = check_link_validity(file_path, link)
            if not is_valid:
                broken_links.append({
                    **link,
                    'resolved_path': resolved_path
                })
    
    print(f"\n总共找到 {len(all_links)} 个本地链接")
    print(f"其中 {len(broken_links)} 个链接无效")
    
    if broken_links:
        print("\n无效链接列表:")
        print("-" * 60)
        
        # 按文件分组显示
        broken_by_file = {}
        for link in broken_links:
            file_name = os.path.relpath(link['source_file'], docs_dir)
            if file_name not in broken_by_file:
                broken_by_file[file_name] = []
            broken_by_file[file_name].append(link)
        
        for file_name, links in broken_by_file.items():
            print(f"\n文件: {file_name}")
            for link in links:
                print(f"  第{link['line']}行: [{link['text']}]({link['url']})")
                print(f"    期望路径: {link['resolved_path']}")
                print(f"    相对路径: {os.path.relpath(link['resolved_path'], docs_dir)}")
        
        print(f"\n建议:")
        print("1. 检查文件名拼写是否正确")
        print("2. 确认目标文件是否存在")
        print("3. 检查路径分隔符是否正确")
        print("4. 验证目录结构是否与链接路径匹配")
    else:
        print("\n所有本地链接都是有效的！")

if __name__ == "__main__":
    main()
