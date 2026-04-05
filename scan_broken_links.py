#!/usr/bin/env python3
"""
扫描FormalMath项目中的断链
"""
import os
import re
import json
from pathlib import Path
from urllib.parse import urlparse

# 目标分支目录
TARGET_DIRS = [
    "docs/05-数论",
    "docs/06-概率论与统计",
    "docs/07-数理逻辑",
    "docs/08-计算数学",
    "docs/09-组合数学与离散数学",
    "docs/10-应用数学",
    "docs/11-高级数学",
]

# 存储所有发现的文件
all_files = set()
# 存储所有链接
all_links = []
# 存储断链
broken_links = []


def get_all_markdown_files():
    """获取所有Markdown文件"""
    files = set()
    for target_dir in TARGET_DIRS:
        if os.path.exists(target_dir):
            for root, _, filenames in os.walk(target_dir):
                for filename in filenames:
                    if filename.endswith('.md'):
                        full_path = os.path.join(root, filename)
                        files.add(full_path)
                        # 同时存储相对路径
                        rel_path = os.path.relpath(full_path)
                        files.add(rel_path)
                        # 存储正斜杠版本
                        files.add(rel_path.replace('\\', '/'))
    return files


def extract_links_from_file(file_path):
    """从Markdown文件中提取链接"""
    links = []
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
    except Exception as e:
        print(f"Error reading {file_path}: {e}")
        return links

    # 匹配Markdown链接 [text](url)
    md_pattern = r'\[([^\]]+)\]\(([^)]+)\)'
    # 匹配HTML链接 <a href="url">
    html_pattern = r'<a\s+href=["\']([^"\']+)["\']'
    # 匹配图片链接 ![alt](url)
    img_pattern = r'!\[([^\]]*)\]\(([^)]+)\)'

    for match in re.finditer(md_pattern, content):
        link_text = match.group(1)
        url = match.group(2)
        links.append({
            'type': 'markdown',
            'text': link_text,
            'url': url,
            'line': content[:match.start()].count('\n') + 1,
            'file': file_path
        })

    for match in re.finditer(html_pattern, content):
        url = match.group(1)
        links.append({
            'type': 'html',
            'text': '',
            'url': url,
            'line': content[:match.start()].count('\n') + 1,
            'file': file_path
        })

    for match in re.finditer(img_pattern, content):
        alt_text = match.group(1)
        url = match.group(2)
        links.append({
            'type': 'image',
            'text': alt_text,
            'url': url,
            'line': content[:match.start()].count('\n') + 1,
            'file': file_path
        })

    return links


def is_external_url(url):
    """检查是否是外部URL"""
    return url.startswith('http://') or url.startswith('https://') or url.startswith('ftp://') or url.startswith('mailto:')


def is_anchor_only(url):
    """检查是否只是锚点链接"""
    return url.startswith('#')


def resolve_link(source_file, link_url):
    """解析链接为绝对路径"""
    if is_external_url(link_url) or is_anchor_only(link_url):
        return None

    # 移除锚点
    if '#' in link_url:
        link_url = link_url.split('#')[0]

    if not link_url:
        return None

    # 获取源文件所在目录
    source_dir = os.path.dirname(source_file)

    # 解析链接
    if os.path.isabs(link_url):
        resolved = link_url.lstrip('/')
    else:
        resolved = os.path.normpath(os.path.join(source_dir, link_url))

    return resolved


def check_link_exists(link_info, all_files):
    """检查链接是否存在"""
    url = link_info['url']

    # 跳过外部链接（可能有网络问题）
    if is_external_url(url):
        return True, "external"

    # 跳过纯锚点链接
    if is_anchor_only(url):
        return True, "anchor"

    # 解析链接
    resolved = resolve_link(link_info['file'], url)
    if resolved is None:
        return True, "unknown"

    # 检查文件是否存在
    # 尝试多种路径格式
    variants = [
        resolved,
        resolved.replace('/', '\\'),
        resolved.replace('\\', '/'),
        resolved + '.md',
        (resolved + '.md').replace('/', '\\'),
        (resolved + '.md').replace('\\', '/'),
    ]

    for variant in variants:
        if variant in all_files:
            return True, "exists"
        if os.path.exists(variant):
            return True, "exists"

    return False, "not_found"


def main():
    print("开始扫描断链...")

    # 获取所有文件
    print("收集所有Markdown文件...")
    global all_files
    all_files = get_all_markdown_files()
    print(f"找到 {len(all_files)} 个文件")

    # 提取所有链接
    print("提取链接...")
    for target_dir in TARGET_DIRS:
        if os.path.exists(target_dir):
            for root, _, filenames in os.walk(target_dir):
                for filename in filenames:
                    if filename.endswith('.md'):
                        file_path = os.path.join(root, filename)
                        links = extract_links_from_file(file_path)
                        all_links.extend(links)

    print(f"找到 {len(all_links)} 个链接")

    # 检查每个链接
    print("检查链接有效性...")
    for link in all_links:
        exists, status = check_link_exists(link, all_files)
        if not exists:
            broken_links.append({
                **link,
                'status': status
            })

    print(f"发现 {len(broken_links)} 个断链")

    # 保存结果
    result = {
        'total_links': len(all_links),
        'broken_links': len(broken_links),
        'links': broken_links
    }

    with open('broken_links_report.json', 'w', encoding='utf-8') as f:
        json.dump(result, f, ensure_ascii=False, indent=2)

    print("报告已保存到 broken_links_report.json")

    # 按文件分组显示断链
    by_file = {}
    for link in broken_links:
        file = link['file']
        if file not in by_file:
            by_file[file] = []
        by_file[file].append(link)

    print("\n=== 断链详情 ===")
    for file, links in sorted(by_file.items()):
        print(f"\n文件: {file}")
        for link in links:
            print(f"  行 {link['line']}: [{link['text']}] -> {link['url']}")


if __name__ == '__main__':
    main()
