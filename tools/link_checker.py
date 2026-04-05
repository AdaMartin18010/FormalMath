#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalMath项目外部链接检查与修复工具 (优化版)
"""

import re
import os
import json
import time
from pathlib import Path
from collections import defaultdict

# 链接扫描结果存储
link_data = {
    "all_links": [],
    "link_by_file": defaultdict(list),
    "link_categories": defaultdict(list),
}

# 重要链接模式（优先修复）
IMPORTANT_PATTERNS = [
    r'.*math\.(mit|harvard|stanford|oxford|cam)\.ac.*',
    r'.*ocw\.mit\.edu.*',
    r'.*arxiv\.org.*',
    r'.*doi\.org.*',
    r'.*wikipedia\.org.*',
    r'.*ams\.org.*',
    r'.*maa\.org.*',
    r'.*lean-lang\.org.*',
    r'.*leanprover.*',
    r'.*oeis\.org.*',
    r'.*github\.com.*formalmath.*',
]

# 需要删除的链接模式（不重要）
DELETE_PATTERNS = [
    r'http://localhost.*',
    r'http://127\.0\.0\.1.*',
    r'http://example\.com.*',
    r'http://10\..*',
    r'http://api\.example\.com.*',
    r'http://backend.*',
    r'http://backend-service.*',
    r'http://.*\.local.*',
]

# 国际课程链接
COURSE_LINKS = [
    'math.mit.edu',
    'ocw.mit.edu',
    'math.harvard.edu',
    'math.stanford.edu',
    'math.ox.ac.uk',
    'maths.cam.ac.uk',
    'math.ethz.ch',
    'math.princeton.edu',
    'math.berkeley.edu',
    'math.ucla.edu',
    'math.cmu.edu',
    'math.nyu.edu',
]

# 数学资源链接
MATH_RESOURCES = [
    'arxiv.org',
    'oeis.org',
    'doi.org',
    'ams.org',
    'maa.org',
    'mathworld.wolfram.com',
    'mathoverflow.net',
    'math.stackexchange.com',
    'zbmath.org',
]

# 参考文献链接
REFERENCE_LINKS = [
    'en.wikipedia.org',
    'github.com/formalmath',
    'lean-lang.org',
    'leanprover.github.io',
    'ncatlab.org',
]


def extract_links_from_file(file_path):
    """从文件中提取所有http/https链接"""
    links = []
    try:
        with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
            # 匹配URL
            pattern = r'https?://[^\s\)\]\<\>\"\'\`\,\;]+'
            matches = re.finditer(pattern, content)
            for match in matches:
                url = match.group().rstrip('.,;:\'"`')
                if len(url) > 10:  # 过滤掉太短的URL
                    links.append({
                        'url': url,
                        'line': content[:match.start()].count('\n') + 1
                    })
    except Exception as e:
        pass
    return links


def categorize_link(url):
    """分类链接"""
    url_lower = url.lower()
    
    # 检查是否是本地/测试链接
    for pattern in DELETE_PATTERNS:
        if re.match(pattern, url, re.IGNORECASE):
            return 'local_test'
    
    # 检查是否是课程链接
    for domain in COURSE_LINKS:
        if domain in url_lower:
            return 'course'
    
    # 检查是否是数学资源
    for domain in MATH_RESOURCES:
        if domain in url_lower:
            return 'math_resource'
    
    # 检查是否是参考文献
    for domain in REFERENCE_LINKS:
        if domain in url_lower:
            return 'reference'
    
    # 检查是否是GitHub链接
    if 'github.com' in url_lower:
        return 'github'
    
    # 检查是否是npm/shields等开发资源
    if any(x in url_lower for x in ['npmjs', 'shields.io', 'badge']):
        return 'dev_badge'
    
    return 'other'


def is_important_link(url):
    """判断链接是否重要"""
    for pattern in IMPORTANT_PATTERNS:
        if re.match(pattern, url, re.IGNORECASE):
            return True
    return False


def scan_project(project_dir):
    """扫描项目中的所有文件 - 优化版"""
    project_path = Path(project_dir)
    
    # 要扫描的文件类型 - 主要关注Markdown文件
    extensions = ['.md']
    
    # 排除的目录
    exclude_dirs = {'.git', 'node_modules', '__pycache__', '.venv', 'venv', 
                    'dist', 'build', 'vendor', '.github', 'tools', 'output'}
    
    all_links_info = []
    file_count = 0
    
    # 只扫描指定目录
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
                
                file_count += 1
                if file_count % 500 == 0:
                    print(f"  已扫描 {file_count} 个文件...")
                
                try:
                    links = extract_links_from_file(file_path)
                    for link_info in links:
                        all_links_info.append({
                            'file': str(file_path.relative_to(project_path)),
                            'url': link_info['url'],
                            'line': link_info['line'],
                            'category': categorize_link(link_info['url']),
                            'is_important': is_important_link(link_info['url'])
                        })
                except Exception as e:
                    pass
    
    print(f"总共扫描了 {file_count} 个文件")
    return all_links_info


def analyze_links(links_info):
    """分析链接并生成报告"""
    report = {
        'total': len(links_info),
        'by_category': defaultdict(list),
        'by_file': defaultdict(list),
        'unique_urls': set(),
        'course_links': [],
        'math_resource_links': [],
        'reference_links': [],
        'github_links': [],
        'dev_badge_links': [],
        'local_test_links': [],
        'other_links': [],
    }
    
    for info in links_info:
        url = info['url']
        category = info['category']
        
        report['by_category'][category].append(info)
        report['by_file'][info['file']].append(info)
        report['unique_urls'].add(url)
        
        # 分类存储
        if category == 'course':
            report['course_links'].append(info)
        elif category == 'math_resource':
            report['math_resource_links'].append(info)
        elif category == 'reference':
            report['reference_links'].append(info)
        elif category == 'github':
            report['github_links'].append(info)
        elif category == 'dev_badge':
            report['dev_badge_links'].append(info)
        elif category == 'local_test':
            report['local_test_links'].append(info)
        else:
            report['other_links'].append(info)
    
    return report


def generate_markdown_report(report, output_path):
    """生成Markdown格式的报告"""
    lines = []
    
    lines.append("# FormalMath项目外部链接修复报告")
    lines.append("")
    lines.append(f"**生成时间**: {time.strftime('%Y-%m-%d %H:%M:%S')}")
    lines.append("")
    
    # 统计概览
    lines.append("## 1. 统计概览")
    lines.append("")
    lines.append(f"- **总链接数**: {report['total']}")
    lines.append(f"- **唯一URL数**: {len(report['unique_urls'])}")
    lines.append("")
    
    # 分类统计表
    lines.append("| 类别 | 数量 | 处理策略 |")
    lines.append("|------|------|----------|")
    lines.append(f"| 国际课程链接 | {len(report['course_links'])} | 优先保留并验证 |")
    lines.append(f"| 数学资源链接 | {len(report['math_resource_links'])} | 保留并验证 |")
    lines.append(f"| 参考文献链接 | {len(report['reference_links'])} | 保留 |")
    lines.append(f"| GitHub链接 | {len(report['github_links'])} | 保留 |")
    lines.append(f"| 开发徽章链接 | {len(report['dev_badge_links'])} | 保留（如可用）|")
    lines.append(f"| 本地/测试链接 | {len(report['local_test_links'])} | **删除** |")
    lines.append(f"| 其他链接 | {len(report['other_links'])} | 逐一验证 |")
    lines.append("")
    
    # 保留链接详情 - 国际课程链接
    if report['course_links']:
        lines.append("## 2. 国际课程链接（优先修复）")
        lines.append("")
        seen = set()
        for info in report['course_links']:
            url = info['url']
            if url not in seen:
                seen.add(url)
                lines.append(f"- `{url}`")
                lines.append(f"  - 位置: `{info['file']}` (第 {info['line']} 行)")
        lines.append("")
    
    # 数学资源链接
    if report['math_resource_links']:
        lines.append("## 3. 数学资源链接")
        lines.append("")
        seen = set()
        count = 0
        for info in report['math_resource_links']:
            url = info['url']
            if url not in seen and count < 50:
                seen.add(url)
                count += 1
                lines.append(f"- `{url}`")
                lines.append(f"  - 位置: `{info['file']}` (第 {info['line']} 行)")
        lines.append("")
    
    # 参考文献链接
    if report['reference_links']:
        lines.append("## 4. 参考文献链接")
        lines.append("")
        seen = set()
        count = 0
        for info in report['reference_links']:
            url = info['url']
            if url not in seen and count < 50:
                seen.add(url)
                count += 1
                lines.append(f"- `{url}`")
                lines.append(f"  - 位置: `{info['file']}` (第 {info['line']} 行)")
        lines.append("")
    
    # GitHub链接
    if report['github_links']:
        lines.append("## 5. GitHub相关链接")
        lines.append("")
        seen = set()
        count = 0
        for info in report['github_links']:
            url = info['url']
            if url not in seen and count < 30:
                seen.add(url)
                count += 1
                lines.append(f"- `{url}`")
                lines.append(f"  - 位置: `{info['file']}` (第 {info['line']} 行)")
        lines.append("")
    
    # 建议删除链接
    if report['local_test_links']:
        lines.append("## 6. 建议删除链接（本地/测试链接）")
        lines.append("")
        seen = set()
        for info in report['local_test_links']:
            url = info['url']
            if url not in seen:
                seen.add(url)
                lines.append(f"- `{url}`")
                lines.append(f"  - 位置: `{info['file']}` (第 {info['line']} 行)")
        lines.append("")
    
    # 其他链接
    if report['other_links']:
        lines.append("## 7. 其他链接（需逐一验证）")
        lines.append("")
        seen = set()
        count = 0
        for info in report['other_links']:
            url = info['url']
            if url not in seen and count < 30:
                seen.add(url)
                count += 1
                lines.append(f"- `{url}`")
                lines.append(f"  - 位置: `{info['file']}` (第 {info['line']} 行)")
        lines.append("")
    
    # 修复建议
    lines.append("## 8. 修复建议")
    lines.append("")
    lines.append("### 8.1 优先修复")
    lines.append("")
    lines.append("1. **国际课程链接** - MIT、Harvard、Stanford等数学课程链接")
    lines.append("2. **数学资源链接** - arXiv、DOI、AMS、MAA等")
    lines.append("3. **参考文献链接** - Wikipedia、GitHub项目页面等")
    lines.append("")
    lines.append("### 8.2 处理策略")
    lines.append("")
    lines.append("| 链接类型 | 处理策略 |")
    lines.append("|---------|---------|")
    lines.append("| 可访问的重要链接 | **保留** |")
    lines.append("| 不可访问但重要的链接 | **标记为'需更新'** |")
    lines.append("| 不可访问且不重要的链接 | **删除** |")
    lines.append("| 本地/测试链接 | **删除** |")
    lines.append("")
    
    # 涉及文件列表
    lines.append("## 9. 涉及文件列表（前30个）")
    lines.append("")
    sorted_files = sorted(report['by_file'].items(), key=lambda x: len(x[1]), reverse=True)
    for file_path, links in sorted_files[:30]:
        lines.append(f"- `{file_path}` - {len(links)} 个链接")
    lines.append("")
    
    # 修复统计
    total_course = len(report['course_links'])
    total_math_resource = len(report['math_resource_links'])
    total_reference = len(report['reference_links'])
    total_local_test = len(report['local_test_links'])
    
    lines.append("## 10. 修复统计")
    lines.append("")
    lines.append(f"- **国际课程链接**: {total_course} 个")
    lines.append(f"- **数学资源链接**: {total_math_resource} 个")
    lines.append(f"- **参考文献链接**: {total_reference} 个")
    lines.append(f"- **待删除链接**: {total_local_test} 个")
    lines.append(f"- **总计处理**: {total_course + total_math_resource + total_reference + total_local_test} 个链接")
    lines.append("")
    
    lines.append("---")
    lines.append("")
    lines.append("*报告由FormalMath外部链接检查工具自动生成*")
    
    with open(output_path, 'w', encoding='utf-8') as f:
        f.write('\n'.join(lines))
    
    return output_path


def main():
    """主函数"""
    project_dir = r"g:\_src\FormalMath"
    output_path = os.path.join(project_dir, "00-外部链接修复报告.md")
    
    print("开始扫描FormalMath项目中的外部链接...")
    links_info = scan_project(project_dir)
    print(f"扫描完成，共发现 {len(links_info)} 个链接")
    
    print("正在分析链接...")
    report = analyze_links(links_info)
    
    print("正在生成报告...")
    report_path = generate_markdown_report(report, output_path)
    print(f"报告已生成: {report_path}")
    
    # 打印统计信息
    print("\n=== 统计摘要 ===")
    print(f"总链接数: {report['total']}")
    print(f"唯一URL数: {len(report['unique_urls'])}")
    print(f"国际课程链接: {len(report['course_links'])}")
    print(f"数学资源链接: {len(report['math_resource_links'])}")
    print(f"参考文献链接: {len(report['reference_links'])}")
    print(f"GitHub链接: {len(report['github_links'])}")
    print(f"开发徽章链接: {len(report['dev_badge_links'])}")
    print(f"本地/测试链接: {len(report['local_test_links'])}")
    print(f"其他链接: {len(report['other_links'])}")
    
    return report


if __name__ == "__main__":
    main()
