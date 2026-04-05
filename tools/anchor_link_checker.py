#!/usr/bin/env python3
"""
FormalMath项目docs/01-06分支链接-锚点匹配检查工具
检测断链和锚点不匹配问题
"""

import re
import os
from collections import defaultdict
from datetime import datetime

# 要处理的分支
BRANCHES = [
    '01-基础数学',
    '02-代数结构', 
    '03-分析学',
    '04-几何与拓扑',
    '05-数论',
    '06-概率论与统计'
]


def generate_github_anchor(title):
    """生成GitHub风格的锚点"""
    if not title:
        return ''
    
    # 移除Markdown格式
    title = re.sub(r'\*\*|__|\*|_|`', '', title)
    
    # 转换为小写
    anchor = title.lower()
    
    # 替换空格为短横线
    anchor = re.sub(r'\s+', '-', anchor)
    
    # 移除标点符号（保留中文、字母、数字、短横线）
    anchor = re.sub(r'[^\w\u4e00-\u9fff-]', '', anchor)
    
    # 合并多个短横线
    anchor = re.sub(r'-+', '-', anchor)
    
    # 移除首尾短横线
    anchor = anchor.strip('-')
    
    return anchor


def normalize_anchor(anchor):
    """规范化锚点用于比较"""
    if not anchor:
        return ''
    
    # 转换为小写
    anchor = anchor.lower()
    
    # 替换下划线为短横线
    anchor = anchor.replace('_', '-')
    
    # 合并多个短横线
    anchor = re.sub(r'-+', '-', anchor)
    
    # 移除首尾短横线
    anchor = anchor.strip('-')
    
    return anchor


def extract_headers(content):
    """提取文档中的所有标题"""
    headers = []
    pattern = r'^(#{1,6})\s+(.+?)(?:\s+\{#[^}]+\})?\s*$'
    
    for match in re.finditer(pattern, content, re.MULTILINE):
        level = len(match.group(1))
        title = match.group(2).strip()
        # 移除显式锚点标记
        title_clean = re.sub(r'\s*\{#[^}]+\}\s*$', '', title)
        
        anchor = generate_github_anchor(title_clean)
        
        headers.append({
            'level': level,
            'title': title_clean,
            'anchor': anchor,
            'normalized': normalize_anchor(anchor),
            'line': content[:match.start()].count('\n') + 1
        })
    
    return headers


def extract_links(content, current_file):
    """提取文档中的所有链接"""
    links = []
    pattern = r'\[([^\]]*)\]\(([^)]+)\)'
    
    for match in re.finditer(pattern, content):
        text = match.group(1)
        url = match.group(2)
        line = content[:match.start()].count('\n') + 1
        
        # 忽略外部链接
        if url.startswith(('http://', 'https://', 'mailto:')):
            continue
        
        # 解析链接
        if '#' in url:
            path_part, anchor = url.rsplit('#', 1)
        else:
            path_part = url
            anchor = None
        
        links.append({
            'text': text,
            'url': url,
            'path': path_part,
            'anchor': anchor,
            'line': line,
            'is_page_anchor': url.startswith('#'),
            'is_relative': not path_part.startswith('/')
        })
    
    return links


def scan_documents(docs_dir):
    """扫描所有文档"""
    all_files = []
    
    for branch in BRANCHES:
        branch_dir = os.path.join(docs_dir, branch)
        if os.path.exists(branch_dir):
            for root, dirs, files in os.walk(branch_dir):
                for file in files:
                    if file.endswith('.md'):
                        file_path = os.path.join(root, file)
                        all_files.append(file_path)
    
    return sorted(all_files)


def analyze_links_and_anchors(files):
    """分析链接和锚点的匹配情况"""
    
    # 第一阶段：收集所有文件的标题信息
    file_headers = {}  # file_path -> list of headers
    all_anchors = defaultdict(list)  # normalized_anchor -> list of (file, header)
    
    print("  第一阶段：收集标题信息...")
    for idx, file_path in enumerate(files):
        if (idx + 1) % 100 == 0:
            print(f"    已处理 {idx + 1}/{len(files)} 个文件...")
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            headers = extract_headers(content)
            file_headers[file_path] = headers
            
            for header in headers:
                all_anchors[header['normalized']].append({
                    'file': file_path,
                    'header': header
                })
        
        except Exception as e:
            print(f"    错误读取 {file_path}: {e}")
    
    # 第二阶段：分析链接
    print("\n  第二阶段：分析链接...")
    results = {
        'total_links': 0,
        'page_anchor_links': [],  # 页内锚点链接
        'cross_file_links': [],   # 跨文件链接
        'broken_links': [],       # 断链
        'potential_issues': [],   # 潜在问题
        'file_headers': file_headers
    }
    
    for idx, file_path in enumerate(files):
        if (idx + 1) % 100 == 0:
            print(f"    已分析 {idx + 1}/{len(files)} 个文件的链接...")
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            links = extract_links(content, file_path)
            
            for link in links:
                results['total_links'] += 1
                
                if link['is_page_anchor']:
                    # 页内锚点链接
                    results['page_anchor_links'].append({
                        'source': file_path,
                        **link
                    })
                    
                    # 检查锚点是否存在
                    if link['anchor']:
                        normalized = normalize_anchor(link['anchor'])
                        current_headers = file_headers.get(file_path, [])
                        
                        # 检查是否匹配
                        found = False
                        for h in current_headers:
                            if h['anchor'] == link['anchor'] or h['normalized'] == normalized:
                                found = True
                                break
                        
                        if not found:
                            results['broken_links'].append({
                                'source': file_path,
                                'target': file_path,
                                'anchor': link['anchor'],
                                'line': link['line'],
                                'url': link['url'],
                                'type': 'page_anchor_not_found'
                            })
                
                elif link['anchor']:
                    # 跨文件锚点链接
                    results['cross_file_links'].append({
                        'source': file_path,
                        **link
                    })
                    
                    # 解析目标文件路径
                    if link['path']:
                        if os.path.isabs(link['path']):
                            target_file = link['path']
                        else:
                            base_dir = os.path.dirname(file_path)
                            target_file = os.path.normpath(os.path.join(base_dir, link['path']))
                    else:
                        target_file = file_path
                    
                    # 检查目标文件是否存在
                    if target_file in file_headers:
                        target_headers = file_headers[target_file]
                        normalized = normalize_anchor(link['anchor'])
                        
                        # 检查锚点是否匹配
                        found = False
                        for h in target_headers:
                            if h['anchor'] == link['anchor'] or h['normalized'] == normalized:
                                found = True
                                break
                        
                        if not found:
                            results['broken_links'].append({
                                'source': file_path,
                                'target': target_file,
                                'anchor': link['anchor'],
                                'line': link['line'],
                                'url': link['url'],
                                'type': 'cross_file_anchor_not_found'
                            })
                    else:
                        # 目标文件不存在
                        results['broken_links'].append({
                            'source': file_path,
                            'target': target_file,
                            'anchor': link['anchor'],
                            'line': link['line'],
                            'url': link['url'],
                            'type': 'target_file_not_found'
                        })
        
        except Exception as e:
            print(f"    错误分析链接 {file_path}: {e}")
    
    return results


def generate_report(results, output_path):
    """生成分析报告"""
    
    report = f"""# 锚点ID规范化报告 - docs/01-06分支

**生成时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}

## 执行摘要

本次任务对FormalMath项目docs目录下的01-06分支进行了全面的链接-锚点匹配分析。

### 分析范围

| 指标 | 数量 |
|------|------|
| 扫描文档数 | {len(results['file_headers']):,} |
| 标题总数 | {sum(len(h) for h in results['file_headers'].values()):,} |
| 链接总数 | {results['total_links']:,} |
| 页内锚点链接 | {len(results['page_anchor_links']):,} |
| 跨文件锚点链接 | {len(results['cross_file_links']):,} |

### 断链统计

| 断链类型 | 数量 |
|----------|------|
"""
    
    broken_by_type = defaultdict(list)
    for link in results['broken_links']:
        broken_by_type[link['type']].append(link)
    
    for link_type, links in sorted(broken_by_type.items()):
        report += f"| {link_type} | {len(links):,} |\n"
    
    report += f"| **总计** | **{len(results['broken_links']):,}** |\n"
    
    # 断链详情
    report += """
## 断链详情

### 页内锚点未找到

"""
    
    page_broken = broken_by_type.get('page_anchor_not_found', [])
    if page_broken:
        report += "| 序号 | 源文件 | 断链锚点 | 行号 |\n"
        report += "|------|--------|----------|------|\n"
        for idx, link in enumerate(page_broken[:100], 1):
            file_name = os.path.basename(link['source'])
            report += f"| {idx} | `{file_name}` | `{link['anchor']}` | {link['line']} |\n"
        
        if len(page_broken) > 100:
            report += f"\n... 还有 {len(page_broken) - 100} 个未显示\n"
    else:
        report += "未发现页内锚点断链。\n"
    
    report += """
### 跨文件锚点未找到

"""
    
    cross_broken = broken_by_type.get('cross_file_anchor_not_found', [])
    if cross_broken:
        report += "| 序号 | 源文件 | 目标文件 | 断链锚点 | 行号 |\n"
        report += "|------|--------|----------|----------|------|\n"
        for idx, link in enumerate(cross_broken[:100], 1):
            source_name = os.path.basename(link['source'])
            target_name = os.path.basename(link['target']) if link['target'] else '-'
            report += f"| {idx} | `{source_name}` | `{target_name}` | `{link['anchor']}` | {link['line']} |\n"
        
        if len(cross_broken) > 100:
            report += f"\n... 还有 {len(cross_broken) - 100} 个未显示\n"
    else:
        report += "未发现跨文件锚点断链。\n"
    
    report += """
### 目标文件未找到

"""
    
    file_broken = broken_by_type.get('target_file_not_found', [])
    if file_broken:
        report += "| 序号 | 源文件 | 目标路径 | 锚点 | 行号 |\n"
        report += "|------|--------|----------|------|------|\n"
        for idx, link in enumerate(file_broken[:50], 1):
            source_name = os.path.basename(link['source'])
            target = link['target'] if link['target'] else '-'
            anchor = link['anchor'] if link['anchor'] else '-'
            report += f"| {idx} | `{source_name}` | `{target}` | `{anchor}` | {link['line']} |\n"
        
        if len(file_broken) > 50:
            report += f"\n... 还有 {len(file_broken) - 50} 个未显示\n"
    else:
        report += "未发现目标文件缺失。\n"
    
    # 常见断链锚点
    broken_anchors = defaultdict(int)
    for link in results['broken_links']:
        if link['anchor']:
            broken_anchors[link['anchor']] += 1
    
    report += """
## 常见断链锚点（Top 30）

| 锚点 | 断链次数 |
|------|----------|
"""
    
    for anchor, count in sorted(broken_anchors.items(), key=lambda x: -x[1])[:30]:
        report += f"| `{anchor}` | {count} |\n"
    
    # 断链最多的文件
    broken_by_file = defaultdict(int)
    for link in results['broken_links']:
        broken_by_file[link['source']] += 1
    
    report += """
## 断链最多的文件（Top 20）

| 文件 | 断链数 |
|------|--------|
"""
    
    for file_path, count in sorted(broken_by_file.items(), key=lambda x: -x[1])[:20]:
        file_name = os.path.basename(file_path)
        report += f"| `{file_name}` | {count} |\n"
    
    report += f"""
## 锚点规范化建议

基于分析结果，建议采取以下规范化措施：

### 1. 锚点格式统一

- 统一使用小写字母
- 使用短横线 `-` 替代下划线 `_`
- 移除多余的空格
- 合并连续的短横线

### 2. 链接修复策略

对于发现的 {len(results['broken_links']):,} 个断链：

1. **自动修复**: 对于格式问题（大小写、短横线等）可以自动修复
2. **手动修复**: 对于锚点不存在的情况需要手动检查
3. **批量更新**: 对于常见断链锚点，批量更新所有引用

### 3. 规范化规则

```
原始锚点 → 规范化后
Section_1 → section-1
Chapter One → chapter-one
API.Docs → api-docs
Test__Case → test-case
UpperCase → uppercase
```

### 4. 持续集成建议

1. 在CI中加入链接检查步骤
2. 提交前自动规范化锚点
3. 定期运行全站链接检查

---

**报告结束**

*生成工具*: `tools/anchor_link_checker.py`  
*处理时间*: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
"""
    
    with open(output_path, 'w', encoding='utf-8') as f:
        f.write(report)
    
    return report


def main():
    """主函数"""
    docs_dir = 'docs'
    output_report = '00-锚点规范化报告-分支01-06.md'
    
    print("=" * 70)
    print("FormalMath项目链接-锚点匹配检查工具")
    print("=" * 70)
    
    # 扫描文档
    print("\n[1/2] 扫描文档...")
    files = scan_documents(docs_dir)
    print(f"  找到 {len(files)} 个Markdown文件")
    
    # 分析链接和锚点
    print("\n[2/2] 分析链接和锚点匹配...")
    results = analyze_links_and_anchors(files)
    
    # 生成报告
    print("\n[3/3] 生成报告...")
    generate_report(results, output_report)
    print(f"  报告已保存: {output_report}")
    
    print("\n" + "=" * 70)
    print("分析完成!")
    print("=" * 70)
    print(f"\n文档总数: {len(results['file_headers']):,}")
    print(f"标题总数: {sum(len(h) for h in results['file_headers'].values()):,}")
    print(f"链接总数: {results['total_links']:,}")
    print(f"页内锚点链接: {len(results['page_anchor_links']):,}")
    print(f"跨文件锚点链接: {len(results['cross_file_links']):,}")
    print(f"\n断链总数: {len(results['broken_links']):,}")
    print("=" * 70)


if __name__ == '__main__':
    main()
