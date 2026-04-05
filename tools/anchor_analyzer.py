#!/usr/bin/env python3
"""
FormalMath项目docs/01-06分支锚点深度分析工具
检测各种锚点格式问题
"""

import re
import os
import json
from pathlib import Path
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


def check_anchor_issues(anchor):
    """
    检查锚点的各种问题
    返回问题列表
    """
    issues = []
    
    if not anchor:
        return ['空锚点']
    
    # 检查1: 包含下划线
    if '_' in anchor:
        issues.append('包含下划线')
    
    # 检查2: 包含空格
    if ' ' in anchor:
        issues.append('包含空格')
    
    # 检查3: 包含多个连续短横线
    if '--' in anchor:
        issues.append('连续短横线')
    
    # 检查4: 首尾短横线
    if anchor.startswith('-') or anchor.endswith('-'):
        issues.append('首尾短横线')
    
    # 检查5: 包含句点
    if '.' in anchor:
        issues.append('包含句点')
    
    # 检查6: 包含其他特殊字符
    if re.search(r'[^\w\u4e00-\u9fff\s.-]', anchor):
        issues.append('包含特殊字符')
    
    # 检查7: 大写字母（应该小写）
    if re.search(r'[A-Z]', anchor):
        issues.append('包含大写')
    
    # 检查8: 中文标点
    if re.search(r'[，。！？、；：""''（）【】《》]', anchor):
        issues.append('中文标点')
    
    return issues


def extract_explicit_anchors(content):
    """提取文档中显式定义的锚点 {#anchor}"""
    anchors = []
    # 匹配 {#anchor} 格式
    pattern = r'\{#([^}]+)\}'
    
    for match in re.finditer(pattern, content):
        anchor = match.group(1)
        line = content[:match.start()].count('\n') + 1
        context = content[max(0, match.start()-50):min(len(content), match.end()+50)]
        anchors.append({
            'anchor': anchor,
            'line': line,
            'context': context.replace('\n', ' ')
        })
    
    return anchors


def extract_headers_with_auto_anchors(content):
    """提取标题并自动生成GitHub风格锚点"""
    headers = []
    # 匹配Markdown标题: ## 标题内容
    pattern = r'^(#{1,6})\s+(.+?)$'
    
    for match in re.finditer(pattern, content, re.MULTILINE):
        level = len(match.group(1))
        title = match.group(2).strip()
        
        # 移除显式锚点标记
        title_clean = re.sub(r'\s*\{#[^}]+\}\s*$', '', title)
        
        # 生成GitHub风格锚点
        anchor = generate_github_anchor(title_clean)
        
        headers.append({
            'level': level,
            'title': title_clean,
            'anchor': anchor,
            'line': content[:match.start()].count('\n') + 1
        })
    
    return headers


def generate_github_anchor(title):
    """生成GitHub风格的锚点"""
    # 移除Markdown格式
    title = re.sub(r'\*\*|__|\*|_|`', '', title)
    # 转换为小写
    anchor = title.lower()
    # 替换空格为短横线
    anchor = re.sub(r'\s+', '-', anchor)
    # 移除标点符号
    anchor = re.sub(r'[^\w\u4e00-\u9fff-]', '', anchor)
    # 合并多个短横线
    anchor = re.sub(r'-+', '-', anchor)
    # 移除首尾短横线
    anchor = anchor.strip('-')
    return anchor


def extract_links(content):
    """提取文档中的所有内部链接"""
    links = []
    # 匹配 [文本](路径#锚点) 格式
    pattern = r'\[([^\]]+)\]\(([^)]+)\)'
    
    for match in re.finditer(pattern, content):
        text = match.group(1)
        url = match.group(2)
        
        # 解析链接
        if '#' in url:
            path, anchor = url.rsplit('#', 1)
        else:
            path = url
            anchor = None
        
        # 只处理内部链接或页内锚点
        if anchor and not url.startswith(('http://', 'https://', 'mailto:')):
            links.append({
                'text': text,
                'url': url,
                'path': path,
                'anchor': anchor,
                'line': content[:match.start()].count('\n') + 1
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


def analyze_documents(files):
    """深度分析所有文档"""
    results = {
        'files_analyzed': len(files),
        'explicit_anchors': [],
        'headers': [],
        'links': [],
        'issues_by_type': defaultdict(list),
        'issue_summary': defaultdict(int)
    }
    
    print(f"  正在分析 {len(files)} 个文件...")
    
    for idx, file_path in enumerate(files):
        if (idx + 1) % 100 == 0:
            print(f"    已处理 {idx + 1}/{len(files)} 个文件...")
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # 分析显式锚点
            explicit = extract_explicit_anchors(content)
            for a in explicit:
                issues = check_anchor_issues(a['anchor'])
                if issues:
                    results['explicit_anchors'].append({
                        'file': file_path,
                        'anchor': a['anchor'],
                        'line': a['line'],
                        'issues': issues
                    })
                    for issue in issues:
                        results['issues_by_type'][issue].append({
                            'file': file_path,
                            'anchor': a['anchor'],
                            'line': a['line']
                        })
                        results['issue_summary'][issue] += 1
            
            # 分析标题
            headers = extract_headers_with_auto_anchors(content)
            results['headers'].extend([{
                'file': file_path,
                **h
            } for h in headers])
            
            # 分析链接
            links = extract_links(content)
            results['links'].extend([{
                'source_file': file_path,
                **l
            } for l in links])
        
        except Exception as e:
            print(f"    错误处理 {file_path}: {e}")
    
    return results


def generate_report(results, output_path):
    """生成分析报告"""
    
    report = f"""# 锚点ID深度分析报告 - docs/01-06分支

**生成时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}

## 执行摘要

本次任务对FormalMath项目docs目录下的01-06分支进行了深度锚点分析。

### 分析范围

| 指标 | 数量 |
|------|------|
| 扫描文档数 | {results['files_analyzed']:,} |
| 显式锚点数 | {len(results['explicit_anchors']):,} |
| 标题总数 | {len(results['headers']):,} |
| 带锚点链接数 | {len(results['links']):,} |

### 问题汇总

| 问题类型 | 出现次数 |
|----------|----------|
"""
    
    for issue_type, count in sorted(results['issue_summary'].items(), key=lambda x: -x[1]):
        report += f"| {issue_type} | {count:,} |\n"
    
    total_issues = sum(results['issue_summary'].values())
    report += f"| **总计** | **{total_issues:,}** |\n"
    
    report += """
## 问题详情

"""
    
    # 每种问题类型的详情
    for issue_type in sorted(results['issues_by_type'].keys()):
        items = results['issues_by_type'][issue_type]
        report += f"### {issue_type} ({len(items)} 个)\n\n"
        report += "| 序号 | 文件 | 锚点 | 行号 |\n"
        report += "|------|------|------|------|\n"
        
        for idx, item in enumerate(items[:50], 1):  # 只显示前50个
            file_name = os.path.basename(item['file'])
            report += f"| {idx} | `{file_name}` | `{item['anchor']}` | {item['line']} |\n"
        
        if len(items) > 50:
            report += f"\n... 还有 {len(items) - 50} 个未显示\n"
        
        report += "\n"
    
    # 显式锚点统计
    report += """## 显式锚点使用统计

"""
    
    if results['explicit_anchors']:
        report += "| 序号 | 文件 | 锚点 | 问题 |\n"
        report += "|------|------|------|------|\n"
        
        for idx, item in enumerate(results['explicit_anchors'][:100], 1):
            file_name = os.path.basename(item['file'])
            issues = ', '.join(item['issues'])
            report += f"| {idx} | `{file_name}` | `{item['anchor']}` | {issues} |\n"
        
        if len(results['explicit_anchors']) > 100:
            report += f"\n... 还有 {len(results['explicit_anchors']) - 100} 个未显示\n"
    else:
        report += "未发现使用显式锚点的文档。\n"
    
    # 链接锚点分析
    report += f"""
## 链接锚点分析

共发现 {len(results['links']):,} 个带锚点的内部链接。

### 链接锚点示例（前50个）

| 序号 | 源文件 | 链接文本 | 锚点 |\n"
|------|--------|----------|------|\n"
"""
    
    for idx, link in enumerate(results['links'][:50], 1):
        file_name = os.path.basename(link['source_file'])
        text = link['text'][:20] + '...' if len(link['text']) > 20 else link['text']
        report += f"| {idx} | `{file_name}` | {text} | `{link['anchor']}` |\n"
    
    report += """
## 规范化建议

### 优先级1: 高影响问题

"""
    
    # 高优先级问题
    high_priority = ['包含空格', '包含下划线', '包含大写']
    for issue in high_priority:
        if issue in results['issue_summary']:
            report += f"- **{issue}**: {results['issue_summary'][issue]} 处需要修复\n"
    
    report += """
### 优先级2: 格式问题

"""
    
    medium_priority = ['包含句点', '连续短横线', '首尾短横线']
    for issue in medium_priority:
        if issue in results['issue_summary']:
            report += f"- **{issue}**: {results['issue_summary'][issue]} 处需要修复\n"
    
    report += """
### 优先级3: 特殊字符

"""
    
    low_priority = ['包含特殊字符', '中文标点']
    for issue in low_priority:
        if issue in results['issue_summary']:
            report += f"- **{issue}**: {results['issue_summary'][issue]} 处需要修复\n"
    
    report += """
## 规范化规则

推荐遵循以下锚点规范化规则：

1. **使用短横线连接**: 空格和下划线统一替换为 `-`
2. **统一小写**: 英文字母全部使用小写
3. **移除标点**: 移除句点、逗号等标点符号
4. **合并连续短横线**: `--` → `-`
5. **清理首尾**: 移除锚点两端的短横线
6. **保留中文**: 中文字符保持原样

### 规范化示例

| 原始锚点 | 规范化后 | 问题 |
|----------|----------|------|
| `Section_1_1` | `section-1-1` | 下划线转短横线，小写 |
| `第一章 引言` | `第一章-引言` | 空格转短横线 |
| `HTTP_Request` | `http-request` | 大写转小写 |
| `API.v2.Docs` | `apiv2docs` | 移除句点，小写 |
| `Test--Case` | `test-case` | 合并连续短横线 |
| `-section-` | `section` | 移除首尾短横线 |

---

**报告结束**

*生成工具*: `tools/anchor_analyzer.py`  
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
    print("FormalMath项目锚点深度分析工具")
    print("=" * 70)
    
    # 扫描文档
    print("\n[1/2] 扫描文档...")
    files = scan_documents(docs_dir)
    print(f"  找到 {len(files)} 个Markdown文件")
    
    # 分析文档
    print("\n[2/2] 深度分析锚点...")
    results = analyze_documents(files)
    
    # 生成报告
    print("\n[3/3] 生成报告...")
    generate_report(results, output_report)
    print(f"  报告已保存: {output_report}")
    
    print("\n" + "=" * 70)
    print("分析完成!")
    print("=" * 70)
    print(f"\n文档总数: {results['files_analyzed']:,}")
    print(f"显式锚点: {len(results['explicit_anchors']):,}")
    print(f"标题总数: {len(results['headers']):,}")
    print(f"链接总数: {len(results['links']):,}")
    print(f"\n问题汇总:")
    for issue_type, count in sorted(results['issue_summary'].items(), key=lambda x: -x[1]):
        print(f"  - {issue_type}: {count:,}")
    print("=" * 70)


if __name__ == '__main__':
    main()
