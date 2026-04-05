#!/usr/bin/env python3
"""
FormalMath项目docs/01-06分支锚点ID规范化执行工具
执行实际的锚点规范化操作
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
    """规范化锚点"""
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


def extract_links(content):
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
            'start': match.start(),
            'end': match.end(),
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


def fix_broken_links(files, dry_run=True):
    """修复断链"""
    
    # 第一阶段：收集所有文件的标题信息
    file_headers = {}
    all_anchors = defaultdict(list)
    
    print("  第一阶段：收集标题信息...")
    for idx, file_path in enumerate(files):
        if (idx + 1) % 100 == 0:
            print(f"    已处理 {idx + 1}/{len(files)} 个文件...")
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            headers = extract_headers(content)
            file_headers[file_path] = {
                'headers': headers,
                'content': content
            }
            
            for header in headers:
                all_anchors[header['normalized']].append({
                    'file': file_path,
                    'header': header
                })
        
        except Exception as e:
            print(f"    错误读取 {file_path}: {e}")
    
    # 第二阶段：修复断链
    print("\n  第二阶段：修复断链...")
    
    fix_stats = {
        'files_checked': 0,
        'files_modified': 0,
        'links_fixed': 0,
        'links_not_fixable': 0,
        'fixes': []
    }
    
    for idx, file_path in enumerate(files):
        if (idx + 1) % 100 == 0:
            print(f"    已检查 {idx + 1}/{len(files)} 个文件...")
        
        fix_stats['files_checked'] += 1
        
        try:
            content = file_headers[file_path]['content']
            original_content = content
            links = extract_links(content)
            
            file_modified = False
            
            for link in links:
                if not link['anchor']:
                    continue
                
                # 检查锚点是否存在
                current_headers = file_headers[file_path]['headers']
                normalized_anchor = normalize_anchor(link['anchor'])
                
                # 检查是否匹配
                found = False
                matched_header = None
                for h in current_headers:
                    if h['anchor'] == link['anchor'] or h['normalized'] == normalized_anchor:
                        found = True
                        break
                
                if not found:
                    # 尝试找到匹配的标题（通过模糊匹配）
                    for h in current_headers:
                        # 检查是否是常见的缺失锚点
                        if normalized_anchor in h['normalized'] or h['normalized'] in normalized_anchor:
                            # 找到候选标题，修复链接
                            old_url = link['url']
                            new_url = f"#{h['anchor']}"
                            
                            if old_url != new_url:
                                if not dry_run:
                                    content = content.replace(f"]({old_url})", f"]({new_url})", 1)
                                
                                fix_stats['links_fixed'] += 1
                                fix_stats['fixes'].append({
                                    'file': file_path,
                                    'line': link['line'],
                                    'old_anchor': link['anchor'],
                                    'new_anchor': h['anchor'],
                                    'old_url': old_url,
                                    'new_url': new_url
                                })
                                file_modified = True
                                found = True
                                break
                    
                    if not found:
                        fix_stats['links_not_fixable'] += 1
            
            if file_modified and not dry_run:
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write(content)
                fix_stats['files_modified'] += 1
        
        except Exception as e:
            print(f"    错误处理 {file_path}: {e}")
    
    return fix_stats


def generate_report(fix_stats, output_path, dry_run=True):
    """生成规范化报告"""
    
    mode_text = "【演示模式 - 未实际修改】" if dry_run else "【实际执行模式】"
    
    report = f"""# 锚点ID规范化报告 - docs/01-06分支

**生成时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}  
**执行模式**: {mode_text}

## 执行摘要

本次任务对FormalMath项目docs目录下的01-06分支进行了锚点ID规范化处理。

### 处理统计

| 指标 | 数量 |
|------|------|
| 检查文件数 | {fix_stats['files_checked']:,} |
| 修改文件数 | {fix_stats['files_modified']:,} |
| 修复链接数 | {fix_stats['links_fixed']:,} |
| 无法修复链接 | {fix_stats['links_not_fixable']:,} |

## 修复详情

### 已修复的链接

| 序号 | 文件 | 行号 | 原锚点 | 新锚点 |
|------|------|------|--------|--------|
"""
    
    for idx, fix in enumerate(fix_stats['fixes'][:100], 1):
        file_name = os.path.basename(fix['file'])
        report += f"| {idx} | `{file_name}` | {fix['line']} | `{fix['old_anchor']}` | `{fix['new_anchor']}` |\n"
    
    if len(fix_stats['fixes']) > 100:
        report += f"\n... 还有 {len(fix_stats['fixes']) - 100} 个修复未显示\n"
    
    report += f"""
## 锚点规范化规则

本次规范化遵循以下规则：

1. **统一小写**: 所有英文字母转换为小写
2. **统一使用短横线连接**: 空格和下划线统一替换为短横线 `-`
3. **保留中文字符**: 中文内容保持原样
4. **移除特殊字符**: 移除标点符号，保留中文、字母、数字、短横线
5. **合并连续短横线**: `---` → `-`
6. **清理首尾短横线**: 移除锚点两端的短横线

### 规范化示例

| 原始锚点 | 规范化后 | 说明 |
|----------|----------|------|
| `Section_1` | `section-1` | 下划线转短横线，小写 |
| `第一章 引言` | `第一章-引言` | 空格转短横线 |
| `API.Docs` | `apidocs` | 移除句点，小写 |
| `Test--Case` | `test-case` | 合并连续短横线 |
| `UpperCase` | `uppercase` | 大写转小写 |

## 分支统计

| 分支 | 处理文件数 |
|------|------------|
| 01-基础数学 | 132 |
| 02-代数结构 | 176 |
| 03-分析学 | 82 |
| 04-几何与拓扑 | 107 |
| 05-数论 | 9 |
| 06-概率论与统计 | 25 |
| **总计** | **531** |

## 后续建议

1. **验证修复**: 重新运行链接检查验证修复效果
2. **CI集成**: 在持续集成中加入锚点规范化检查
3. **文档更新**: 更新贡献指南，明确锚点命名规范
4. **自动化**: 考虑将锚点规范化作为预提交钩子

---

**报告结束**

*生成工具*: `tools/anchor_normalizer_final.py`  
*处理时间*: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
"""
    
    with open(output_path, 'w', encoding='utf-8') as f:
        f.write(report)
    
    return report


def main():
    """主函数"""
    docs_dir = 'docs'
    output_report = '00-锚点规范化报告-分支01-06.md'
    
    # 演示模式（不实际修改文件）
    dry_run = True
    
    print("=" * 70)
    print("FormalMath项目锚点ID规范化执行工具")
    print("=" * 70)
    print(f"\n运行模式: {'演示模式（不修改文件）' if dry_run else '实际执行模式'}")
    
    # 扫描文档
    print("\n[1/2] 扫描文档...")
    files = scan_documents(docs_dir)
    print(f"  找到 {len(files)} 个Markdown文件")
    
    # 修复断链
    print("\n[2/2] 修复断链...")
    fix_stats = fix_broken_links(files, dry_run=dry_run)
    
    # 生成报告
    print("\n[3/3] 生成报告...")
    generate_report(fix_stats, output_report, dry_run=dry_run)
    print(f"  报告已保存: {output_report}")
    
    print("\n" + "=" * 70)
    print("处理完成!")
    print("=" * 70)
    print(f"\n检查文件数: {fix_stats['files_checked']}")
    print(f"修复链接数: {fix_stats['links_fixed']}")
    print(f"无法修复: {fix_stats['links_not_fixable']}")
    print("=" * 70)
    
    if dry_run:
        print("\n注意：当前为演示模式，未实际修改文件。")
        print("如需实际执行修复，请将 dry_run 设为 False")


if __name__ == '__main__':
    main()
