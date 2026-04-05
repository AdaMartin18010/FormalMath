#!/usr/bin/env python3
"""
FormalMath项目docs/01-06分支锚点ID规范化工具 V2
改进版本：保留中文，只规范化格式
"""

import re
import os
import json
import unicodedata
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


def normalize_anchor_v2(anchor):
    """
    规范化锚点ID - V2版本
    规则:
    1. 统一小写（仅ASCII字符）
    2. 统一使用短横线连接
    3. 保留中文字符
    4. 移除特殊字符（保留中文、字母、数字、短横线）
    5. 合并多个连续的短横线
    """
    if not anchor:
        return ''
    
    # 替换下划线为短横线
    anchor = anchor.replace('_', '-')
    
    # 将空格转换为短横线
    anchor = re.sub(r'\s+', '-', anchor)
    
    # 小写化（仅ASCII字符）
    anchor = anchor.lower()
    
    # 保留中文、字母、数字、短横线，其他字符转为短横线
    # 中文字符范围: \u4e00-\u9fff
    anchor = re.sub(r'[^\w\u4e00-\u9fff-]', '-', anchor)
    
    # 合并多个连续的短横线
    anchor = re.sub(r'-+', '-', anchor)
    
    # 移除首尾短横线
    anchor = anchor.strip('-')
    
    return anchor


def extract_headers(content):
    """提取文档中的所有标题"""
    headers = []
    # 匹配Markdown标题: ## 标题内容 {#锚点} 或 ## 标题内容
    pattern = r'^(#{1,6})\s+(.+?)(?:\s+\{#([^}]+)\})?\s*$'
    
    for match in re.finditer(pattern, content, re.MULTILINE):
        level = len(match.group(1))
        title = match.group(2).strip()
        explicit_anchor = match.group(3)
        
        # 如果没有显式锚点，从标题生成
        if explicit_anchor:
            anchor = explicit_anchor
        else:
            # GitHub风格锚点生成
            anchor = generate_github_anchor(title)
        
        headers.append({
            'level': level,
            'title': title,
            'anchor': anchor,
            'line': content[:match.start()].count('\n') + 1
        })
    
    return headers


def generate_github_anchor(title):
    """生成GitHub风格的锚点"""
    # 移除Markdown格式
    title = re.sub(r'\*\*|__|\*|_|`', '', title)
    
    # 转换为小写（仅ASCII）
    anchor = title.lower()
    
    # 替换空格为短横线
    anchor = re.sub(r'\s+', '-', anchor)
    
    # 移除特殊字符（保留中文、字母、数字、短横线）
    anchor = re.sub(r'[^\w\u4e00-\u9fff-]', '', anchor)
    
    # 合并多个短横线
    anchor = re.sub(r'-+', '-', anchor)
    
    # 移除首尾短横线
    anchor = anchor.strip('-')
    
    return anchor


def extract_links(content, base_path):
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
        
        # 只处理内部链接
        if not path.startswith(('http://', 'https://', 'mailto:')):
            links.append({
                'text': text,
                'url': url,
                'path': path,
                'anchor': anchor,
                'start': match.start(),
                'end': match.end(),
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


def analyze_anchors(files):
    """分析所有文档的锚点"""
    results = {
        'files': {},
        'anchors': defaultdict(list),
        'links': [],
        'broken_links': [],
        'inconsistent_anchors': []
    }
    
    print(f"  正在分析 {len(files)} 个文件...")
    
    # 第一阶段：收集所有标题和锚点
    for idx, file_path in enumerate(files):
        if (idx + 1) % 50 == 0:
            print(f"    已处理 {idx + 1}/{len(files)} 个文件...")
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            headers = extract_headers(content)
            
            results['files'][file_path] = {
                'headers': headers,
                'content': content
            }
            
            for header in headers:
                anchor = header['anchor']
                normalized = normalize_anchor_v2(anchor)
                results['anchors'][normalized].append({
                    'file': file_path,
                    'header': header,
                    'original_anchor': anchor
                })
                
                # 检查是否需要规范化
                if anchor != normalized:
                    results['inconsistent_anchors'].append({
                        'file': file_path,
                        'header': header,
                        'original': anchor,
                        'normalized': normalized
                    })
        
        except Exception as e:
            print(f"    错误处理 {file_path}: {e}")
    
    # 第二阶段：收集所有链接
    print(f"  正在分析链接...")
    for file_path, data in results['files'].items():
        content = data['content']
        links = extract_links(content, os.path.dirname(file_path))
        
        for link in links:
            link_info = {
                'source_file': file_path,
                **link
            }
            results['links'].append(link_info)
    
    return results


def generate_anchor_mapping(results):
    """生成锚点映射表"""
    mapping = {}
    
    for normalized, instances in results['anchors'].items():
        if len(instances) > 1:
            # 检查是否有不一致
            original_anchors = set(i['original_anchor'] for i in instances)
            if len(original_anchors) > 1:
                mapping[normalized] = {
                    'canonical': normalized,
                    'variants': list(original_anchors),
                    'files': [i['file'] for i in instances]
                }
    
    return mapping


def generate_report(results, stats, output_path):
    """生成规范化报告"""
    
    # 统计锚点类型
    anchor_types = {
        '纯中文': 0,
        '纯英文': 0,
        '中英混合': 0,
        '包含数字': 0,
        '包含特殊字符': 0
    }
    
    for item in results['inconsistent_anchors']:
        anchor = item['original']
        has_chinese = bool(re.search(r'[\u4e00-\u9fff]', anchor))
        has_english = bool(re.search(r'[a-zA-Z]', anchor))
        has_digit = bool(re.search(r'\d', anchor))
        has_special = bool(re.search(r'[^\w\u4e00-\u9fff\s-]', anchor))
        
        if has_chinese and not has_english:
            anchor_types['纯中文'] += 1
        elif has_english and not has_chinese:
            anchor_types['纯英文'] += 1
        elif has_chinese and has_english:
            anchor_types['中英混合'] += 1
        
        if has_digit:
            anchor_types['包含数字'] += 1
        if has_special:
            anchor_types['包含特殊字符'] += 1
    
    report = f"""# 锚点ID规范化报告 - docs/01-06分支

**生成时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}

## 执行摘要

本次任务对FormalMath项目docs目录下的01-06分支进行了全面的锚点ID规范化分析。

### 处理范围

| 分支 | 文件数 |
|------|--------|
"""
    
    for branch, count in sorted(stats['branch_counts'].items()):
        report += f"| {branch} | {count} |\n"
    
    report += f"""
### 处理统计

| 指标 | 数量 |
|------|------|
| 扫描文档总数 | {stats['total_files']:,} |
| 发现标题总数 | {stats['total_headers']:,} |
| 发现链接总数 | {stats['total_links']:,} |
| 需规范化锚点数量 | {stats['normalized_anchors']:,} |

### 锚点类型分布

| 类型 | 数量 |
|------|------|
| 纯中文锚点 | {anchor_types['纯中文']:,} |
| 纯英文锚点 | {anchor_types['纯英文']:,} |
| 中英混合锚点 | {anchor_types['中英混合']:,} |
| 包含数字 | {anchor_types['包含数字']:,} |
| 包含特殊字符 | {anchor_types['包含特殊字符']:,} |

## 锚点规范化规则

本次规范化遵循以下规则：

1. **统一小写**: 所有ASCII字符转换为小写
2. **统一使用短横线连接**: 空格和下划线统一替换为短横线 `-`
3. **保留中文字符**: 中文内容保持原样
4. **移除特殊字符**: 只保留中文、字母、数字、短横线
5. **合并连续短横线**: 多个连续短横线合并为单个
6. **移除首尾短横线**: 清理锚点两端的短横线

### 规范化示例

| 原始锚点 | 规范化后 | 说明 |
|----------|----------|------|
| `1-引言` | `1-引言` | 中文保留 |
| `Introduction_Chapter` | `introduction-chapter` | 下划线转短横线，小写 |
| `数学公式_示例` | `数学公式-示例` | 混合内容，下划线转短横线 |
| `Section 1.1` | `section-11` | 空格转短横线，移除句点 |
| `C++基础` | `c基础` | 移除特殊符号 |

## 规范化详情

### 需要规范化的锚点（前100个）

| 序号 | 文件 | 标题 | 原锚点 | 规范化后 |
|------|------|------|--------|----------|
"""
    
    for idx, item in enumerate(results['inconsistent_anchors'][:100], 1):
        file = os.path.basename(item['file'])
        title = item['header']['title'][:25] + '...' if len(item['header']['title']) > 25 else item['header']['title']
        report += f"| {idx} | `{file}` | {title} | `{item['original']}` | `{item['normalized']}` |\n"
    
    if len(results['inconsistent_anchors']) > 100:
        report += f"\n**... 还有 {len(results['inconsistent_anchors']) - 100:,} 个规范化条目未显示**\n"
    
    report += """
## 重复锚点分析

以下锚点在多个文件中有不同变体形式：

"""
    
    mapping = generate_anchor_mapping(results)
    if mapping:
        report += "| 规范化锚点 | 变体形式 | 涉及文件数 |\n"
        report += "|------------|----------|------------|\n"
        for normalized, data in sorted(mapping.items(), key=lambda x: -len(x[1]['variants']))[:30]:
            variants = ', '.join(f'`{v}`' for v in data['variants'][:3])
            if len(data['variants']) > 3:
                variants += f" 等{len(data['variants'])}个"
            report += f"| `{normalized}` | {variants} | {len(data['files'])} |\n"
    else:
        report += "未发现重复锚点。\n"
    
    # 文件级别统计
    file_stats = defaultdict(int)
    for item in results['inconsistent_anchors']:
        file_stats[item['file']] += 1
    
    top_files = sorted(file_stats.items(), key=lambda x: -x[1])[:20]
    
    report += """
## 需规范化文件排行（Top 20）

| 文件 | 需规范化锚点数 |
|------|----------------|
"""
    for file_path, count in top_files:
        file_name = os.path.basename(file_path)
        report += f"| `{file_name}` | {count} |\n"
    
    report += f"""
## 建议与后续行动

### 立即行动

1. **批量规范化**: 使用脚本对所有识别出的锚点进行自动规范化
2. **链接更新**: 同步更新所有引用这些锚点的内部链接
3. **验证测试**: 规范化后执行全站链接检查

### 长期改进

1. **CI检查**: 在持续集成中加入锚点格式检查
2. **编辑器插件**: 开发VS Code插件实时提示锚点格式
3. **预提交钩子**: 添加Git钩子自动规范化新提交的锚点
4. **文档规范**: 更新CONTRIBUTING.md，明确锚点命名规范

### 锚点命名最佳实践

```markdown
<!-- 推荐格式 -->
## 1. 引言 {{#1-引言}}
## 基本概念 {{#基本概念}}
## Theorem证明 {{#theorem证明}}

<!-- 避免使用 -->
## 1_引言  <!-- 避免下划线 -->
## 基本概念  <!-- 缺少显式锚点 -->
## Theorem_证明  <!-- 混合格式不一致 -->
```

## 技术实现说明

### 锚点生成算法

```python
def normalize_anchor_v2(anchor):
    # 1. 替换下划线为短横线
    anchor = anchor.replace('_', '-')
    
    # 2. 将空格转换为短横线
    anchor = re.sub(r'\s+', '-', anchor)
    
    # 3. 小写化（仅ASCII字符）
    anchor = anchor.lower()
    
    # 4. 保留中文、字母、数字、短横线
    anchor = re.sub(r'[^\w\u4e00-\u9fff-]', '-', anchor)
    
    # 5. 合并多个连续的短横线
    anchor = re.sub(r'-+', '-', anchor)
    
    # 6. 移除首尾短横线
    anchor = anchor.strip('-')
    
    return anchor
```

### GitHub风格锚点生成

GitHub自动生成锚点的规则与本工具一致：
- 转换为小写
- 空格转为短横线
- 移除标点符号
- 保留中文字符

---

**报告结束**

*生成工具*: `tools/anchor_normalizer_v2.py`  
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
    print("FormalMath项目锚点ID规范化工具 V2")
    print("=" * 70)
    
    # 1. 扫描文档
    print("\n[1/4] 扫描文档...")
    files = scan_documents(docs_dir)
    print(f"  找到 {len(files)} 个Markdown文件")
    
    # 按分支统计
    branch_counts = defaultdict(int)
    for f in files:
        for branch in BRANCHES:
            if branch in f:
                branch_counts[branch] += 1
                break
    
    # 2. 分析锚点
    print("\n[2/4] 分析锚点和链接...")
    results = analyze_anchors(files)
    
    total_headers = sum(len(d['headers']) for d in results['files'].values())
    print(f"\n  统计结果:")
    print(f"    - 标题总数: {total_headers:,}")
    print(f"    - 链接总数: {len(results['links']):,}")
    print(f"    - 需规范化锚点: {len(results['inconsistent_anchors']):,}")
    
    # 3. 生成映射
    print("\n[3/4] 生成锚点映射...")
    mapping = generate_anchor_mapping(results)
    print(f"  发现 {len(mapping)} 组重复锚点")
    
    # 4. 生成报告
    print("\n[4/4] 生成报告...")
    stats = {
        'total_files': len(files),
        'total_headers': total_headers,
        'total_links': len(results['links']),
        'normalized_anchors': len(results['inconsistent_anchors']),
        'branch_counts': dict(branch_counts)
    }
    
    generate_report(results, stats, output_report)
    print(f"  报告已保存: {output_report}")
    
    print("\n" + "=" * 70)
    print("处理完成!")
    print("=" * 70)
    print(f"\n文档总数: {len(files):,}")
    print(f"标题总数: {total_headers:,}")
    print(f"链接总数: {len(results['links']):,}")
    print(f"需规范化锚点: {len(results['inconsistent_anchors']):,}")
    print(f"重复锚点组: {len(mapping):,}")
    print("=" * 70)


if __name__ == '__main__':
    main()
