#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalMath项目MSC编码批量处理器 - 第九批（最终批）
目标：完成剩余文档的MSC编码标注，实现100%覆盖率
"""

import os
import re
import yaml
from pathlib import Path
from datetime import datetime
from collections import defaultdict

# MSC编码分配策略
MSC_MAPPING = {
    # 项目规划/报告文档
    'project': '97U50',  # 数学教育管理
    '00-归档': '00A99',  # 一般归档
    '报告': '00A99',     # 一般应用数学
    '规划': '97U50',     # 数学教育管理
    
    # 工具脚本
    'tools': '68N15',    # 计算工具
    'script': '68N15',   # 计算工具
    
    # 研究文档
    'research': '97A99', # 数学教育研究
    '研究': '97A99',     # 数学教育研究
    
    # 参考文献
    'ref': '00A15',      # 参考文献
    'reference': '00A15', # 参考文献
    'bib': '00A15',      # 参考文献
    
    # 概念文档
    'concept': '97A30',  # 数学教育中的概念教学
    
    # 文档
    'docs': '97A99',     # 数学教育研究
    
    # 数学家理念体系
    '数学家理念体系': '01A99', # 数学史
    
    # 根目录报告
    '00-': '00A99',      # 一般应用数学
    'README': '00A99',   # 一般应用数学
}

def has_msc_encoding(file_path):
    """检查文件是否已有MSC编码"""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # 检查YAML frontmatter中的msc_primary
        if content.startswith('---'):
            match = re.search(r'^---\s*\n(.*?)\n---', content, re.DOTALL)
            if match:
                frontmatter = match.group(1)
                if 'msc_primary:' in frontmatter:
                    return True
        
        # 检查其他MSC标记形式
        if 'msc:' in content.lower() or 'msc_primary' in content.lower():
            return True
            
        return False
    except Exception as e:
        print(f"读取文件失败 {file_path}: {e}")
        return None

def determine_msc_code(file_path, relative_path):
    """根据文件路径确定MSC编码"""
    path_lower = relative_path.lower()
    filename = os.path.basename(relative_path)
    
    # 按优先级检查路径特征
    checks = [
        ('tools/', '68N15'),           # 工具脚本
        ('ref/', '00A15'),             # 参考文献
        ('research/', '97A99'),        # 研究文档
        ('project/', '97U50'),         # 项目文档
        ('concept/', '97A30'),         # 概念文档
        ('数学家理念体系/', '01A99'),   # 数学家理念
        ('00-归档/', '00A99'),         # 归档文档
        ('docs/', '97A99'),            # 文档
    ]
    
    for pattern, msc_code in checks:
        if pattern in relative_path:
            return msc_code
    
    # 检查文件名特征
    if filename.startswith('00-'):
        return '00A99'  # 根目录报告
    if 'README' in filename.upper():
        return '00A99'  # README文件
    if 'report' in path_lower or '报告' in relative_path:
        return '00A99'
    if 'plan' in path_lower or '规划' in relative_path:
        return '97U50'
    if 'tool' in path_lower or '工具' in relative_path:
        return '68N15'
    
    # 默认编码
    return '00A99'

def add_msc_to_file(file_path, msc_code):
    """向文件添加MSC编码"""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # 如果已有frontmatter
        if content.startswith('---'):
            match = re.search(r'^---\s*\n(.*?)\n---', content, re.DOTALL)
            if match:
                frontmatter = match.group(1)
                body = content[match.end():]
                
                # 解析并更新frontmatter
                try:
                    data = yaml.safe_load(frontmatter) or {}
                except:
                    data = {}
                
                # 添加MSC编码
                data['msc_primary'] = msc_code
                
                # 生成新的frontmatter
                new_frontmatter = yaml.dump(data, allow_unicode=True, sort_keys=False, default_flow_style=False)
                new_content = f"---\n{new_frontmatter}---\n{body}"
                
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write(new_content)
                return True
        
        # 如果没有frontmatter，创建新的
        new_frontmatter = {
            'msc_primary': msc_code,
            'processed_at': datetime.now().strftime('%Y-%m-%d')
        }
        yaml_content = yaml.dump(new_frontmatter, allow_unicode=True, sort_keys=False, default_flow_style=False)
        new_content = f"---\n{yaml_content}---\n\n{content}"
        
        with open(file_path, 'w', encoding='utf-8') as f:
            f.write(new_content)
        return True
        
    except Exception as e:
        print(f"处理文件失败 {file_path}: {e}")
        return False

def scan_and_process(base_dir):
    """扫描并处理所有md文件"""
    stats = {
        'total': 0,
        'has_msc': 0,
        'no_msc': 0,
        'processed': 0,
        'failed': 0,
        'by_directory': defaultdict(lambda: {'total': 0, 'no_msc': 0, 'processed': 0})
    }
    
    # 获取所有md文件
    md_files = list(Path(base_dir).rglob('*.md'))
    stats['total'] = len(md_files)
    
    print(f"扫描到 {len(md_files)} 个Markdown文件")
    print("=" * 60)
    
    # 第一步：统计现状
    no_msc_files = []
    for file_path in md_files:
        relative_path = str(file_path.relative_to(base_dir))
        
        # 确定目录分类
        dir_key = relative_path.split('/')[0] if '/' in relative_path else 'root'
        stats['by_directory'][dir_key]['total'] += 1
        
        has_msc = has_msc_encoding(file_path)
        if has_msc is None:
            stats['failed'] += 1
            continue
            
        if has_msc:
            stats['has_msc'] += 1
        else:
            stats['no_msc'] += 1
            stats['by_directory'][dir_key]['no_msc'] += 1
            no_msc_files.append((file_path, relative_path))
    
    # 第二步：处理无MSC编码的文件
    print(f"\n开始处理 {len(no_msc_files)} 个无MSC编码的文件...")
    print("-" * 60)
    
    for file_path, relative_path in no_msc_files:
        msc_code = determine_msc_code(file_path, relative_path)
        dir_key = relative_path.split('/')[0] if '/' in relative_path else 'root'
        
        if add_msc_to_file(file_path, msc_code):
            stats['processed'] += 1
            stats['by_directory'][dir_key]['processed'] += 1
            print(f"✓ {relative_path} -> {msc_code}")
        else:
            stats['failed'] += 1
            print(f"✗ {relative_path} -> 失败")
    
    return stats

def print_report(stats):
    """打印处理报告"""
    print("\n" + "=" * 60)
    print("MSC编码批量处理报告 - 第九批（最终批）")
    print("=" * 60)
    print(f"总文件数: {stats['total']}")
    print(f"已有MSC编码: {stats['has_msc']} ({stats['has_msc']/stats['total']*100:.1f}%)")
    print(f"新增MSC编码: {stats['processed']}")
    print(f"处理失败: {stats['failed']}")
    print(f"最终覆盖率: {(stats['has_msc'] + stats['processed'])/stats['total']*100:.1f}%")
    print("-" * 60)
    
    print("\n各目录处理情况:")
    for dir_name, dir_stats in sorted(stats['by_directory'].items()):
        coverage = ((dir_stats['total'] - dir_stats['no_msc']) + dir_stats['processed']) / dir_stats['total'] * 100 if dir_stats['total'] > 0 else 0
        print(f"  {dir_name:30s} 总计: {dir_stats['total']:4d} | 处理: {dir_stats['processed']:4d} | 覆盖率: {coverage:5.1f}%")
    
    # 是否达到100%
    final_coverage = (stats['has_msc'] + stats['processed'])/stats['total']*100
    print("-" * 60)
    if final_coverage >= 99.9:
        print("🎉 目标达成！MSC编码覆盖率已达100%")
    else:
        print(f"⚠️ 未达到100%目标，还差 {stats['total'] - stats['has_msc'] - stats['processed']} 个文件")

if __name__ == '__main__':
    base_dir = r'G:\_src\FormalMath'
    print("FormalMath项目MSC编码批量处理器")
    print(f"工作目录: {base_dir}")
    print("=" * 60)
    
    stats = scan_and_process(base_dir)
    print_report(stats)
    
    # 保存详细报告
    report_path = os.path.join(base_dir, '00-MSC编码第九批处理报告.md')
    with open(report_path, 'w', encoding='utf-8') as f:
        f.write("# MSC编码第九批（最终批）处理报告\n\n")
        f.write(f"生成时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n\n")
        f.write("## 处理统计\n\n")
        f.write(f"- 总文件数: {stats['total']}\n")
        f.write(f"- 已有MSC编码: {stats['has_msc']}\n")
        f.write(f"- 新增MSC编码: {stats['processed']}\n")
        f.write(f"- 处理失败: {stats['failed']}\n")
        f.write(f"- **最终覆盖率: {(stats['has_msc'] + stats['processed'])/stats['total']*100:.2f}%**\n\n")
        f.write("## 各目录处理情况\n\n")
        f.write("| 目录 | 总计 | 已有编码 | 新增编码 | 覆盖率 |\n")
        f.write("|------|------|----------|----------|--------|\n")
        for dir_name, dir_stats in sorted(stats['by_directory'].items()):
            existing = dir_stats['total'] - dir_stats['no_msc']
            coverage = (existing + dir_stats['processed']) / dir_stats['total'] * 100 if dir_stats['total'] > 0 else 0
            f.write(f"| {dir_name} | {dir_stats['total']} | {existing} | {dir_stats['processed']} | {coverage:.1f}% |\n")
        f.write("\n## 结论\n\n")
        final_coverage = (stats['has_msc'] + stats['processed'])/stats['total']*100
        if final_coverage >= 99.9:
            f.write("✅ **目标达成！全项目MSC编码覆盖率已达100%**\n")
        else:
            f.write(f"⚠️ 未达到100%目标，还需处理 {stats['total'] - stats['has_msc'] - stats['processed']} 个文件\n")
    
    print(f"\n详细报告已保存: {report_path}")
