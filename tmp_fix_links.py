#!/usr/bin/env python3
"""
修复FormalMath项目中的断链问题
"""

import os
import re
import json
from pathlib import Path
from collections import defaultdict

WORK_DIR = Path("g:/_src/FormalMath")

def get_file_mapping():
    """构建文件名到实际路径的映射"""
    mapping = {}
    for pattern in ['concept/**/*.md', 'tools/**/*.md', 'tests/**/*.md', '*.md', 'docs/**/*.md', '数学家理念体系/**/*.md']:
        for f in WORK_DIR.glob(pattern):
            if f.is_file():
                name = f.name
                rel_path = str(f.relative_to(WORK_DIR)).replace('\\', '/')
                if name not in mapping:
                    mapping[name] = []
                mapping[name].append(rel_path)
    return mapping

def find_best_match(target_path, source_file, file_mapping):
    """为断链寻找最佳匹配"""
    target = target_path.replace('\\', '/').strip('./')
    target_name = target.split('/')[-1]
    
    # 1. 直接文件名匹配
    if target_name in file_mapping:
        candidates = file_mapping[target_name]
        if len(candidates) == 1:
            return candidates[0]
        # 多个候选，选择路径最接近的
        source_rel = str(source_file.relative_to(WORK_DIR)).replace('\\', '/')
        source_parts = source_rel.split('/')
        best = None
        best_score = -1
        for c in candidates:
            c_parts = c.split('/')
            score = 0
            for i, (a, b) in enumerate(zip(source_parts, c_parts)):
                if a == b:
                    score += 10
                else:
                    break
            if score > best_score:
                best_score = score
                best = c
        return best
    
    # 2. 核心概念特殊处理
    if '核心概念' in target or target_name.startswith('01-') or target_name.startswith('02-'):
        core_concept_dir = WORK_DIR / 'concept' / '核心概念'
        if core_concept_dir.exists():
            for f in core_concept_dir.glob('*.md'):
                if f.name.endswith(target_name) or target_name.endswith(f.name.replace('.md', '') + '.md'):
                    return str(f.relative_to(WORK_DIR)).replace('\\', '/')
    
    # 3. 检查是否是归档文件
    if '00-归档' not in target:
        archive_dirs = [
            WORK_DIR / 'concept' / '00-归档',
            WORK_DIR / '00-归档',
        ]
        for arc_dir in archive_dirs:
            if arc_dir.exists():
                for root, dirs, files in os.walk(arc_dir):
                    for f in files:
                        if f == target_name:
                            full_path = Path(root) / f
                            return str(full_path.relative_to(WORK_DIR)).replace('\\', '/')
    
    return None

def get_relative_path(source, target):
    """计算从source到target的相对路径"""
    source_parts = source.replace('\\', '/').split('/')
    target_parts = target.replace('\\', '/').split('/')
    
    source_dir = source_parts[:-1]
    
    common = 0
    for i, (s, t) in enumerate(zip(source_dir, target_parts)):
        if s == t:
            common += 1
        else:
            break
    
    up = len(source_dir) - common
    rel_parts = ['..'] * up + target_parts[common:]
    
    if not rel_parts:
        return './' + target_parts[-1]
    
    return './' + '/'.join(rel_parts)

def fix_broken_links():
    """修复断链"""
    with open(WORK_DIR / 'tmp_broken_links_report.json', 'r', encoding='utf-8') as f:
        report = json.load(f)
    
    file_mapping = get_file_mapping()
    
    fixed_count = 0
    not_fixed_count = 0
    fix_details = []
    
    by_source = defaultdict(list)
    for link in report['broken_links']:
        by_source[link['source']].append(link)
    
    print(f"处理 {len(by_source)} 个文件中的断链...")
    
    processed = 0
    for source_path, links in by_source.items():
        processed += 1
        if processed % 100 == 0:
            print(f"  已处理 {processed}/{len(by_source)} 个文件...")
        
        source_file = WORK_DIR / source_path
        if not source_file.exists():
            continue
        
        try:
            with open(source_file, 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read()
            
            original_content = content
            
            for link in links:
                old_path = link['path']
                
                # 查找最佳匹配
                new_path = find_best_match(old_path, source_file, file_mapping)
                
                if new_path:
                    # 计算相对路径
                    source_rel = str(source_file.relative_to(WORK_DIR)).replace('\\', '/')
                    new_rel_path = get_relative_path(source_rel, new_path)
                    
                    # 处理锚点
                    if '#' in old_path:
                        anchor = old_path.split('#')[1]
                        new_rel_path_with_anchor = new_rel_path + '#' + anchor
                    else:
                        new_rel_path_with_anchor = new_rel_path
                    
                    # 替换链接
                    old_link_pattern = f"]({re.escape(old_path)})"
                    new_link_replace = f"]({new_rel_path_with_anchor})"
                    
                    if old_link_pattern.replace('\\', '') in content:
                        content = content.replace(old_link_pattern.replace('\\', ''), new_link_replace)
                        fixed_count += 1
                        fix_details.append({
                            'source': source_path,
                            'old': old_path,
                            'new': new_rel_path_with_anchor,
                            'status': 'fixed'
                        })
                    elif f"]({old_path})" in content:
                        content = content.replace(f"]({old_path})", new_link_replace)
                        fixed_count += 1
                        fix_details.append({
                            'source': source_path,
                            'old': old_path,
                            'new': new_rel_path_with_anchor,
                            'status': 'fixed'
                        })
                else:
                    not_fixed_count += 1
                    fix_details.append({
                        'source': source_path,
                        'old': old_path,
                        'new': None,
                        'status': 'not_found'
                    })
            
            # 保存修改后的文件
            if content != original_content:
                with open(source_file, 'w', encoding='utf-8') as f:
                    f.write(content)
        
        except Exception as e:
            print(f"处理文件 {source_path} 时出错: {e}")
    
    # 保存修复详情
    with open(WORK_DIR / 'tmp_fix_details.json', 'w', encoding='utf-8') as f:
        json.dump({
            'fixed_count': fixed_count,
            'not_fixed_count': not_fixed_count,
            'details': fix_details
        }, f, ensure_ascii=False, indent=2)
    
    print(f"\n修复完成:")
    print(f"  - 已修复: {fixed_count}")
    print(f"  - 未修复(未找到匹配): {not_fixed_count}")
    print(f"\n详细修复信息已保存到 tmp_fix_details.json")

if __name__ == '__main__':
    fix_broken_links()
