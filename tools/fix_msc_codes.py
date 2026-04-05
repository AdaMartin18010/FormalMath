#!/usr/bin/env python3
"""
修复MSC编码格式问题
将XX-XX格式转换为有效的MSC编码格式
"""

import os
import re
import yaml
from pathlib import Path

# MSC大类到默认具体编码的映射
MSC_CATEGORY_MAPPING = {
    '00-XX': '00A99',  # 一般数学
    '00-01': '00A05',  # 一般数学教材
    '00A99': '00A99',
    '01-XX': '01A99',  # 数学史
    '03-XX': '03E99',  # 数理逻辑
    '05-XX': '05A99',  # 组合学
    '06-XX': '06A99',  # 序、格
    '08-XX': '08A99',  # 一般代数系统
    '11-XX': '11A99',  # 数论
    '12-XX': '12F99',  # 域论
    '13-XX': '13A99',  # 交换代数
    '14-XX': '14A99',  # 代数几何
    '15-XX': '15A99',  # 线性代数
    '16-XX': '16A99',  # 结合环
    '17-XX': '17A99',  # 非结合环
    '18-XX': '18A99',  # 范畴论
    '19-XX': '19A99',  # K-理论
    '20-XX': '20A99',  # 群论
    '22-XX': '22A99',  # 拓扑群
    '26-XX': '26A99',  # 实函数
    '28-XX': '28A99',  # 测度论
    '30-XX': '30A99',  # 单复变函数
    '31-XX': '31A99',  # 位势论
    '32-XX': '32A99',  # 多复变函数
    '33-XX': '33A99',  # 特殊函数
    '34-XX': '34A99',  # 常微分方程
    '35-XX': '35A99',  # 偏微分方程
    '37-XX': '37A99',  # 动力系统
    '39-XX': '39A99',  # 差分方程
    '40-XX': '40A99',  # 序列、级数
    '41-XX': '41A99',  # 逼近论
    '42-XX': '42A99',  # 傅里叶分析
    '43-XX': '43A99',  # 抽象调和分析
    '44-XX': '44A99',  # 积分变换
    '45-XX': '45A99',  # 积分方程
    '46-XX': '46A99',  # 泛函分析
    '47-XX': '47A99',  # 算子理论
    '49-XX': '49A99',  # 变分法
    '51-XX': '51A99',  # 几何学
    '52-XX': '52A99',  # 凸几何
    '53-XX': '53A99',  # 微分几何
    '54-XX': '54A99',  # 一般拓扑学
    '55-XX': '55A99',  # 代数拓扑
    '57-XX': '57A99',  # 流形
    '58-XX': '58A99',  # 大范围分析
    '60-XX': '60A99',  # 概率论
    '62-XX': '62A99',  # 统计学
    '65-XX': '65A99',  # 数值分析
    '68-XX': '68A99',  # 计算机科学
    '70-XX': '70A99',  # 质点力学
    '74-XX': '74A99',  # 固体力学
    '76-XX': '76A99',  # 流体力学
    '78-XX': '78A99',  # 光学
    '80-XX': '80A99',  # 经典热力学
    '81-XX': '81A99',  # 量子理论
    '82-XX': '82A99',  # 统计力学
    '83-XX': '83A99',  # 相对论
    '85-XX': '85A99',  # 天文学
    '86-XX': '86A99',  # 地球物理学
    '90-XX': '90A99',  # 运筹学
    '91-XX': '91A99',  # 博弈论
    '92-XX': '92A99',  # 生物学
    '93-XX': '93A99',  # 系统论
    '94-XX': '94A99',  # 信息论
    '97-XX': '97A99',  # 数学教育
}

def fix_msc_code(code):
    """修复单个MSC编码"""
    if not isinstance(code, str):
        code = str(code)
    
    code = code.strip().strip('"\'')
    
    # 如果已经是正确格式，直接返回
    if re.match(r'^\d{2}[A-Z]\d{2}$', code):
        return code
    
    # 映射大类编码
    if code in MSC_CATEGORY_MAPPING:
        return MSC_CATEGORY_MAPPING[code]
    
    # 处理XX-XX格式
    if re.match(r'^\d{2}-XX$', code):
        category = code[:2]
        return MSC_CATEGORY_MAPPING.get(code, f'{category}A99')
    
    # 处理其他变体
    # 03-XX -> 03E99
    match = re.match(r'^(\d{2})-XX$', code)
    if match:
        category = match.group(1)
        return f'{category}A99'
    
    # 00-01 -> 00A05 (教科书分类)
    if code == '00-01':
        return '00A05'
    
    # 如果无法识别，返回默认编码
    return '00A99'

def process_file(filepath):
    """处理单个文件"""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
        
        if not content.startswith('---'):
            return None
        
        match = re.search(r'^---\s*\n(.*?)\n---\s*\n', content, re.DOTALL)
        if not match:
            return None
        
        frontmatter_str = match.group(1)
        remaining = content[match.end():]
        
        try:
            data = yaml.safe_load(frontmatter_str)
        except yaml.YAMLError:
            return None
        
        if not data:
            return None
        
        modified = False
        changes = []
        
        # 修复msc_primary
        if 'msc_primary' in data:
            old_val = data['msc_primary']
            if isinstance(old_val, list):
                # 如果是数组，取第一个
                old_val = old_val[0] if old_val else '00A99'
                data['msc_primary'] = fix_msc_code(old_val)
                modified = True
                changes.append(f'msc_primary: {old_val} -> {data["msc_primary"]}')
            elif isinstance(old_val, str):
                new_val = fix_msc_code(old_val)
                if new_val != old_val:
                    data['msc_primary'] = new_val
                    modified = True
                    changes.append(f'msc_primary: {old_val} -> {new_val}')
        
        # 修复msc_secondary
        if 'msc_secondary' in data:
            old_secondary = data['msc_secondary']
            if isinstance(old_secondary, str):
                # 可能是逗号分隔的列表
                codes = [c.strip() for c in old_secondary.split(',')]
                new_codes = [fix_msc_code(c) for c in codes]
                data['msc_secondary'] = new_codes
                modified = True
                changes.append(f'msc_secondary: {old_secondary} -> {new_codes}')
            elif isinstance(old_secondary, list):
                new_codes = []
                for code in old_secondary:
                    if isinstance(code, str):
                        # 处理逗号分隔的字符串
                        if ',' in code:
                            subcodes = [c.strip() for c in code.split(',')]
                            new_codes.extend([fix_msc_code(c) for c in subcodes])
                        else:
                            new_codes.append(fix_msc_code(code))
                    else:
                        new_codes.append(fix_msc_code(str(code)))
                if new_codes != old_secondary:
                    data['msc_secondary'] = new_codes
                    modified = True
                    changes.append(f'msc_secondary: {old_secondary} -> {new_codes}')
        
        if modified:
            # 生成新的frontmatter
            yaml_content = yaml.dump(data, allow_unicode=True, sort_keys=False, default_flow_style=False)
            new_frontmatter = f"---\n{yaml_content}---\n"
            new_content = new_frontmatter + remaining
            
            with open(filepath, 'w', encoding='utf-8') as f:
                f.write(new_content)
            
            return changes
        
        return None
        
    except Exception as e:
        return [f'Error: {e}']

def main():
    root_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    
    print(f"扫描目录: {root_dir}")
    print("=" * 60)
    
    fixed_count = 0
    total_issues = 0
    
    for dirpath, dirnames, filenames in os.walk(root_dir):
        # 跳过特定目录
        dirnames[:] = [d for d in dirnames if d not in ['.git', 'node_modules', '__pycache__', '.venv', 'venv']]
        
        for filename in filenames:
            if filename.endswith('.md'):
                filepath = os.path.join(dirpath, filename)
                changes = process_file(filepath)
                if changes:
                    rel_path = os.path.relpath(filepath, root_dir)
                    print(f"\n{rel_path}:")
                    for change in changes:
                        print(f"  - {change}")
                    fixed_count += 1
                    total_issues += len(changes)
    
    print(f"\n{'=' * 60}")
    print(f"修复完成!")
    print(f"  - 修复文件数: {fixed_count}")
    print(f"  - 修复问题数: {total_issues}")

if __name__ == '__main__':
    main()
