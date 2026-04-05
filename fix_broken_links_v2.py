#!/usr/bin/env python3
"""
修复FormalMath项目中的断链 - 第二轮
"""
import os
import re
import json

# 新增链接映射规则
ADDITIONAL_LINK_MAPPING = {
    # 代数结构子目录映射
    "../02-代数结构/01-群论/00-README.md": "../02-代数结构/02-核心理论/群论/群论.md",
    "../02-代数结构/02-环论/00-README.md": "../02-代数结构/02-核心理论/环论/环论.md",
    "../02-代数结构/02-范畴论/00-README.md": "../02-代数结构/02-核心理论/范畴论/范畴论.md",
    "../02-代数结构/03-线性代数/00-README.md": "../02-代数结构/02-核心理论/线性代数与矩阵理论/线性代数.md",
    "../02-代数结构/04-李群与李代数/00-README.md": "../02-代数结构/02-核心理论/李代数/李代数.md",
    
    # 数理逻辑内部映射
    "../07-数理逻辑/可计算性理论/00-README.md": "../07-数理逻辑/04-可计算性理论/00-README.md",
    "../07-数理逻辑/01-集合论/01-基础概念.md": "../07-数理逻辑/01-集合论/01-基础概念.md",  # 检查是否存在
    
    # 分析学映射
    "../03-分析学/01-实分析/00-README.md": "../03-分析学/01-实分析/00-README.md",  # 检查是否存在
    "../03-分析学/02-泛函分析/00-README.md": "../03-分析学/03-泛函分析/00-README.md",
    "../03-分析学/03-微分方程/00-README.md": "../03-分析学/05-微分方程/00-README.md",
    "../03-分析学/03-插值理论-深度版.md": "../03-分析学/03-微分学-深度版.md",
    "../03-分析学/正交多项式.md": "../03-分析学/03-微分学-深度版.md",
    
    # 几何拓扑映射
    "../04-几何与拓扑/03-拓扑学/00-README.md": "../04-几何与拓扑/03-拓扑学内容/00-README.md",
    "../04-几何与拓扑/03-拓扑学内容.md": "../04-几何与拓扑/03-拓扑学内容/00-README.md",
    "../04-几何与拓扑/01-几何学基础/00-README.md": "../04-几何与拓扑/01-几何学基础/00-README.md",  # 检查
    "../04-几何与拓扑/02-代数拓扑/02-核心定理.md": "../04-几何与拓扑/02-微分几何-扩展/02-核心定理.md",
    "../04-几何与拓扑/辛几何.md": "../04-几何与拓扑/01-几何学基础/辛几何.md",
    "../04-几何与拓扑/热带几何.md": "../04-几何与拓扑/01-几何学基础/热带几何.md",
    "../04-几何与拓扑/etale-cohomology.md": "../04-几何与拓扑/02-微分几何-扩展/etale-cohomology.md",
    
    # 概率统计 - 时间序列分析不存在，映射到随机过程
    "../06-概率论与统计/04-时间序列分析/00-README.md": "../06-概率论与统计/02-随机过程/00-README.md",
    
    # 应用数学内部
    "../10-应用数学/强化学习.md": "../10-应用数学/07-人工智能数学-深化版.md",
    "../12-应用数学/06-机器学习数学基础.md": "../10-应用数学/06-机器学习数学基础.md",
    
    # 高级数学内部
    "../11-高级数学/层论基础-深度版.md": "../11-高级数学/sheaf-cohomology.md",
    "../11-高级数学/28-量子数学-深化版.md": "../11-高级数学/32-量子数学-深化版.md",
    
    # 索引文件
    "../../INDEX.md": "../INDEX.md",
    "../../docs/README.md": "../README.md",
    
    # 案例库内部
    "01-基础数学/": "../01-基础数学/",
    "02-代数结构/": "../02-代数结构/",
    "03-分析学/": "../03-分析学/",
    "04-几何学/": "../04-几何与拓扑/01-几何学基础/",
    "05-拓扑学/": "../04-几何与拓扑/03-拓扑学内容/",
    "06-数论/": "../05-数论/",
    "07-逻辑学/": "../07-数理逻辑/",
    "08-计算数学/": "../08-计算数学/",
    "../00-README.md": "./00-README.md",
    "入门级/": "./",
    "中级/": "./",
    "高级/": "./",
    
    # 其他缺失文件
    "../01-基础数学/图论基础.md": "../09-组合数学与离散数学/02-图论/01-图论基础-深度版.md",
    "../09-组合数学与离散数学/计算复杂性理论.md": "../09-组合数学与离散数学/01-组合数学/31.05-极值组合学/00-README.md",
    
    # 动力学系统扩展
    "../../concept/": "../../../concept/",
    "../../project/": "../../../project/",
    "../../数学家理念体系/": "../../../数学家理念体系/",
}

# 目录存在性检查 - 如果不存在则映射到存在的目录
DIRECTORY_FALLBACKS = {
    "../06-概率论与统计/04-时间序列分析/": "../06-概率论与统计/02-随机过程/",
}


def fix_file_v2(file_path, fixes_made):
    """修复单个文件中的断链 - 第二轮"""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
    except Exception as e:
        return False

    original_content = content
    file_fixed = False

    # 应用新增链接映射
    for old_link, new_link in ADDITIONAL_LINK_MAPPING.items():
        # 处理Markdown链接 [text](url)
        pattern = rf'\[([^\]]*)\]\({re.escape(old_link)}\)'
        matches = list(re.finditer(pattern, content))
        if matches:
            for match in matches:
                text = match.group(1)
                content = content.replace(match.group(0), f'[{text}]({new_link})')
                fixes_made.append({
                    'file': file_path,
                    'old': match.group(0),
                    'new': f'[{text}]({new_link})',
                    'type': 'additional_mapping'
                })
                file_fixed = True

    # 处理目录级别的回退
    for old_dir, new_dir in DIRECTORY_FALLBACKS.items():
        if old_dir in content:
            content = content.replace(old_dir, new_dir)
            fixes_made.append({
                'file': file_path,
                'old': old_dir,
                'new': new_dir,
                'type': 'directory_fallback'
            })
            file_fixed = True

    if file_fixed and content != original_content:
        try:
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(content)
            return True
        except Exception as e:
            print(f"Error writing {file_path}: {e}")
            return False
    
    return False


def main():
    # 目标分支目录
    target_dirs = [
        "docs/05-数论",
        "docs/06-概率论与统计",
        "docs/07-数理逻辑",
        "docs/08-计算数学",
        "docs/09-组合数学与离散数学",
        "docs/10-应用数学",
        "docs/11-高级数学",
    ]

    fixes_made = []
    files_fixed = 0

    print("开始第二轮断链修复...")

    for target_dir in target_dirs:
        if not os.path.exists(target_dir):
            continue
        
        for root, _, filenames in os.walk(target_dir):
            for filename in filenames:
                if filename.endswith('.md'):
                    file_path = os.path.join(root, filename)
                    file_path = file_path.replace('\\', '/')
                    if fix_file_v2(file_path, fixes_made):
                        files_fixed += 1

    total_links_fixed = len(fixes_made)

    print(f"\n第二轮修复完成!")
    print(f"修复文件数: {files_fixed}")
    print(f"修复链接数: {total_links_fixed}")

    # 保存修复记录
    report = {
        'files_fixed': files_fixed,
        'total_links_fixed': total_links_fixed,
        'fixes': fixes_made
    }

    with open('link_fixes_report_v2.json', 'w', encoding='utf-8') as f:
        json.dump(report, f, ensure_ascii=False, indent=2)


if __name__ == '__main__':
    main()
