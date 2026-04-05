#!/usr/bin/env python3
"""
修复FormalMath项目中的断链
"""
import os
import re
import json
from pathlib import Path

# 链接映射规则: 旧链接 -> 新链接
LINK_MAPPING = {
    # 目录重映射
    "../04-抽象代数/": "../02-代数结构/",
    "../02-线性代数/": "../02-代数结构/",
    "../03-分析学/": "../03-分析学/",
    "../05-数论/": "../05-数论/",
    "../02-代数结构/02-核心理论/代数几何/": "../04-几何与拓扑/02-代数拓扑/",
    "../04-几何与拓扑/03-拓扑学内容/": "../04-几何与拓扑/",
    "../04-几何与拓扑/03-拓扑学内容": "../04-几何与拓扑/",
    "../12-应用数学/": "../10-应用数学/",
    "../11-概率论/": "../06-概率论与统计/",
    "../07-算法与数据结构/": "../09-组合数学与离散数学/",
    "../09-形式化证明/": "../07-数理逻辑/",
    "../10-语义模型/": "../07-数理逻辑/",
    "../14-自动机理论/": "../09-组合数学与离散数学/",
    
    # 文件重映射
    "../02-代数结构/范畴论/06-范畴论.md": "../02-代数结构/02-范畴论/00-README.md",
    "../02-代数结构/05-李代数.md": "../02-代数结构/04-李群与李代数/00-README.md",
    "../05-数论/02-代数数论.md": "../05-数论/02-代数数论/00-README.md",
    "../05-数论/03-解析数论.md": "../05-数论/03-解析数论/00-README.md",
    "../05-数论.md": "../05-数论/00-README.md",
    "../08-计算数学/02-优化理论.md": "../08-计算数学/02-优化理论-增强版.md",
    "../08-计算数学/03-量子计算.md": "../11-高级数学/40-量子计算数学基础.md",
    "../08-计算数学/04-金融数学.md": "../10-应用数学/12-金融数学-深化版.md",
    "../05-数论/05-生物数学.md": "../10-应用数学/08-生物数学-深化版.md",
    "../05-数论/06-概率论.md": "../06-概率论与统计/00-README.md",
    "../02-代数结构/群论/01-群论.md": "../02-代数结构/01-群论/00-README.md",
    "../02-代数结构/08-K理论.md": "../11-高级数学/08-代数K理论.md",
    "../02-代数结构/09-导出范畴论.md": "../11-高级数学/05-导出代数几何.md",
    "../02-代数结构/10-无穷范畴论.md": "../11-高级数学/06-无穷范畴理论.md",
    "../04-几何与拓扑/03-拓扑学内容/07-谱序列理论.md": "../04-几何与拓扑/02-代数拓扑/02-核心定理.md",
    "../03-分析学/05-微分方程/05-微分方程.md": "../03-分析学/03-微分方程/00-README.md",
    "../03-分析学/01-实分析/01-实分析.md": "../03-分析学/01-实分析/00-README.md",
    "../04-几何与拓扑/01-几何学基础/01-欧几里得几何.md": "../04-几何与拓扑/01-几何学基础/00-README.md",
    "../04-几何与拓扑/03-拓扑学内容/01-点集拓扑.md": "../04-几何与拓扑/03-拓扑学/00-README.md",
    "../02-代数结构/环论/02-环论.md": "../02-代数结构/02-环论/00-README.md",
    "../08-计算数学/02-优化理论.md": "../08-计算数学/02-优化理论-增强版.md",
    
    # 深度版文件映射
    "层论基础-深度版.md": "../11-高级数学/层论基础-深度版.md",
    "导出代数几何-深度版.md": "../11-高级数学/导出代数几何.md",
    "概形理论-深度版.md": "../11-高级数学/scheme-theory.md",
    "无穷范畴-深度版.md": "../11-高级数学/infinity-categories.md",
    "插值理论-深度版.md": "../03-分析学/03-插值理论-深度版.md",
    "etale上同调-深度版.md": "../04-几何与拓扑/etale-cohomology.md",
    "强化学习.md": "../10-应用数学/强化学习.md",
    "最优控制.md": "../10-应用数学/04-控制论.md",
    "组合优化.md": "../10-应用数学/03-运筹学.md",
    "网络流理论.md": "../09-组合数学与离散数学/01-组合数学/31.02-图论/00-README.md",
    "凸优化理论.md": "../08-计算数学/02-优化理论-增强版.md",
    "整数规划.md": "../10-应用数学/03-运筹学.md",
    "稀疏矩阵技术.md": "../08-计算数学/矩阵计算-深度版.md",
    "多项式计算.md": "../08-计算数学/数值积分方法-深度版.md",
    "量子计算基础.md": "../11-高级数学/40-量子计算数学基础.md",
    "统计物理数值方法.md": "../10-应用数学/11-物理数学-深化版.md",
    "qr分解与算法.md": "../08-计算数学/特征值计算-深度版.md",
    "量子力学谱理论.md": "../03-分析学/02-泛函分析/00-README.md",
    
    # 概率统计文件
    "03-随机过程.md": "../06-概率论与统计/02-随机过程/00-README.md",
    "04-数理统计.md": "../06-概率论与统计/03-数理统计/00-README.md",
    "05-时间序列分析.md": "../06-概率论与统计/04-时间序列分析/00-README.md",
    
    # 补充内容目录
    "../12-应用数学/01-概率论.md": "../10-应用数学/01-概率论.md",
    "../12-应用数学/02-统计学.md": "../10-应用数学/02-统计学.md",
    "../12-应用数学/10-信息论数学-深化版.md": "../10-应用数学/10-信息论数学-深化版.md",
    "../12-应用数学/13-区块链数学-深化版.md": "../10-应用数学/13-区块链数学-深化版.md",
    "../12-应用数学/14-量子计算数学-深化版.md": "../10-应用数学/14-量子计算数学-深化版.md",
    "../11-高级数学/28-量子数学-深化版.md": "../11-高级数学/28-量子数学-深化版.md",
    "../09-形式化证明/02-自动定理证明-深化版.md": "../07-数理逻辑/可计算性理论/00-README.md",
    
    # 数理逻辑内部
    "../01-基础数学/集合论/01-集合论基础.md": "../07-数理逻辑/01-集合论/01-基础概念.md",
    "../10-语义模型/05-类型论语义.md": "../07-数理逻辑/05-类型论/00-README.md",
    "../11-高级数学/构造性数学.md": "../07-数理逻辑/01-基础内容/04-直觉逻辑.md",
    "../12-应用数学/概率论.md": "../06-概率论与统计/00-README.md",
    "../11-高级数学/人工智能数学.md": "../11-高级数学/33-人工智能数学-深化版.md",
    
    # 计算数学内部
    "../02-代数结构/线性代数.md": "../02-代数结构/03-线性代数/00-README.md",
    "../03-分析学/微积分.md": "../03-分析学/01-实分析/00-README.md",
    "../11-高级数学/机器学习数学.md": "../11-高级数学/25-机器学习数学.md",
    "../11-高级数学/算法理论.md": "../08-计算数学/03-优化算法.md",
    "../11-高级数学/量子计算.md": "../11-高级数学/40-量子计算数学基础.md",
    "../12-应用数学/分布式系统.md": "../10-应用数学/09-网络科学数学-深化版.md",
    "../02-代数结构/代数结构.md": "../02-代数结构/00-README.md",
    "../11-高级数学/计算机代数.md": "../08-计算数学/05-符号计算.md",
    "../01-基础数学/算法复杂度理论.md": "../09-组合数学与离散数学/计算复杂性理论.md",
    "../04-几何与拓扑/01-几何学基础/热带几何.md": "../04-几何与拓扑/热带几何.md",
    "../05-数论/有限域理论.md": "../05-数论/有限域.md",
    "../02-代数结构/02-核心理论/正交多项式理论.md": "../03-分析学/正交多项式.md",
    "../02-代数结构/随机矩阵理论.md": "../11-高级数学/random-matrix-theory.md",
    
    # 几何拓扑
    "../04-几何与拓扑/01-几何学基础/辛几何-增强版.md": "../04-几何与拓扑/辛几何.md",
    
    # 数理逻辑
    "../00-数学基础/": "../07-数理逻辑/",
    "../13-图论/": "../09-组合数学与离散数学/02-图论/",
    
    # 项目文件
    "../项目索引.md": "../../INDEX.md",
    "../FormalMath文档格式规范-2025年12月.md": "../../docs/README.md",
    
    # 应用案例库
    "../../应用案例库/00-README.md": "../00-README.md",
    "../应用案例库/": "../00-README.md",
}

# 需要删除的链接模式（数学表达式误识别）
DELETE_PATTERNS = [
    (r'\[t_1, \\ldots, t_n\]\(s\)', r't_1, \\ldots, t_n'),
    (r'\[y\^\{n-1\}\]\(1\+y\)', r'y^{n-1}'),
    (r'\[x\^\{10\}\]\(-x\^4\)', r'x^{10}'),
    (r'\[x\^\{10\}\]\(-x\^5\)', r'x^{10}'),
    (r'\[x\^\{10\}\]\(-x\^6\)', r'x^{10}'),
    (r'\[x_0, x_1\]\(x - x_0\)', r'x_0, x_1'),
    (r'\[x_0, \\ldots, x_n\]\(x - x_0\)', r'x_0, \\ldots, x_n'),
    (r'\[S\]\(t\)', r'S'),
    (r'\[-1\]\(x\)', r'-1'),
    (r"\[s'\|s, a\]\(R\(s, a, s'", r"s'|s, a"),
    (r"\[s'\|s,a\]\(R\(s,a", r"s'|s,a"),
    (r'\[-E_a/k_B T\]\(1 - \\exp\(-\\Delta G/k_B T', r'-E_a/k_B T'),
    (r'\[f \* g\]\(n\)', r'f * g'),
    (r"\[s'\|s,a\]\(R\(s,a,s'", r"s'|s,a"),
    (r'\[public_key\]\(12:', r'public_key'),
]

# 文件特定修复
FILE_SPECIFIC_FIXES = {
    "docs/05-数论/07-深度扩展/00-README.md": [
        ("../05-数论/", "../"),
        ("../04-抽象代数/", "../02-代数结构/"),
        ("../03-分析学/", "../03-分析学/"),
        ("../02-代数结构/02-核心理论/代数几何/", "../04-几何与拓扑/"),
    ],
    "docs/06-概率论与统计/01-概率论基础/05-布朗运动与随机微积分-深度扩展版.md": [
        ("./06-概率论与统计/01-概率论基础在数学中的应用-深度扩展版.md", "./07-概率论在数学中的应用-深度扩展版.md"),
    ],
    "docs/06-概率论与统计/01-概率论基础/06-极限定理-深度扩展版.md": [
        ("./06-概率论与统计/01-概率论基础在数学中的应用-深度扩展版.md", "./07-概率论在数学中的应用-深度扩展版.md"),
    ],
}


def fix_file(file_path, fixes_made):
    """修复单个文件中的断链"""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
    except Exception as e:
        print(f"Error reading {file_path}: {e}")
        return False

    original_content = content
    file_fixed = False

    # 应用通用链接映射
    for old_link, new_link in LINK_MAPPING.items():
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
                    'type': 'general_mapping'
                })
                file_fixed = True

    # 应用数学表达式删除模式
    for pattern, replacement in DELETE_PATTERNS:
        matches = re.findall(pattern, content)
        if matches:
            content = re.sub(pattern, replacement, content)
            fixes_made.append({
                'file': file_path,
                'old': pattern,
                'new': replacement,
                'type': 'math_expression'
            })
            file_fixed = True

    # 应用文件特定修复
    if file_path in FILE_SPECIFIC_FIXES:
        for old_link, new_link in FILE_SPECIFIC_FIXES[file_path]:
            if old_link in content:
                content = content.replace(old_link, new_link)
                fixes_made.append({
                    'file': file_path,
                    'old': old_link,
                    'new': new_link,
                    'type': 'file_specific'
                })
                file_fixed = True

    # 特殊处理：删除链接到不存在的文档（保留文本）
    # 链接到不存在的文件但保留锚点
    broken_file_patterns = [
        (r'\[([^\]]+)\]\(\.\./交互式图表增强-2025年1月\.md#[^)]+\)', r'\1'),
        (r'\[([^\]]+)\]\(\.\./定理证明补充-2025年1月\.md#[^)]+\)', r'\1'),
        (r'\[([^\]]+)\]\(\.\./反例与特殊情况补充-2025年1月\.md#[^)]+\)', r'\1'),
        (r'\[([^\]]+)\]\(\.\./历史背景补充-2025年1月\.md#[^)]+\)', r'\1'),
    ]
    
    for pattern, replacement_template in broken_file_patterns:
        matches = list(re.finditer(pattern, content))
        if matches:
            for match in matches:
                text = match.group(1)
                content = content.replace(match.group(0), text)
                fixes_made.append({
                    'file': file_path,
                    'old': match.group(0),
                    'new': text,
                    'type': 'remove_broken_link'
                })
                file_fixed = True

    # 特殊处理：删除量子数学等高级主题中的不存在文件链接
    advanced_topics_patterns = [
        r'\[量子群论高级主题\]\(./量子群论高级主题\.md\)',
        r'\[非交换几何高级主题\]\(./非交换几何高级主题\.md\)',
        r'\[量子拓扑高级主题\]\(./量子拓扑高级主题\.md\)',
        r'\[量子计算高级主题\]\(./量子计算高级主题\.md\)',
        r'\[深度学习理论高级主题\]\(./深度学习理论高级主题\.md\)',
        r'\[优化理论高级主题\]\(./优化理论高级主题\.md\)',
        r'\[概率图模型高级主题\]\(./概率图模型高级主题\.md\)',
        r'\[信息几何高级主题\]\(./信息几何高级主题\.md\)',
        r'\[统计学习理论高级主题\]\(./统计学习理论高级主题\.md\)',
        r'\[高维统计高级主题\]\(./高维统计高级主题\.md\)',
        r'\[随机矩阵理论高级主题\]\(./随机矩阵理论高级主题\.md\)',
        r'\[网络科学高级主题\]\(./网络科学高级主题\.md\)',
    ]
    
    for pattern in advanced_topics_patterns:
        matches = list(re.finditer(pattern, content))
        if matches:
            for match in matches:
                # 提取文本并移除链接
                text = match.group(0).split(']')[0][1:]
                content = content.replace(match.group(0), f'**{text}**')
                fixes_made.append({
                    'file': file_path,
                    'old': match.group(0),
                    'new': f'**{text}**',
                    'type': 'mark_as_advanced'
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
    total_links_fixed = 0

    print("开始修复断链...")

    for target_dir in target_dirs:
        if not os.path.exists(target_dir):
            continue
        
        for root, _, filenames in os.walk(target_dir):
            for filename in filenames:
                if filename.endswith('.md'):
                    file_path = os.path.join(root, filename)
                    # 转换为正斜杠路径
                    file_path = file_path.replace('\\', '/')
                    if fix_file(file_path, fixes_made):
                        files_fixed += 1

    total_links_fixed = len(fixes_made)

    print(f"\n修复完成!")
    print(f"修复文件数: {files_fixed}")
    print(f"修复链接数: {total_links_fixed}")

    # 保存修复记录
    report = {
        'files_fixed': files_fixed,
        'total_links_fixed': total_links_fixed,
        'fixes': fixes_made
    }

    with open('link_fixes_report.json', 'w', encoding='utf-8') as f:
        json.dump(report, f, ensure_ascii=False, indent=2)

    print("修复报告已保存到 link_fixes_report.json")


if __name__ == '__main__':
    main()
