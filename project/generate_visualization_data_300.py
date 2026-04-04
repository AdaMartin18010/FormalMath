#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalMath 概念图谱可视化数据生成脚本 (300节点版本)
========================================================

基于 concept_prerequisites.yaml 生成可视化数据，支持300个概念节点。

作者: FormalMath Team
创建日期: 2026年4月4日
版本: 3.0.0

功能:
1. 解析YAML概念数据库
2. 生成可视化JSON数据
3. 生成统计报告
4. 支持300节点性能优化

依赖:
- PyYAML: YAML解析
- json: JSON导出
"""

import yaml
import json
from collections import defaultdict
from datetime import datetime
import os


def parse_concepts(yaml_file: str) -> dict:
    """
    解析YAML概念数据库
    
    Args:
        yaml_file: YAML文件路径
        
    Returns:
        dict: 解析后的概念数据
    """
    with open(yaml_file, 'r', encoding='utf-8') as f:
        data = yaml.safe_load(f)
    return data


def generate_visualization_data(concepts_data: dict) -> dict:
    """
    生成可视化数据
    
    Args:
        concepts_data: 概念数据
        
    Returns:
        dict: 可视化JSON数据
    """
    concepts = concepts_data.get('concepts', [])
    
    # 分类到组的映射
    category_to_group = {
        "分析学": 1,
        "代数学": 2,
        "几何拓扑": 3,
        "数论逻辑": 4,
        "概率统计": 5,
        "最优化": 6,
        "控制论": 7,
        "信息论": 8,
        "密码学": 9,
        "金融数学": 10,
        "生物数学": 11,
        "计算数学": 12,
        "物理数学": 13,
        "数据科学": 14
    }
    
    # 分类颜色映射
    category_colors = {
        "分析学": "#E3F2FD",      # 浅蓝
        "代数学": "#F3E5F5",      # 浅紫
        "几何拓扑": "#E8F5E9",    # 浅绿
        "数论逻辑": "#FFF3E0",    # 浅橙
        "概率统计": "#FCE4EC",    # 浅粉
        "最优化": "#E0F7FA",      # 浅青
        "控制论": "#FFF8E1",      # 浅黄
        "信息论": "#F3E5F5",      # 浅紫
        "密码学": "#FFEBEE",      # 浅红
        "金融数学": "#E8EAF6",    # 靛蓝
        "生物数学": "#E0F2F1",    # 青绿
        "计算数学": "#F1F8E9",    # 浅绿黄
        "物理数学": "#FFF3E0",    # 琥珀
        "数据科学": "#FBE9E7"     # 深橙
    }
    
    nodes = []
    edges = []
    concept_ids = set()
    
    # 生成节点
    for concept in concepts:
        concept_id = concept.get('concept_id')
        concept_ids.add(concept_id)
        category = concept.get('category', '未分类')
        
        node = {
            "id": concept_id,
            "label": concept.get('name'),
            "category": category,
            "difficulty": concept.get('difficulty', 1),
            "estimated_hours": concept.get('estimated_hours', 0),
            "group": category_to_group.get(category, 0),
            "color": category_colors.get(category, "#E0E0E0"),
            "title": f"{concept.get('name')} ({concept_id})\n难度: {concept.get('difficulty', 1)}\n预计学习: {concept.get('estimated_hours', 0)}小时"
        }
        nodes.append(node)
    
    # 生成边（依赖关系）
    edge_count = 0
    for concept in concepts:
        from_id = concept.get('concept_id')
        prerequisites = concept.get('prerequisites', [])
        
        for prereq in prerequisites:
            to_id = prereq.get('concept_id')
            if to_id in concept_ids:
                edge = {
                    "from": to_id,
                    "to": from_id,
                    "level": prereq.get('level', 'L0'),
                    "relation": prereq.get('relation', '依赖')
                }
                edges.append(edge)
                edge_count += 1
    
    # 统计跨学科连接
    cross_connections = 0
    for edge in edges:
        from_node = next((n for n in nodes if n['id'] == edge['from']), None)
        to_node = next((n for n in nodes if n['id'] == edge['to']), None)
        if from_node and to_node:
            if from_node['category'] != to_node['category']:
                cross_connections += 1
    
    viz_data = {
        "metadata": {
            "version": "3.0",
            "generated_date": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "total_concepts": len(nodes),
            "total_dependencies": len(edges),
            "total_cross_connections": cross_connections
        },
        "nodes": nodes,
        "edges": edges
    }
    
    return viz_data


def generate_statistics(concepts_data: dict) -> dict:
    """
    生成统计报告
    
    Args:
        concepts_data: 概念数据
        
    Returns:
        dict: 统计报告
    """
    concepts = concepts_data.get('concepts', [])
    metadata = concepts_data.get('metadata', {})
    
    # 按分类统计
    category_stats = defaultdict(lambda: {'count': 0, 'total_hours': 0, 'difficulties': []})
    
    # 难度分布
    difficulty_distribution = defaultdict(int)
    
    # 学习时长分布
    hours_distribution = {
        '0-20': 0,
        '21-40': 0,
        '41-60': 0,
        '61+': 0
    }
    
    total_hours = 0
    total_prerequisites = 0
    total_successors = 0
    
    for concept in concepts:
        category = concept.get('category', '未分类')
        difficulty = concept.get('difficulty', 1)
        hours = concept.get('estimated_hours', 0)
        
        # 分类统计
        category_stats[category]['count'] += 1
        category_stats[category]['total_hours'] += hours
        category_stats[category]['difficulties'].append(difficulty)
        
        # 难度分布
        difficulty_distribution[difficulty] += 1
        
        # 学习时长分布
        if hours <= 20:
            hours_distribution['0-20'] += 1
        elif hours <= 40:
            hours_distribution['21-40'] += 1
        elif hours <= 60:
            hours_distribution['41-60'] += 1
        else:
            hours_distribution['61+'] += 1
        
        total_hours += hours
        total_prerequisites += len(concept.get('prerequisites', []))
        total_successors += len(concept.get('successors', []))
    
    # 计算分类平均难度
    for category in category_stats:
        difficulties = category_stats[category]['difficulties']
        category_stats[category]['avg_difficulty'] = sum(difficulties) / len(difficulties) if difficulties else 0
        del category_stats[category]['difficulties']
    
    # 跨学科连接统计
    cross_discipline = {
        "金融数学 ↔ 概率统计": ["brownian_motion", "martingale", "stochastic_calculus"],
        "金融数学 ↔ 随机分析": ["ito_calculus", "sde", "ito_lemma"],
        "生物数学 ↔ 微分方程": ["population_dynamics", "sir_model", "reaction_diffusion"],
        "生物数学 ↔ 动力系统": ["evolutionary_dynamics", "replicator_dynamics", "biological_oscillator"],
        "计算数学 ↔ 数值分析": ["finite_difference", "finite_element", "numerical_pde"],
        "计算数学 ↔ 线性代数": ["sparse_matrix", "iterative_method", "numerical_linear_algebra"],
        "物理数学 ↔ 泛函分析": ["quantum_mechanics", "schrodinger_equation", "operator_theory"],
        "物理数学 ↔ 李群": ["gauge_theory", "lie_group", "symmetry"],
        "数据科学 ↔ 概率统计": ["pca", "bayesian_inference", "statistical_learning"],
        "数据科学 ↔ 优化": ["gradient_descent", "adam_optimizer", "svm"]
    }
    
    stats = {
        "general": {
            "total_concepts": len(concepts),
            "total_categories": len(category_stats),
            "total_estimated_hours": total_hours,
            "avg_hours_per_concept": round(total_hours / len(concepts), 2) if concepts else 0,
            "avg_prerequisites": round(total_prerequisites / len(concepts), 2) if concepts else 0,
            "avg_successors": round(total_successors / len(concepts), 2) if concepts else 0
        },
        "by_category": dict(category_stats),
        "difficulty_distribution": dict(difficulty_distribution),
        "hours_distribution": hours_distribution,
        "cross_discipline_connections": cross_discipline,
        "metadata": {
            "version": "3.0",
            "generated_date": datetime.now().strftime("%Y-%m-%d"),
            "previous_version": "2.0 (200 concepts)",
            "current_version": "3.0 (300 concepts)",
            "new_categories": ["金融数学", "生物数学", "计算数学", "物理数学", "数据科学"]
        }
    }
    
    return stats


def generate_category_summary(stats: dict) -> str:
    """
    生成分类汇总报告（Markdown格式）
    
    Args:
        stats: 统计数据
        
    Returns:
        str: Markdown格式的报告
    """
    lines = [
        "# FormalMath 概念图谱统计报告 (300概念)",
        "",
        f"**生成日期**: {stats['metadata']['generated_date']}",
        f"**版本**: {stats['metadata']['current_version']}",
        "",
        "## 总体统计",
        "",
        f"- **总概念数**: {stats['general']['total_concepts']}",
        f"- **总分类数**: {stats['general']['total_categories']}",
        f"- **总学习时长**: {stats['general']['total_estimated_hours']} 小时",
        f"- **平均学习时长**: {stats['general']['avg_hours_per_concept']} 小时/概念",
        f"- **平均前置依赖**: {stats['general']['avg_prerequisites']}",
        f"- **平均后继概念**: {stats['general']['avg_successors']}",
        "",
        "## 分类统计",
        "",
        "| 分类 | 概念数 | 总学习时长 | 平均难度 |",
        "|------|--------|------------|----------|"
    ]
    
    for category, data in sorted(stats['by_category'].items()):
        lines.append(f"| {category} | {data['count']} | {data['total_hours']} 小时 | {data['avg_difficulty']:.1f} |")
    
    lines.extend([
        "",
        "## 难度分布",
        "",
        "| 难度等级 | 概念数量 | 占比 |",
        "|----------|----------|------|"
    ])
    
    total = stats['general']['total_concepts']
    for difficulty, count in sorted(stats['difficulty_distribution'].items()):
        percentage = (count / total * 100) if total > 0 else 0
        lines.append(f"| 难度 {difficulty} | {count} | {percentage:.1f}% |")
    
    lines.extend([
        "",
        "## 学习时长分布",
        "",
        "| 时长范围 | 概念数量 | 占比 |",
        "|----------|----------|------|"
    ])
    
    for range_name, count in stats['hours_distribution'].items():
        percentage = (count / total * 100) if total > 0 else 0
        lines.append(f"| {range_name} 小时 | {count} | {percentage:.1f}% |")
    
    lines.extend([
        "",
        "## 跨学科连接",
        "",
        "新增应用数学与纯数学的连接:",
        ""
    ])
    
    for connection, concepts in stats['cross_discipline_connections'].items():
        lines.append(f"- **{connection}**: {', '.join(concepts[:3])}...")
    
    lines.extend([
        "",
        "## 新增分类",
        "",
        "第十三批新增5个应用数学分支：",
        ""
    ])
    
    for category in stats['metadata']['new_categories']:
        data = stats['by_category'].get(category, {})
        lines.append(f"- **{category}**: {data.get('count', 0)} 个概念, {data.get('total_hours', 0)} 小时")
    
    lines.extend([
        "",
        "---",
        "",
        "*报告由 FormalMath 概念图谱系统生成*"
    ])
    
    return '\n'.join(lines)


def main():
    """
    主函数
    """
    print("=" * 60)
    print("FormalMath 概念图谱可视化数据生成 (300节点)")
    print("=" * 60)
    
    # 文件路径
    yaml_file = "concept_prerequisites.yaml"
    viz_output = "visualization_data_300.json"
    stats_output = "concept_statistics_300.json"
    report_output = "concept_statistics_report_300.md"
    
    # 1. 解析YAML
    print(f"\n[1/4] 解析概念数据库: {yaml_file}")
    try:
        data = parse_concepts(yaml_file)
        concepts = data.get('concepts', [])
        print(f"      ✓ 成功加载 {len(concepts)} 个概念")
    except Exception as e:
        print(f"      ✗ 错误: {e}")
        return
    
    # 2. 生成可视化数据
    print(f"\n[2/4] 生成可视化数据...")
    try:
        viz_data = generate_visualization_data(data)
        with open(viz_output, 'w', encoding='utf-8') as f:
            json.dump(viz_data, f, ensure_ascii=False, indent=2)
        print(f"      ✓ 已生成: {viz_output}")
        print(f"        - 节点数: {viz_data['metadata']['total_concepts']}")
        print(f"        - 边数: {viz_data['metadata']['total_dependencies']}")
        print(f"        - 跨学科连接: {viz_data['metadata']['total_cross_connections']}")
    except Exception as e:
        print(f"      ✗ 错误: {e}")
        return
    
    # 3. 生成统计报告
    print(f"\n[3/4] 生成统计报告...")
    try:
        stats = generate_statistics(data)
        with open(stats_output, 'w', encoding='utf-8') as f:
            json.dump(stats, f, ensure_ascii=False, indent=2)
        print(f"      ✓ 已生成: {stats_output}")
        
        # 生成Markdown报告
        report = generate_category_summary(stats)
        with open(report_output, 'w', encoding='utf-8') as f:
            f.write(report)
        print(f"      ✓ 已生成: {report_output}")
    except Exception as e:
        print(f"      ✗ 错误: {e}")
        return
    
    # 4. 打印汇总
    print(f"\n[4/4] 汇总信息")
    print(f"      总概念数: {stats['general']['total_concepts']}")
    print(f"      总学习时长: {stats['general']['total_estimated_hours']} 小时")
    print(f"      平均学习时长: {stats['general']['avg_hours_per_concept']} 小时")
    print(f"      分类数量: {stats['general']['total_categories']}")
    
    print("\n" + "=" * 60)
    print("可视化数据生成完成！")
    print("=" * 60)
    print(f"\n输出文件:")
    print(f"  - {viz_output}")
    print(f"  - {stats_output}")
    print(f"  - {report_output}")


if __name__ == "__main__":
    main()
