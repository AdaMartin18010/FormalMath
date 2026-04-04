#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalMath 可视化数据生成脚本
生成用于D3.js/Vis.js等可视化库的数据格式
"""

import yaml
import json
from collections import defaultdict
from datetime import datetime

def parse_concepts(yaml_file):
    """解析YAML文件提取概念数据"""
    with open(yaml_file, 'r', encoding='utf-8') as f:
        content = f.read()
    
    data = yaml.safe_load(content)
    return data.get('concepts', []), data.get('metadata', {})

def generate_visualization_data(concepts, metadata):
    """生成可视化数据"""
    
    # 节点数据
    nodes = []
    for c in concepts:
        node = {
            "id": c['concept_id'],
            "label": c['name'],
            "category": c['category'],
            "difficulty": c['difficulty'],
            "estimated_hours": c['estimated_hours'],
            "group": get_category_group(c['category']),
            "title": f"{c['name']} ({c['concept_id']})\n难度: {c['difficulty']}\n预计学习: {c['estimated_hours']}小时"
        }
        nodes.append(node)
    
    # 边数据（依赖关系）
    edges = []
    edge_id = 0
    for c in concepts:
        for prereq in c.get('prerequisites', []):
            edge = {
                "id": f"e{edge_id}",
                "from": prereq['concept_id'],
                "to": c['concept_id'],
                "label": prereq.get('relation', '依赖'),
                "level": prereq.get('level', 'L1'),
                "arrows": "to"
            }
            edges.append(edge)
            edge_id += 1
    
    # 按类别分组
    categories = defaultdict(list)
    for c in concepts:
        categories[c['category']].append(c['concept_id'])
    
    # 统计每个类别的连接
    cross_connections = []
    for c in concepts:
        for prereq in c.get('prerequisites', []):
            prereq_concept = next((x for x in concepts if x['concept_id'] == prereq['concept_id']), None)
            if prereq_concept and prereq_concept['category'] != c['category']:
                cross_connections.append({
                    "from_category": prereq_concept['category'],
                    "to_category": c['category'],
                    "from_concept": prereq['concept_id'],
                    "to_concept": c['concept_id']
                })
    
    return {
        "metadata": {
            "version": metadata.get('version', '2.0'),
            "generated_date": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "total_concepts": len(concepts),
            "total_dependencies": len(edges),
            "total_cross_connections": len(cross_connections)
        },
        "nodes": nodes,
        "edges": edges,
        "categories": {k: v for k, v in categories.items()},
        "cross_connections": cross_connections
    }

def get_category_group(category):
    """获取类别的颜色组"""
    group_map = {
        "分析学": 1,
        "代数学": 2,
        "几何拓扑": 3,
        "数论逻辑": 4,
        "概率统计": 5,
        "最优化": 6,
        "控制论": 7,
        "信息论": 8,
        "密码学": 9
    }
    return group_map.get(category, 0)

def generate_mermaid_diagram(concepts, max_nodes=50):
    """生成Mermaid图表代码（简化版）"""
    lines = ["```mermaid", "graph TD"]
    
    # 选择核心概念
    core_concepts = [c for c in concepts if c['difficulty'] <= 3][:max_nodes]
    concept_ids = {c['concept_id'] for c in core_concepts}
    
    # 颜色映射
    colors = {
        "分析学": "#E1F5FE",
        "代数学": "#F3E5F5",
        "几何拓扑": "#E8F5E9",
        "数论逻辑": "#FBE9E7",
        "概率统计": "#FFF8E1",
        "最优化": "#E0F2F1",
        "控制论": "#E3F2FD",
        "信息论": "#F3E5F5",
        "密码学": "#ECEFF1"
    }
    
    # 添加节点
    for c in core_concepts:
        color = colors.get(c['category'], "#FFFFFF")
        label = f"{c['name']}"
        lines.append(f'    {c["concept_id"]}["{label}"]')
        lines.append(f'    style {c["concept_id"]} fill:{color}')
    
    # 添加边
    for c in core_concepts:
        for prereq in c.get('prerequisites', []):
            if prereq['concept_id'] in concept_ids:
                lines.append(f"    {prereq['concept_id']} --> {c['concept_id']}")
    
    lines.append("```")
    return '\n'.join(lines)

def generate_statistics_report(concepts, metadata):
    """生成统计报告"""
    
    stats = {
        "总概念数": len(concepts),
        "总依赖关系数": 0,
        "跨学科连接数": 0,
        "预计总学习时长": sum(c['estimated_hours'] for c in concepts),
        "平均学习时长": sum(c['estimated_hours'] for c in concepts) / len(concepts),
        "按类别统计": defaultdict(lambda: {"count": 0, "hours": 0}),
        "按难度统计": defaultdict(int)
    }
    
    for c in concepts:
        stats["按类别统计"][c['category']]["count"] += 1
        stats["按类别统计"][c['category']]["hours"] += c['estimated_hours']
        stats["按难度统计"][c['difficulty']] += 1
        
        for prereq in c.get('prerequisites', []):
            stats["总依赖关系数"] += 1
            prereq_concept = next((x for x in concepts if x['concept_id'] == prereq['concept_id']), None)
            if prereq_concept and prereq_concept['category'] != c['category']:
                stats["跨学科连接数"] += 1
    
    # 转换为普通dict
    stats["按类别统计"] = dict(stats["按类别统计"])
    
    return stats

def main():
    print("=" * 60)
    print("FormalMath 可视化数据生成器")
    print("=" * 60)
    
    # 解析概念数据
    concepts, metadata = parse_concepts('project/concept_prerequisites.yaml')
    print(f"\n✓ 加载了 {len(concepts)} 个概念")
    
    # 生成可视化数据
    viz_data = generate_visualization_data(concepts, metadata)
    
    with open('project/visualization_data.json', 'w', encoding='utf-8') as f:
        json.dump(viz_data, f, ensure_ascii=False, indent=2)
    print(f"✓ 可视化数据已保存: project/visualization_data.json")
    print(f"  - 节点数: {len(viz_data['nodes'])}")
    print(f"  - 边数: {len(viz_data['edges'])}")
    print(f"  - 跨学科连接: {viz_data['metadata']['total_cross_connections']}")
    
    # 生成Mermaid图表
    mermaid = generate_mermaid_diagram(concepts)
    with open('project/concept_graph.mmd', 'w', encoding='utf-8') as f:
        f.write(mermaid)
    print(f"✓ Mermaid图表已保存: project/concept_graph.mmd")
    
    # 生成统计报告
    stats = generate_statistics_report(concepts, metadata)
    
    report = []
    report.append("# FormalMath 概念图谱统计报告\n")
    report.append(f"生成日期: {datetime.now().strftime('%Y年%m月%d日')}\n")
    report.append("## 总体统计\n")
    report.append(f"- **总概念数**: {stats['总概念数']}\n")
    report.append(f"- **总依赖关系数**: {stats['总依赖关系数']}\n")
    report.append(f"- **跨学科连接数**: {stats['跨学科连接数']}\n")
    report.append(f"- **预计总学习时长**: {stats['预计总学习时长']:.0f} 小时 ({stats['预计总学习时长']/40:.0f} 周，每周40小时)\n")
    report.append(f"- **平均每个概念学习时长**: {stats['平均学习时长']:.1f} 小时\n")
    
    report.append("\n## 按类别统计\n")
    report.append("| 类别 | 概念数 | 预计学习时长 | 占比 |\n")
    report.append("|------|--------|--------------|------|\n")
    for cat, data in sorted(stats['按类别统计'].items()):
        pct = data['count'] / stats['总概念数'] * 100
        report.append(f"| {cat} | {data['count']} | {data['hours']}h | {pct:.1f}% |\n")
    
    report.append("\n## 按难度统计\n")
    report.append("| 难度等级 | 概念数 | 占比 |\n")
    report.append("|----------|--------|------|\n")
    diff_names = {1: "初级", 2: "入门", 3: "中级", 4: "高级", 5: "专家"}
    for diff in sorted(stats['按难度统计'].keys()):
        count = stats['按难度统计'][diff]
        pct = count / stats['总概念数'] * 100
        report.append(f"| {diff} ({diff_names.get(diff, '未知')}) | {count} | {pct:.1f}% |\n")
    
    with open('project/concept_statistics_report.md', 'w', encoding='utf-8') as f:
        f.writelines(report)
    print(f"✓ 统计报告已保存: project/concept_statistics_report.md")
    
    # 生成详细的JSON统计
    with open('project/concept_statistics.json', 'w', encoding='utf-8') as f:
        json.dump(stats, f, ensure_ascii=False, indent=2)
    print(f"✓ JSON统计已保存: project/concept_statistics.json")
    
    print("\n" + "=" * 60)
    print("所有文件生成完成!")
    print("=" * 60)

if __name__ == '__main__':
    main()
