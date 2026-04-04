#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""更新分析报告"""

import json
import yaml
from collections import defaultdict

# 加载数据
with open('concept_prerequisites_400.yaml', 'r', encoding='utf-8') as f:
    prereq_data = yaml.safe_load(f)

with open('category_graph_400.json', 'r', encoding='utf-8') as f:
    category_data = json.load(f)

# 构建依赖图
graph = defaultdict(list)
reverse_graph = defaultdict(list)
concept_info = {}
concept_ids = set()

if 'concepts' in prereq_data:
    for concept in prereq_data['concepts']:
        concept_id = concept['concept_id']
        concept_ids.add(concept_id)
        concept_info[concept_id] = {
            'name': concept['name'],
            'category': concept['category'],
            'difficulty': concept.get('difficulty', 1),
            'hours': concept.get('estimated_hours', 10)
        }
        
        if 'prerequisites' in concept:
            for prereq in concept['prerequisites']:
                prereq_id = prereq['concept_id']
                if prereq_id in concept_ids:
                    reverse_graph[concept_id].append(prereq_id)
                    graph[prereq_id].append(concept_id)
        
        if 'successors' in concept:
            for succ in concept['successors']:
                succ_id = succ['concept_id']
                if succ_id in concept_ids:
                    graph[concept_id].append(succ_id)
                    reverse_graph[succ_id].append(concept_id)

# 计算层级
basic_concepts = []
for cid in concept_ids:
    prereqs = reverse_graph.get(cid, [])
    valid_prereqs = [p for p in prereqs if p in concept_ids]
    if not valid_prereqs:
        basic_concepts.append(cid)

levels = {}
queue = [(cid, 0) for cid in basic_concepts]
visited = set(basic_concepts)

for cid in basic_concepts:
    levels[cid] = 0

while queue:
    current, level = queue.pop(0)
    
    for succ in graph.get(current, []):
        if succ in concept_ids:
            prereqs = [p for p in reverse_graph.get(succ, []) if p in concept_ids]
            if all(p in levels for p in prereqs):
                new_level = max(levels.get(p, 0) for p in prereqs) + 1 if prereqs else 0
                if succ not in levels or levels[succ] < new_level:
                    levels[succ] = new_level
                if succ not in visited:
                    visited.add(succ)
                    queue.append((succ, new_level))

# 统计信息
total_concepts = len(concept_info)
total_edges = sum(len(succs) for succs in graph.values())
level_dist = defaultdict(int)
for lvl in levels.values():
    level_dist[lvl] += 1

# 分类统计
category_stats = defaultdict(lambda: {'count': 0, 'total_difficulty': 0, 'total_hours': 0})
for cid, info in concept_info.items():
    cat = info['category']
    category_stats[cat]['count'] += 1
    category_stats[cat]['total_difficulty'] += info.get('difficulty', 1)
    category_stats[cat]['total_hours'] += info.get('hours', 10)

# 枢纽概念
connectivity = {}
for cid in concept_info:
    out_degree = len(graph.get(cid, []))
    in_degree = len(reverse_graph.get(cid, []))
    connectivity[cid] = out_degree + in_degree

hub_concepts = sorted(connectivity.items(), key=lambda x: x[1], reverse=True)[:15]

# 高级概念
advanced_concepts = sorted(
    [(cid, len(reverse_graph.get(cid, []))) for cid in concept_info if cid in reverse_graph],
    key=lambda x: x[1],
    reverse=True
)[:15]

# 生成报告
report_lines = [
    "# FormalMath 概念依赖网络分析报告",
    "",
    "## 1. 总体统计",
    "",
    "| 指标 | 数值 |",
    "|------|------|",
    f"| 概念总数 | {total_concepts} |",
    f"| 依赖关系总数 | {total_edges} |",
    f"| 平均每个概念的后继 | {total_edges / total_concepts:.2f} |",
    f"| 层级深度 | {max(levels.values()) if levels else 0} |",
    "",
    "## 2. 层级分布",
    "",
    "| 层级 | 概念数量 | 占比 |",
    "|------|----------|------|",
]

for level in sorted(level_dist.keys()):
    count = level_dist[level]
    pct = count / total_concepts * 100
    report_lines.append(f"| L{level} | {count} | {pct:.1f}% |")

report_lines.extend([
    "",
    "## 3. 分支统计",
    "",
    "| 分支 | 概念数 | 平均难度 | 总学习时长(小时) |",
    "|------|--------|----------|------------------|",
])

for cat, stats in sorted(category_stats.items(), key=lambda x: x[1]['count'], reverse=True):
    avg_diff = stats['total_difficulty'] / stats['count'] if stats['count'] > 0 else 0
    report_lines.append(f"| {cat} | {stats['count']} | {avg_diff:.1f} | {stats['total_hours']} |")

report_lines.extend([
    "",
    "## 4. 枢纽概念（连接度最高）",
    "",
    "| 排名 | 概念 | 分类 | 连接度 | 说明 |",
    "|------|------|------|--------|------|",
])

for i, (cid, conn) in enumerate(hub_concepts, 1):
    name = concept_info[cid]['name']
    cat = concept_info[cid]['category']
    report_lines.append(f"| {i} | {name} | {cat} | {conn} | 核心枢纽 |")

report_lines.extend([
    "",
    "## 5. 基础概念（学习起点）",
    "",
    "| 概念 | 分类 | 预计学时 |",
    "|------|------|----------|",
])

for cid in basic_concepts[:20]:
    name = concept_info[cid]['name']
    cat = concept_info[cid]['category']
    hours = concept_info[cid].get('hours', 10)
    report_lines.append(f"| {name} | {cat} | {hours} |")

if len(basic_concepts) > 20:
    report_lines.append(f"\n*... 共 {len(basic_concepts)} 个基础概念*\n")

report_lines.extend([
    "",
    "## 6. 高级概念（依赖最多）",
    "",
    "| 排名 | 概念 | 分类 | 前置依赖数 |",
    "|------|------|------|------------|",
])

for i, (cid, deps) in enumerate(advanced_concepts, 1):
    name = concept_info[cid]['name']
    cat = concept_info[cid]['category']
    report_lines.append(f"| {i} | {name} | {cat} | {deps} |")

report_lines.extend([
    "",
    "## 7. 分支间依赖关系",
    "",
    "### 7.1 主要依赖流向",
    "",
    "| 源分支 | 目标分支 | 依赖强度 |",
    "|--------|----------|----------|",
])

branch_deps = []
for link in category_data.get('links', []):
    branch_deps.append((link['source'], link['target'], link['value']))

branch_deps.sort(key=lambda x: x[2], reverse=True)
for src, tgt, val in branch_deps[:25]:
    report_lines.append(f"| {src} | {tgt} | {val} |")

report_lines.extend([
    "",
    "## 8. 学习路径建议",
    "",
    "### 8.1 初学者路径（基础概念优先）",
    "",
    "建议从以下基础概念开始：",
    "",
    "1. **数学基础**：集合论、实数理论、二元运算",
    "2. **分析基础**：极限、连续性",
    "3. **代数基础**：群、环、域",
    "4. **几何基础**：拓扑空间",
    "",
    "### 8.2 进阶路径（按分支深入）",
    "",
    "- **分析学**：极限 → 导数 → 积分 → 级数 → 测度论 → 泛函分析",
    "- **代数学**：群 → 环 → 域 → 向量空间 → 线性代数 → 模论",
    "- **几何拓扑**：拓扑空间 → 流形 → 黎曼几何 → 辛几何",
    "- **数论**：同余 → 二次剩余 → 椭圆曲线 → 模形式",
    "",
    "### 8.3 跨分支学习建议",
    "",
    "某些概念是多个分支的交汇点，建议重点关注：",
    "",
    "- **线性代数**：连接代数、分析、几何",
    "- **流形**：连接几何、拓扑、分析",
    "- **Langlands纲领**：连接数论、代数几何、表示论",
    "",
    "## 9. 可视化图表",
    "",
    "本次生成了以下可视化图表：",
    "",
    "1. **层次结构图** (`concept_hierarchy.mmd`): 按学习层级展示概念组织",
    "2. **关键路径图** (`concept_critical_path.mmd`): 展示核心概念的依赖链",
    "3. **分支依赖图** (`concept_branch_dependency.mmd`): 展示数学分支间的依赖关系",
    "4. **学习路径图** (`concept_learning_path.mmd`): 推荐的学习路线图",
    "",
    "## 10. 网络特征分析",
    "",
    f"### 10.1 网络密度",
    f"概念依赖网络的密度反映了概念间的关联紧密程度。本网络包含 {total_concepts} 个概念和 {total_edges} 条依赖边。",
    "",
    f"### 10.2 层级结构",
    f"概念按学习依赖关系被组织为 {max(levels.values()) + 1 if levels else 0} 个层级，形成了清晰的学习进阶路径。",
    "",
    "### 10.3 核心-边缘结构",
    "枢纽概念（如范畴论、群、线性代数）处于网络核心位置，连接大量其他概念；",
    "而专业应用概念（如金融数学、生物数学中的特定概念）处于网络边缘。",
    "",
    "---",
    "",
    "*报告生成时间: 2026年4月*",
    "*数据来源: FormalMath 概念图谱 v3.0*",
    f"*概念总数: {total_concepts} | 依赖关系: {total_edges} | 最大深度: {max(levels.values()) if levels else 0}*",
])

with open('concept_dependency_analysis_report.md', 'w', encoding='utf-8') as f:
    f.write('\n'.join(report_lines))

print('Updated concept_dependency_analysis_report.md')

# 同时生成综合可视化数据
viz_summary = {
    'metadata': {
        'version': '3.0',
        'generated_date': '2026-04-04',
        'total_concepts': total_concepts,
        'total_dependencies': total_edges,
        'max_level': max(levels.values()) if levels else 0
    },
    'statistics': {
        'total_concepts': total_concepts,
        'total_edges': total_edges,
        'avg_out_degree': round(total_edges / total_concepts, 2) if total_concepts > 0 else 0,
        'level_distribution': dict(sorted(level_dist.items())),
        'basic_concepts_count': len(basic_concepts),
        'max_depth': max(levels.values()) if levels else 0
    },
    'concepts_by_level': {},
    'hub_concepts': [
        {
            'id': cid,
            'name': concept_info[cid]['name'],
            'category': concept_info[cid]['category'],
            'connectivity': conn
        }
        for cid, conn in hub_concepts
    ],
    'basic_concepts': [
        {
            'id': cid,
            'name': concept_info[cid]['name'],
            'category': concept_info[cid]['category']
        }
        for cid in basic_concepts
    ]
}

# 按层级分组概念
for level in sorted(level_dist.keys()):
    concepts_at_level = [cid for cid, lvl in levels.items() if lvl == level]
    viz_summary['concepts_by_level'][f'L{level}'] = [
        {
            'id': cid,
            'name': concept_info[cid]['name'],
            'category': concept_info[cid]['category']
        }
        for cid in concepts_at_level
    ]

with open('concept_dependency_network_summary.json', 'w', encoding='utf-8') as f:
    json.dump(viz_summary, f, ensure_ascii=False, indent=2)

print('Generated concept_dependency_network_summary.json')
