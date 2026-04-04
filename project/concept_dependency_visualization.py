#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalMath 概念依赖网络可视化生成器
生成层次结构图、关键路径图、分支依赖图、学习路径推荐图
"""

import json
import yaml
from collections import defaultdict, deque
from typing import Dict, List, Set, Tuple
import os

# 加载数据
def load_data():
    """加载现有数据文件"""
    base_path = os.path.dirname(os.path.abspath(__file__))
    
    # 加载可视化数据
    with open(os.path.join(base_path, 'visualization_data_400.json'), 'r', encoding='utf-8') as f:
        viz_data = json.load(f)
    
    # 加载分类图数据
    with open(os.path.join(base_path, 'category_graph_400.json'), 'r', encoding='utf-8') as f:
        category_data = json.load(f)
    
    # 加载前置关系数据
    with open(os.path.join(base_path, 'concept_prerequisites_400.yaml'), 'r', encoding='utf-8') as f:
        prereq_data = yaml.safe_load(f)
    
    return viz_data, category_data, prereq_data

# 构建依赖图
def build_dependency_graph(prereq_data: dict) -> Tuple[Dict, Dict, Dict]:
    """构建概念依赖图，返回前置图、后继图和概念信息"""
    graph = defaultdict(list)  # 概念 -> 后继
    reverse_graph = defaultdict(list)  # 概念 -> 前置
    concept_info = {}
    
    if 'concepts' in prereq_data:
        for concept in prereq_data['concepts']:
            concept_id = concept['concept_id']
            concept_info[concept_id] = {
                'name': concept['name'],
                'category': concept['category'],
                'difficulty': concept.get('difficulty', 1),
                'hours': concept.get('estimated_hours', 10)
            }
            
            # 添加后继关系
            if 'successors' in concept:
                for succ in concept['successors']:
                    graph[concept_id].append(succ['concept_id'])
            
            # 添加前置关系
            if 'prerequisites' in concept:
                for prereq in concept['prerequisites']:
                    reverse_graph[concept_id].append(prereq['concept_id'])
                    graph[prereq['concept_id']].append(concept_id)
    
    return dict(graph), dict(reverse_graph), concept_info

# 计算概念层级
def calculate_levels(reverse_graph: Dict, concept_info: Dict) -> Dict:
    """计算每个概念的学习层级（拓扑排序）"""
    levels = {}
    in_degree = defaultdict(int)
    
    # 计算入度
    for concept in concept_info:
        if concept in reverse_graph:
            in_degree[concept] = len(reverse_graph[concept])
        else:
            in_degree[concept] = 0
    
    # BFS分层
    queue = deque()
    for concept in concept_info:
        if in_degree[concept] == 0:
            levels[concept] = 0
            queue.append(concept)
    
    while queue:
        current = queue.popleft()
        current_level = levels[current]
        
        for neighbor in graph.get(current, []):
            in_degree[neighbor] -= 1
            if in_degree[neighbor] == 0:
                levels[neighbor] = current_level + 1
                queue.append(neighbor)
    
    return levels

# 生成层次结构图
def generate_hierarchy_mermaid(graph: Dict, concept_info: Dict, levels: Dict) -> str:
    """生成层次结构的Mermaid图"""
    lines = ["graph TD"]
    lines.append("    %% 层次结构图 - 按学习层级组织")
    lines.append("")
    
    # 按层级分组
    level_groups = defaultdict(list)
    for concept_id, level in levels.items():
        if concept_id in concept_info:
            level_groups[level].append(concept_id)
    
    # 生成层级子图
    colors = ["#E3F2FD", "#E8F5E9", "#FFF3E0", "#FCE4EC", "#F3E5F5", "#E0F7FA", "#FFF8E1", "#F1F8E9"]
    
    for level in sorted(level_groups.keys()):
        concepts = level_groups[level]
        if not concepts:
            continue
        
        color = colors[level % len(colors)]
        lines.append(f"    subgraph L{level}[层级 {level}]")
        lines.append(f"        style L{level} fill:{color}")
        
        for concept_id in concepts:
            name = concept_info[concept_id]['name']
            category = concept_info[concept_id]['category']
            lines.append(f'        {concept_id}["{name}<br/><small>{category}</small>"]')
        
        lines.append("    end")
        lines.append("")
    
    # 添加连接
    added_edges = set()
    for concept_id, successors in graph.items():
        if concept_id not in concept_info:
            continue
        for succ in successors:
            if succ in concept_info and (concept_id, succ) not in added_edges:
                lines.append(f"    {concept_id} --> {succ}")
                added_edges.add((concept_id, succ))
    
    return "\n".join(lines)

# 生成关键路径图
def generate_critical_path_mermaid(graph: Dict, concept_info: Dict, levels: Dict) -> str:
    """生成关键路径Mermaid图（显示最重要的学习路径）"""
    lines = ["graph LR"]
    lines.append("    %% 关键路径图 - 核心概念依赖链")
    lines.append("")
    
    # 定义核心概念（基础且重要的概念）
    core_concepts = [
        # 分析学核心链
        ("limit", "极限"),
        ("continuity", "连续性"),
        ("derivative", "导数"),
        ("riemann_integral", "积分"),
        ("infinite_series", "级数"),
        ("measure_theory", "测度论"),
        ("lebesgue_integral", "Lebesgue积分"),
        ("functional_analysis", "泛函分析"),
        # 代数学核心链
        ("group", "群"),
        ("ring", "环"),
        ("field", "域"),
        ("vector_space", "向量空间"),
        ("linear_algebra", "线性代数"),
        ("module", "模"),
        ("homological_algebra", "同调代数"),
        # 几何拓扑核心链
        ("topological_space", "拓扑空间"),
        ("manifold", "流形"),
        ("riemannian_metric", "黎曼度量"),
        ("curvature", "曲率"),
        # 数论逻辑核心链
        ("set_theory", "集合论"),
        ("congruence", "同余"),
        ("elliptic_curve", "椭圆曲线"),
        ("modular_form", "模形式"),
        ("langlands_program", "Langlands纲领"),
    ]
    
    # 过滤存在的概念
    existing_core = [(cid, name) for cid, name in core_concepts if cid in concept_info]
    
    # 生成核心节点
    lines.append("    subgraph 分析学核心[分析学核心路径]")
    lines.append("        style 分析学核心 fill:#E3F2FD")
    analysis_chain = ["limit", "continuity", "derivative", "riemann_integral", "infinite_series", "measure_theory", "functional_analysis"]
    for cid in analysis_chain:
        if cid in concept_info:
            name = concept_info[cid]['name']
            lines.append(f'        {cid}["{name}"]')
    lines.append("    end")
    lines.append("")
    
    lines.append("    subgraph 代数学核心[代数学核心路径]")
    lines.append("        style 代数学核心 fill:#E8F5E9")
    algebra_chain = ["group", "ring", "field", "vector_space", "linear_algebra", "module", "homological_algebra"]
    for cid in algebra_chain:
        if cid in concept_info:
            name = concept_info[cid]['name']
            lines.append(f'        {cid}["{name}"]')
    lines.append("    end")
    lines.append("")
    
    lines.append("    subgraph 几何拓扑核心[几何拓扑核心路径]")
    lines.append("        style 几何拓扑核心 fill:#FFF3E0")
    geo_chain = ["topological_space", "manifold", "riemannian_metric", "curvature"]
    for cid in geo_chain:
        if cid in concept_info:
            name = concept_info[cid]['name']
            lines.append(f'        {cid}["{name}"]')
    lines.append("    end")
    lines.append("")
    
    lines.append("    subgraph 数论高级核心[数论高级核心路径]")
    lines.append("        style 数论高级核心 fill:#FCE4EC")
    number_chain = ["set_theory", "congruence", "elliptic_curve", "modular_form", "langlands_program"]
    for cid in number_chain:
        if cid in concept_info:
            name = concept_info[cid]['name']
            lines.append(f'        {cid}["{name}"]')
    lines.append("    end")
    lines.append("")
    
    # 添加关键连接
    critical_edges = [
        ("limit", "continuity"),
        ("continuity", "derivative"),
        ("derivative", "riemann_integral"),
        ("limit", "infinite_series"),
        ("riemann_integral", "measure_theory"),
        ("measure_theory", "functional_analysis"),
        ("group", "ring"),
        ("ring", "field"),
        ("field", "vector_space"),
        ("vector_space", "linear_algebra"),
        ("module", "homological_algebra"),
        ("topological_space", "manifold"),
        ("manifold", "riemannian_metric"),
        ("riemannian_metric", "curvature"),
        ("congruence", "elliptic_curve"),
        ("elliptic_curve", "modular_form"),
        ("modular_form", "langlands_program"),
    ]
    
    lines.append("    %% 关键路径连接")
    for src, tgt in critical_edges:
        if src in concept_info and tgt in concept_info:
            lines.append(f"    {src} --> {tgt}")
    
    lines.append("")
    lines.append("    %% 跨分支连接")
    cross_edges = [
        ("functional_analysis", "linear_algebra"),
        ("curvature", "functional_analysis"),
        ("homological_algebra", "langlands_program"),
    ]
    for src, tgt in cross_edges:
        if src in concept_info and tgt in concept_info:
            lines.append(f"    {src} -.-> {tgt}")
    
    return "\n".join(lines)

# 生成分支依赖图
def generate_branch_dependency_mermaid(category_data: Dict) -> str:
    """生成分支间依赖关系的Mermaid图"""
    lines = ["graph TB"]
    lines.append("    %% 分支依赖图 - 数学分支间的依赖关系")
    lines.append("")
    
    # 分支颜色映射
    branch_colors = {
        "分析学": "#E3F2FD",
        "代数学": "#E8F5E9",
        "几何拓扑": "#FFF3E0",
        "数论逻辑": "#FCE4EC",
        "概率统计": "#F3E5F5",
        "最优化": "#E0F7FA",
        "控制论": "#FFF8E1",
        "信息论": "#F1F8E9",
        "密码学": "#FFEBEE",
        "金融数学": "#E8EAF6",
        "生物数学": "#E0F2F1",
        "计算数学": "#FFF9C4",
        "物理数学": "#F3E5F5",
        "数据科学": "#E1F5FE",
        "范畴论": "#FBE9E7",
        "同调代数": "#F3E5F5",
        "代数几何": "#E8F5E9",
        "表示论": "#FFF3E0",
        "数论高级": "#FCE4EC",
        "动力系统": "#E0F7FA",
        "数理逻辑": "#E1F5FE",
    }
    
    # 生成分支节点
    lines.append("    %% 核心基础分支")
    core_branches = ["数论逻辑", "代数学", "分析学", "几何拓扑"]
    for node in category_data.get('nodes', []):
        branch_id = node['id']
        count = node['count']
        if branch_id in core_branches:
            color = branch_colors.get(branch_id, "#E3F2FD")
            lines.append(f'    {branch_id}["{branch_id}<br/>{count}个概念"]')
            lines.append(f"    style {branch_id} fill:{color},stroke:#333,stroke-width:3px")
    
    lines.append("")
    lines.append("    %% 应用分支")
    app_branches = ["概率统计", "最优化", "控制论", "信息论", "计算数学"]
    for node in category_data.get('nodes', []):
        branch_id = node['id']
        count = node['count']
        if branch_id in app_branches:
            color = branch_colors.get(branch_id, "#E3F2FD")
            lines.append(f'    {branch_id}["{branch_id}<br/>{count}个概念"]')
            lines.append(f"    style {branch_id} fill:{color}")
    
    lines.append("")
    lines.append("    %% 交叉分支")
    cross_branches = ["范畴论", "同调代数", "代数几何", "表示论", "数论高级", "动力系统", "数理逻辑"]
    for node in category_data.get('nodes', []):
        branch_id = node['id']
        count = node['count']
        if branch_id in cross_branches:
            color = branch_colors.get(branch_id, "#E3F2FD")
            lines.append(f'    {branch_id}["{branch_id}<br/>{count}个概念"]')
            lines.append(f"    style {branch_id} fill:{color}")
    
    lines.append("")
    lines.append("    %% 专业应用分支")
    prof_branches = ["密码学", "金融数学", "生物数学", "物理数学", "数据科学"]
    for node in category_data.get('nodes', []):
        branch_id = node['id']
        count = node['count']
        if branch_id in prof_branches:
            color = branch_colors.get(branch_id, "#E3F2FD")
            lines.append(f'    {branch_id}["{branch_id}<br/>{count}个概念"]')
            lines.append(f"    style {branch_id} fill:{color}")
    
    # 添加依赖连接
    lines.append("")
    lines.append("    %% 基础依赖关系")
    
    # 按强度分类连接
    strong_deps = []
    medium_deps = []
    weak_deps = []
    
    for link in category_data.get('links', []):
        src = link['source']
        tgt = link['target']
        value = link['value']
        if value >= 6:
            strong_deps.append((src, tgt, value))
        elif value >= 3:
            medium_deps.append((src, tgt, value))
        else:
            weak_deps.append((src, tgt, value))
    
    for src, tgt, val in strong_deps:
        lines.append(f"    {src} ==>|{val}| {tgt}")
    
    lines.append("")
    lines.append("    %% 中等依赖关系")
    for src, tgt, val in medium_deps:
        lines.append(f"    {src} -->|{val}| {tgt}")
    
    lines.append("")
    lines.append("    %% 弱依赖关系")
    for src, tgt, val in weak_deps:
        lines.append(f"    {src} -.->|{val}| {tgt}")
    
    return "\n".join(lines)

# 生成学习路径推荐图
def generate_learning_path_mermaid(graph: Dict, concept_info: Dict, levels: Dict) -> str:
    """生成学习路径推荐Mermaid图"""
    lines = ["graph TD"]
    lines.append("    %% 学习路径推荐图 - 从基础到高级的学习路线")
    lines.append("")
    
    # 定义学习路径
    learning_paths = {
        "数学分析之路": [
            ("real_numbers", "实数理论", 1),
            ("limit", "极限", 2),
            ("continuity", "连续性", 2),
            ("derivative", "导数", 2),
            ("riemann_integral", "Riemann积分", 2),
            ("infinite_series", "级数", 3),
            ("measure_theory", "测度论", 3),
            ("lebesgue_integral", "Lebesgue积分", 3),
            ("functional_analysis", "泛函分析", 4),
        ],
        "代数结构之路": [
            ("set_theory", "集合论", 1),
            ("binary_operations", "二元运算", 1),
            ("group", "群论", 2),
            ("ring", "环论", 2),
            ("field", "域论", 2),
            ("vector_space", "向量空间", 2),
            ("linear_algebra", "线性代数", 2),
            ("module", "模论", 3),
            ("commutative_algebra", "交换代数", 3),
            ("algebraic_geometry", "代数几何", 4),
        ],
        "几何拓扑之路": [
            ("topology_basic", "拓扑基础", 1),
            ("topological_space", "拓扑空间", 2),
            ("continuous_map", "连续映射", 2),
            ("compactness", "紧致性", 2),
            ("manifold", "流形", 3),
            ("riemannian_metric", "黎曼度量", 3),
            ("curvature", "曲率", 3),
            ("symplectic_geometry", "辛几何", 4),
        ],
        "数论探索之路": [
            ("divisibility", "整除理论", 1),
            ("congruence", "同余理论", 2),
            ("quadratic_residue", "二次剩余", 2),
            ("primitive_root", "原根", 2),
            ("elliptic_curve", "椭圆曲线", 3),
            ("modular_form", "模形式", 4),
            ("langlands_program", "Langlands纲领", 5),
        ],
    }
    
    colors = ["#C8E6C9", "#BBDEFB", "#FFE0B2", "#F8BBD9"]
    
    for idx, (path_name, concepts) in enumerate(learning_paths.items()):
        color = colors[idx % len(colors)]
        lines.append(f"    subgraph {path_name}[{path_name}]")
        lines.append(f"        style {path_name} fill:{color}")
        
        for cid, cname, difficulty in concepts:
            if cid in concept_info:
                shape = "([" if difficulty <= 2 else "[[" if difficulty <= 4 else "(("
                end_shape = "])" if difficulty <= 2 else "]]" if difficulty <= 4 else "))"
                lines.append(f'        {cid}{shape}"{cname}<br/>D{difficulty}"{end_shape}')
        
        lines.append("    end")
        lines.append("")
    
    # 添加路径内部连接
    lines.append("    %% 分析路径内部连接")
    analysis_flow = ["real_numbers", "limit", "continuity", "derivative", "riemann_integral", "infinite_series", "measure_theory", "lebesgue_integral", "functional_analysis"]
    for i in range(len(analysis_flow) - 1):
        if analysis_flow[i] in concept_info and analysis_flow[i+1] in concept_info:
            lines.append(f"    {analysis_flow[i]} --> {analysis_flow[i+1]}")
    
    lines.append("")
    lines.append("    %% 代数路径内部连接")
    algebra_flow = ["set_theory", "group", "ring", "field", "vector_space", "linear_algebra", "module", "commutative_algebra", "algebraic_geometry"]
    for i in range(len(algebra_flow) - 1):
        if algebra_flow[i] in concept_info and algebra_flow[i+1] in concept_info:
            lines.append(f"    {algebra_flow[i]} --> {algebra_flow[i+1]}")
    
    lines.append("")
    lines.append("    %% 几何拓扑路径内部连接")
    geo_flow = ["topology_basic", "topological_space", "continuous_map", "compactness", "manifold", "riemannian_metric", "curvature"]
    for i in range(len(geo_flow) - 1):
        if geo_flow[i] in concept_info and geo_flow[i+1] in concept_info:
            lines.append(f"    {geo_flow[i]} --> {geo_flow[i+1]}")
    
    lines.append("")
    lines.append("    %% 数论路径内部连接")
    number_flow = ["divisibility", "congruence", "quadratic_residue", "primitive_root", "elliptic_curve", "modular_form", "langlands_program"]
    for i in range(len(number_flow) - 1):
        if number_flow[i] in concept_info and number_flow[i+1] in concept_info:
            lines.append(f"    {number_flow[i]} --> {number_flow[i+1]}")
    
    lines.append("")
    lines.append("    %% 跨路径连接（虚线表示推荐关联学习）")
    cross_connections = [
        ("functional_analysis", "algebraic_geometry", "代数与分析的交汇"),
        ("curvature", "functional_analysis", "几何与分析"),
        ("langlands_program", "algebraic_geometry", "数论与几何"),
        ("linear_algebra", "topological_space", "代数与拓扑"),
    ]
    for src, tgt, note in cross_connections:
        if src in concept_info and tgt in concept_info:
            lines.append(f"    {src} -.->{tgt}")
    
    return "\n".join(lines)

# 生成分析报告
def generate_analysis_report(graph: Dict, concept_info: Dict, levels: Dict, category_data: Dict) -> str:
    """生成概念依赖网络分析报告"""
    
    # 统计信息
    total_concepts = len(concept_info)
    total_edges = sum(len(succs) for succs in graph.values())
    
    # 层级分布
    level_dist = defaultdict(int)
    for level in levels.values():
        level_dist[level] += 1
    
    # 分类统计
    category_stats = defaultdict(lambda: {'count': 0, 'total_difficulty': 0, 'total_hours': 0})
    for cid, info in concept_info.items():
        cat = info['category']
        category_stats[cat]['count'] += 1
        category_stats[cat]['total_difficulty'] += info.get('difficulty', 1)
        category_stats[cat]['total_hours'] += info.get('hours', 10)
    
    # 找出枢纽概念（连接数最多的概念）
    connectivity = {}
    for cid in concept_info:
        out_degree = len(graph.get(cid, []))
        in_degree = len(reverse_graph.get(cid, []))
        connectivity[cid] = out_degree + in_degree
    
    hub_concepts = sorted(connectivity.items(), key=lambda x: x[1], reverse=True)[:10]
    
    # 找出基础概念（没有前置依赖的概念）
    basic_concepts = [cid for cid in concept_info if cid not in reverse_graph or not reverse_graph[cid]]
    
    # 找出高级概念（依赖最多的概念）
    advanced_concepts = sorted(
        [(cid, len(reverse_graph.get(cid, []))) for cid in concept_info],
        key=lambda x: x[1],
        reverse=True
    )[:10]
    
    report = f"""# FormalMath 概念依赖网络分析报告

## 1. 总体统计

| 指标 | 数值 |
|------|------|
| 概念总数 | {total_concepts} |
| 依赖关系总数 | {total_edges} |
| 平均每个概念的后继 | {total_edges / total_concepts:.2f} |
| 层级深度 | {max(levels.values()) + 1 if levels else 0} |

## 2. 层级分布

| 层级 | 概念数量 | 占比 |
|------|----------|------|
"""
    
    for level in sorted(level_dist.keys()):
        count = level_dist[level]
        pct = count / total_concepts * 100
        report += f"| L{level} | {count} | {pct:.1f}% |\n"
    
    report += f"""
## 3. 分支统计

| 分支 | 概念数 | 平均难度 | 总学习时长(小时) |
|------|--------|----------|------------------|
"""
    
    for cat, stats in sorted(category_stats.items(), key=lambda x: x[1]['count'], reverse=True):
        avg_diff = stats['total_difficulty'] / stats['count'] if stats['count'] > 0 else 0
        report += f"| {cat} | {stats['count']} | {avg_diff:.1f} | {stats['total_hours']} |\n"
    
    report += f"""
## 4. 枢纽概念（连接度最高）

| 排名 | 概念 | 分类 | 连接度 | 说明 |
|------|------|------|--------|------|
"""
    
    for i, (cid, conn) in enumerate(hub_concepts, 1):
        name = concept_info[cid]['name']
        cat = concept_info[cid]['category']
        report += f"| {i} | {name} | {cat} | {conn} | 核心枢纽 |\n"
    
    report += f"""
## 5. 基础概念（学习起点）

| 概念 | 分类 | 预计学时 |
|------|------|----------|
"""
    
    for cid in basic_concepts[:15]:
        name = concept_info[cid]['name']
        cat = concept_info[cid]['category']
        hours = concept_info[cid].get('hours', 10)
        report += f"| {name} | {cat} | {hours} |\n"
    
    if len(basic_concepts) > 15:
        report += f"| ... | ... | ... |\n"
        report += f"\n*共 {len(basic_concepts)} 个基础概念*\n"
    
    report += f"""
## 6. 高级概念（依赖最多）

| 排名 | 概念 | 分类 | 前置依赖数 |
|------|------|------|------------|
"""
    
    for i, (cid, deps) in enumerate(advanced_concepts, 1):
        name = concept_info[cid]['name']
        cat = concept_info[cid]['category']
        report += f"| {i} | {name} | {cat} | {deps} |\n"
    
    report += f"""
## 7. 分支间依赖关系

"""
    
    # 统计分支间依赖
    branch_deps = defaultdict(lambda: defaultdict(int))
    for link in category_data.get('links', []):
        src = link['source']
        tgt = link['target']
        val = link['value']
        branch_deps[src][tgt] += val
    
    report += "### 7.1 主要依赖流向\n\n"
    report += "| 源分支 | 目标分支 | 依赖强度 |\n"
    report += "|--------|----------|----------|\n"
    
    all_deps = []
    for src, tgts in branch_deps.items():
        for tgt, val in tgts.items():
            all_deps.append((src, tgt, val))
    
    all_deps.sort(key=lambda x: x[2], reverse=True)
    for src, tgt, val in all_deps[:20]:
        report += f"| {src} | {tgt} | {val} |\n"
    
    report += f"""
## 8. 学习路径建议

### 8.1 初学者路径（基础概念优先）

建议从以下基础概念开始：

1. **数学基础**：集合论、实数理论、二元运算
2. **分析基础**：极限、连续性
3. **代数基础**：群、环、域
4. **几何基础**：拓扑空间

### 8.2 进阶路径（按分支深入）

- **分析学**：极限 → 导数 → 积分 → 级数 → 测度论 → 泛函分析
- **代数学**：群 → 环 → 域 → 向量空间 → 线性代数 → 模论
- **几何拓扑**：拓扑空间 → 流形 → 黎曼几何 → 辛几何
- **数论**：同余 → 二次剩余 → 椭圆曲线 → 模形式

### 8.3 跨分支学习建议

某些概念是多个分支的交汇点，建议重点关注：

- **线性代数**：连接代数、分析、几何
- **流形**：连接几何、拓扑、分析
- **Langlands纲领**：连接数论、代数几何、表示论

## 9. 可视化图表说明

本次生成了以下可视化图表：

1. **层次结构图** (`concept_hierarchy.mmd`): 按学习层级展示概念组织
2. **关键路径图** (`concept_critical_path.mmd`): 展示核心概念的依赖链
3. **分支依赖图** (`concept_branch_dependency.mmd`): 展示数学分支间的依赖关系
4. **学习路径图** (`concept_learning_path.mmd`): 推荐的学习路线图

---

*报告生成时间: 2026年4月*
*数据来源: FormalMath 概念图谱 v3.0*
"""
    
    return report

# 主函数
def main():
    print("Loading data...")
    viz_data, category_data, prereq_data = load_data()
    
    print("Building dependency graph...")
    global graph, reverse_graph, concept_info
    graph, reverse_graph, concept_info = build_dependency_graph(prereq_data)
    
    print("Calculating concept levels...")
    global levels
    levels = calculate_levels(reverse_graph, concept_info)
    
    # 生成层次结构图
    print("Generating hierarchy mermaid diagram...")
    hierarchy_mmd = generate_hierarchy_mermaid(graph, concept_info, levels)
    with open('concept_hierarchy.mmd', 'w', encoding='utf-8') as f:
        f.write(hierarchy_mmd)
    
    # 生成关键路径图
    print("Generating critical path mermaid diagram...")
    critical_path_mmd = generate_critical_path_mermaid(graph, concept_info, levels)
    with open('concept_critical_path.mmd', 'w', encoding='utf-8') as f:
        f.write(critical_path_mmd)
    
    # 生成分支依赖图
    print("Generating branch dependency mermaid diagram...")
    branch_dep_mmd = generate_branch_dependency_mermaid(category_data)
    with open('concept_branch_dependency.mmd', 'w', encoding='utf-8') as f:
        f.write(branch_dep_mmd)
    
    # 生成学习路径图
    print("Generating learning path mermaid diagram...")
    learning_path_mmd = generate_learning_path_mermaid(graph, concept_info, levels)
    with open('concept_learning_path.mmd', 'w', encoding='utf-8') as f:
        f.write(learning_path_mmd)
    
    # 生成分析报告
    print("Generating analysis report...")
    report = generate_analysis_report(graph, concept_info, levels, category_data)
    with open('concept_dependency_analysis_report.md', 'w', encoding='utf-8') as f:
        f.write(report)
    
    print("\nDone! Generated files:")
    print("  - concept_hierarchy.mmd")
    print("  - concept_critical_path.mmd")
    print("  - concept_branch_dependency.mmd")
    print("  - concept_learning_path.mmd")
    print("  - concept_dependency_analysis_report.md")

if __name__ == '__main__':
    main()
