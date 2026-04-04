#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalMath 全局依赖图使用示例
==============================

本文件演示如何使用全局依赖图系统进行学习路径规划。
"""

from global_dependency_graph import (
    get_core_concepts,
    ConceptDependencyGraph,
    LearningPathGenerator,
    topological_sort_kahn,
    topological_sort_with_levels,
    generate_mermaid_graph,
    analyze_graph,
    KnowledgeDomain,
    KnowledgeLevel,
    DifficultyLevel
)


def example_1_basic_usage():
    """
    示例1：基础用法 - 构建图并执行拓扑排序
    """
    print("=" * 60)
    print("示例1：基础用法")
    print("=" * 60)
    
    # 1. 获取概念数据
    concepts = get_core_concepts()
    print(f"✓ 加载了 {len(concepts)} 个核心概念")
    
    # 2. 构建依赖图
    graph = ConceptDependencyGraph()
    graph.build_from_concepts(concepts)
    
    # 3. 分析图结构
    stats = analyze_graph(graph)
    print(f"✓ 节点数: {stats['total_concepts']}")
    print(f"✓ 边数: {stats['total_dependencies']}")
    print(f"✓ 平均前置数: {stats['avg_prerequisites']:.2f}")
    
    # 4. 拓扑排序
    sorted_ids = topological_sort_kahn(graph)
    print(f"✓ 拓扑排序完成: {len(sorted_ids)} 个节点")
    
    # 5. 显示前10个概念
    print("\n学习顺序前10个概念：")
    for i, cid in enumerate(sorted_ids[:10], 1):
        concept = graph.nodes[cid]
        print(f"  {i}. {concept.name} ({concept.domain.value})")


def example_2_learning_path():
    """
    示例2：生成个性化学习路径
    """
    print("\n" + "=" * 60)
    print("示例2：个性化学习路径生成")
    print("=" * 60)
    
    # 构建图
    concepts = get_core_concepts()
    graph = ConceptDependencyGraph()
    graph.build_from_concepts(concepts)
    
    # 创建路径生成器
    generator = LearningPathGenerator(graph)
    
    # 场景1：学习"群"论
    print("\n场景1：学习群论")
    print("-" * 40)
    path = generator.generate_path(
        target_concepts=["C017"],  # 群
        user_level=DifficultyLevel.ELEMENTARY
    )
    
    time_info = generator.estimate_learning_time(path)
    print(f"目标：群 (Group)")
    print(f"前置概念数：{time_info['concept_count']}")
    print(f"预计总时长：{time_info['total_hours']:.1f} 小时")
    print(f"预计天数（每天4小时）：{time_info['total_days']:.1f} 天")
    print("\n学习路径：")
    for i, concept in enumerate(path, 1):
        print(f"  {i}. {concept.name:12s} ({concept.estimated_hours:4.1f}h) - {concept.domain.value}")
    
    # 场景2：学习"黎曼流形"
    print("\n场景2：学习黎曼流形")
    print("-" * 40)
    path = generator.generate_path(
        target_concepts=["C055"],  # 黎曼流形
        user_level=DifficultyLevel.INTERMEDIATE
    )
    
    time_info = generator.estimate_learning_time(path)
    print(f"目标：黎曼流形 (Riemannian Manifold)")
    print(f"前置概念数：{time_info['concept_count']}")
    print(f"预计总时长：{time_info['total_hours']:.1f} 小时")
    print(f"各领域分布：")
    for domain, hours in time_info['by_domain'].items():
        print(f"  - {domain}: {hours:.1f} 小时")


def example_3_prerequisites():
    """
    示例3：查询概念的前置依赖
    """
    print("\n" + "=" * 60)
    print("示例3：前置依赖查询")
    print("=" * 60)
    
    concepts = get_core_concepts()
    graph = ConceptDependencyGraph()
    graph.build_from_concepts(concepts)
    
    # 查询"朗兰兹纲领"的所有前置
    target = "C096"
    concept = graph.nodes[target]
    print(f"\n目标概念：{concept.name} ({concept.name_en})")
    print(f"难度等级：{concept.difficulty.name}")
    print(f"知识层次：{concept.level.name}")
    
    # 直接前置
    direct_prereqs = graph.get_prerequisites(target, recursive=False)
    print(f"\n直接前置概念 ({len(direct_prereqs)}个)：")
    for prereq_id in sorted(direct_prereqs):
        prereq = graph.nodes[prereq_id]
        print(f"  - {prereq.name} ({prereq_id})")
    
    # 所有前置（递归）
    all_prereqs = graph.get_prerequisites(target, recursive=True)
    print(f"\n全部前置概念 ({len(all_prereqs)}个)：")
    
    # 按领域分组
    by_domain = {}
    for prereq_id in all_prereqs:
        prereq = graph.nodes[prereq_id]
        domain = prereq.domain.value
        if domain not in by_domain:
            by_domain[domain] = []
        by_domain[domain].append(prereq.name)
    
    for domain, names in sorted(by_domain.items()):
        print(f"  {domain}: {len(names)}个")


def example_4_level_analysis():
    """
    示例4：层次化分析
    """
    print("\n" + "=" * 60)
    print("示例4：知识层次分析")
    print("=" * 60)
    
    concepts = get_core_concepts()
    graph = ConceptDependencyGraph()
    graph.build_from_concepts(concepts)
    
    # 按层次分组排序
    by_level = topological_sort_with_levels(graph)
    
    for level, concept_ids in by_level.items():
        print(f"\n{level.name} 层次 ({len(concept_ids)}个概念)：")
        
        # 按领域再分组
        by_domain = {}
        for cid in concept_ids:
            domain = graph.nodes[cid].domain.value
            if domain not in by_domain:
                by_domain[domain] = []
            by_domain[domain].append(graph.nodes[cid].name)
        
        for domain, names in sorted(by_domain.items()):
            print(f"  [{domain}] {', '.join(names[:5])}" + 
                  ("..." if len(names) > 5 else ""))


def example_5_domain_focus():
    """
    示例5：特定领域学习路径
    """
    print("\n" + "=" * 60)
    print("示例5：代数领域完整学习路径")
    print("=" * 60)
    
    concepts = get_core_concepts()
    graph = ConceptDependencyGraph()
    graph.build_from_concepts(concepts)
    
    # 获取代数领域的所有概念
    algebra_concepts = [
        c.id for c in concepts 
        if c.domain == KnowledgeDomain.ALGEBRA
    ]
    
    print(f"\n代数领域共 {len(algebra_concepts)} 个核心概念：")
    
    # 构建子图并排序
    sub_graph = ConceptDependencyGraph()
    for cid in algebra_concepts:
        sub_graph.add_concept(graph.nodes[cid])
    
    for cid in algebra_concepts:
        for prereq in graph.reverse_edges[cid]:
            if prereq in algebra_concepts:
                sub_graph.add_dependency(prereq, cid)
    
    sorted_algebra = topological_sort_kahn(sub_graph)
    
    print("\n推荐学习顺序：")
    for i, cid in enumerate(sorted_algebra, 1):
        concept = graph.nodes[cid]
        print(f"  {i:2d}. {concept.name:15s} (难度:{concept.difficulty.value}) "
              f"[{concept.estimated_hours:.1f}h]")


def main():
    """
    运行所有示例
    """
    print("\n" + "=" * 60)
    print("FormalMath 全局依赖图使用示例集")
    print("=" * 60)
    
    example_1_basic_usage()
    example_2_learning_path()
    example_3_prerequisites()
    example_4_level_analysis()
    example_5_domain_focus()
    
    print("\n" + "=" * 60)
    print("所有示例运行完成！")
    print("=" * 60)


if __name__ == "__main__":
    main()
