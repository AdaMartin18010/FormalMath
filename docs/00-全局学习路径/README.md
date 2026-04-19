---
msc_primary: 00

  - 00A99
title: 全局学习路径
processed_at: '2026-04-05'
---
# 全局学习路径

**目录编号**: DOC.GLP  
**主题分类**: 全局学习路径规划  
**创建日期**: 2026年4月4日  
**维护状态**: 持续更新

---

## 📋 目录

- [概念前置知识全局图谱](./01-概念前置知识全局图谱.md) - 100节点全局依赖图与拓扑排序算法

---

## 概述

全局学习路径模块提供FormalMath项目概念体系的结构化学习规划功能，包括：

- **全局依赖图**：100个数学概念的有向图表示
- **拓扑排序算法**：Kahn算法与DFS算法实现
- **学习路径生成器**：个性化学习路径推荐
- **可视化输出**：Mermaid图表与JSON数据导出

---

## 快速开始

### 运行Python脚本

```bash
cd project
python global_dependency_graph.py

```

### 使用Python API

```python
from global_dependency_graph import (
    get_core_concepts,
    ConceptDependencyGraph,
    LearningPathGenerator,
    topological_sort_kahn
)

# 获取概念数据
concepts = get_core_concepts()

# 构建依赖图
graph = ConceptDependencyGraph()
graph.build_from_concepts(concepts)

# 拓扑排序
sorted_ids = topological_sort_kahn(graph)

# 生成学习路径
generator = LearningPathGenerator(graph)
path = generator.generate_path(["C017"], DifficultyLevel.INTERMEDIATE)

```

---

## 文件结构

```

docs/00-全局学习路径/
├── README.md                          # 本文件
└── 01-概念前置知识全局图谱.md          # 详细文档（约15,000字）

project/
└── global_dependency_graph.py         # Python算法实现

output/                                # 生成文件（运行后）
├── concept_dependency_graph.json      # 完整图数据
├── learning_path_group.json           # 示例学习路径
├── mermaid_graph.md                   # 全局Mermaid图
├── mermaid_foundation.md              # 基础数学子图
├── mermaid_algebra.md                 # 代数子图
├── mermaid_analysis.md                # 分析子图
├── mermaid_geometry.md                # 几何子图
├── mermaid_topology.md                # 拓扑子图
├── mermaid_number_theory.md           # 数论子图
├── mermaid_discrete.md                # 离散数学子图
└── mermaid_interdisciplinary.md       # 交叉领域子图

```

---

## 统计概览

| 指标 | 数值 |
|------|------|
| 概念总数 | 100 |
| 依赖边数 | 158 |
| 平均前置数 | 1.58 |
| 根概念数 | 2（关系、逻辑） |
| 叶概念数 | 31 |
| 知识领域 | 8个 |
| 知识层次 | 4层 |

---

## 贡献指南

欢迎提交Issue和PR来改进全局依赖图：

1. 概念数据改进：修正依赖关系或添加新属性
2. 算法优化：提升拓扑排序或路径生成效率
3. 可视化增强：改进Mermaid图表样式
4. 文档完善：补充示例或修正错误

---

**最后更新**: 2026年4月4日
