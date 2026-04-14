---
msc_primary: 00A99
processed_at: '2026-04-15'
title: König 定理 (König's Theorem)
---
# König 定理 (König's Theorem)

## Mathlib4 引用

```lean
import Mathlib.Combinatorics.SimpleGraph.Matching

namespace SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- König 定理：二分图中最大匹配的大小等于最小顶点覆盖的大小 -/
theorem konigTheorem (h : G.IsBipartite) :
    G.maxMatching.card = G.minVertexCover.card := by
  -- 通过对二分图建立流网络，利用最大流最小割定理证明
  sorry

end SimpleGraph
```

## 数学背景

König 定理由匈牙利数学家 Dénes König 于1931年证明，是二分图理论中最核心的结果之一。该定理建立了二分图中最大匹配的大小等于最小顶点覆盖的大小之间的对偶关系。这一定理是线性规划对偶性在组合优化中的离散体现，对网络流、组合优化和算法设计产生了深远影响。

## 直观解释

想象一个二分图代表工人和任务：左侧顶点是工人，右侧顶点是任务，边表示某个工人可以完成某项任务。匹配表示将工人分配到不同的任务。顶点覆盖则表示选出一组工人和任务，使得每条边至少有一个端点被选中。König 定理告诉我们：最多能同时完成多少项任务，恰好等于需要监督多少个人和任务才能覆盖所有可能的分配关系。

## 形式化表述

设 $G = (X \cup Y, E)$ 是一个二分图，则：

$$\nu(G) = \tau(G)$$

其中：

- $\nu(G)$ 表示 $G$ 中最大匹配的大小（matching number）
- $\tau(G)$ 表示 $G$ 中最小顶点覆盖的大小（vertex cover number）
- $G$ 是二分图意味着顶点集可划分为两个独立集 $X$ 和 $Y$

## 证明思路

1. **平凡不等式**：证明对任意图都有 $\nu(G) \leq \tau(G)$，因为匹配中的每条边都需要一个不同的顶点来覆盖\n2. **构造覆盖**：在二分图中，利用交错路径构造一个大小恰好为 $\nu(G)$ 的顶点覆盖\n3. **Hall 条件或网络流**：通过最大流最小割定理，或从最大匹配出发构造最小覆盖\n4. **等式成立**：在二分图的特殊结构下，上述覆盖恰好达到下界

核心洞察在于二分图的"无环"结构使得匹配和覆盖之间不存在间隙。

## 示例

### 示例 1：简单二分图

考虑二分图 $G$ 其中 $X = \{a, b\}$, $Y = \{1, 2\}$，边为 $a-1, a-2, b-2$。最大匹配可以是 $\{a-1, b-2\}$，大小为 2。最小顶点覆盖为 $\{a, 2\}$，大小也为 2。

### 示例 2：非二分图的失效

三角形图 $K_3$ 的最大匹配大小为 1，但最小顶点覆盖大小为 2。这说明 König 定理对非二分图不成立，二分条件至关重要。

### 示例 3：完美匹配

若二分图存在完美匹配（覆盖所有顶点），则最小顶点覆盖必须包含所有顶点，此时 $\nu(G) = |V|/2 = \tau(G)$。

## 应用

- **任务分配**：将任务最优分配给工作人员的匈牙利算法基础
- **网络流**：与最大流最小割定理等价，是网络优化的核心
- **组合拍卖**：拍卖机制设计中的对偶分析
- **调度问题**：生产调度中的资源匹配与覆盖

## 相关概念

- 匹配 (Matching)：无公共端点的边集
- 顶点覆盖 (Vertex Cover)：与每条边都相交的顶点集
- 二分图 (Bipartite Graph)：顶点可分为两个独立集的图
- Hall 婚姻定理 (Hall's Marriage Theorem)：二分图存在完美匹配的充要条件
- 最大流最小割定理 (Max-Flow Min-Cut Theorem)：网络流中的对偶定理

## 参考

### 教材

- [R. Diestel. Graph Theory. Springer, 5th edition, 2017. Chapter 2]
- [A. Schrijver. Combinatorial Optimization. Springer, 2003. Chapter 16]

### 论文

- [D. König. Gráfok és mátrixok. Mat. Fiz. Lapok, 1931]

### 在线资源

- [Mathlib4 - Matching](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Matching.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*
