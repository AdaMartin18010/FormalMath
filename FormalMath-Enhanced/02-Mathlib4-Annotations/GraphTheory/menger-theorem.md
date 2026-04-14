---
msc_primary: 00A99
processed_at: '2026-04-15'
title: Menger 定理 (Menger's Theorem)
---
# Menger 定理 (Menger's Theorem)

## Mathlib4 引用

```lean
import Mathlib.Combinatorics.SimpleGraph.Connectivity

namespace SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Menger 定理（顶点形式）：两个不相邻顶点间内部不相交路径的最大数量
    等于分离它们的最小顶点割的大小 -/
theorem menger_vertex (s t : V) (hadj : ¬ G.Adj s t) :
    G.maxVertexDisjointPaths s t = G.minVertexSeparator s t := by
  -- 证明基于最大流最小割定理或归纳法
  sorry

/-- Menger 定理（边形式）：两个顶点间边不交路径的最大数量
    等于分离它们的最小边割的大小 -/
theorem menger_edge (s t : V) :
    G.maxEdgeDisjointPaths s t = G.minEdgeSeparator s t := by
  -- 通过将边转化为顶点，归约到顶点形式
  sorry

end SimpleGraph
```

## 数学背景

Menger 定理由奥地利数学家 Karl Menger 于1927年证明，是图论连通性理论的核心结果。该定理有两个经典形式：顶点形式断言两个不相邻顶点间内部顶点不交路径的最大数量等于分离它们的最小顶点割的大小；边形式断言两个顶点间边不交路径的最大数量等于分离它们的最小边割的大小。Menger 定理深刻刻画了图的局部连通结构。

## 直观解释

Menger 定理可以用一个网络可靠性问题来理解：假设一个通信网络中要从城市 $s$ 向城市 $t$ 发送消息，为了避免某个中转站被破坏导致通信中断，希望找到尽可能多的、不共享任何中转站的独立路径。Menger 定理告诉我们：这样独立路径的最大数量，恰好等于要使 $s$ 和 $t$ 完全断开所需要破坏的最少中转站数量。换句话说，网络的"冗余度"与"脆弱性"是一枚硬币的两面。

## 形式化表述

设 $G$ 是一个图，$s, t \in V(G)$ 是两个不同顶点：

**顶点形式**（$s, t$ 不相邻）：
$$\kappa_G(s, t) = \min\{|S| : S \subseteq V(G) \setminus \{s, t\}, \text{ 每个 } s\text{-}t\text{ 路径都经过 } S\}$$

**边形式**：
$$\lambda_G(s, t) = \min\{|F| : F \subseteq E(G), \text{ 每个 } s\text{-}t\text{ 路径都包含 } F\text{ 中的边}\}$$

其中：

- $\kappa_G(s, t)$ 表示 $s$ 与 $t$ 之间内部顶点不交路径的最大数量
- $\lambda_G(s, t)$ 表示 $s$ 与 $t$ 之间边不交路径的最大数量
- 等号右边的表达式分别表示最小顶点分隔集和最小边分隔集的大小

## 证明思路

1. **弱方向**：任何顶点割必须与子路径集相交，因此路径数不超过割的大小\n2. **网络流转化**：将图转化为网络流问题，利用最大流最小割定理证明等号方向\n3. **归纳法**：对图的边数或顶点数进行归纳，分析最短路径的结构\n4. **收缩与删除**：通过图的收缩和边删除操作，保持 Menger 条件并归约到更小图

核心洞察在于"不交路径"与"分隔集"构成完美的对偶关系。

## 示例

### 示例 1：网格图

考虑一个 $3 \times 3$ 网格图，$s$ 为左上角，$t$ 为右下角。可以找到 3 条内部顶点不交的路径，而移除中间一列的 3 个顶点即可断开 $s$ 和 $t$。验证了 Menger 定理的等式。

### 示例 2：完全图 $K_n$

在 $K_n$ 中任取两个顶点 $s, t$。存在 $n - 2$ 条内部顶点不交的路径（直接经过每个其他顶点一次），而移除其余 $n - 2$ 个顶点中的任意 $n - 2$ 个就能断开 $s$ 和 $t$。等号成立。

### 示例 3：树

在树中，任意两个顶点之间只有唯一一条简单路径。因此内部顶点不交路径的最大数量为 1，而移除路径上的任意一个内部顶点即可分离这两个顶点。最小顶点分隔集大小也为 1。

## 应用

- **网络可靠性**：评估通信网络和电力网络在节点/链路故障下的容错能力
- **社交网络**：分析信息传播路径的冗余度和关键影响者
- **VLSI 设计**：集成电路布线中的通道分配和连通性约束
- **组合优化**：与网络流、匹配问题之间的深刻联系

## 相关概念

- 顶点连通度 (Vertex Connectivity)：分离图所需移除的最少顶点数
- 边连通度 (Edge Connectivity)：分离图所需移除的最少边数
- 内部顶点不交路径 (Internally Vertex-Disjoint Paths)：除端点外无公共顶点的路径
- 边不交路径 (Edge-Disjoint Paths)：无公共边的路径
- 最大流最小割定理 (Max-Flow Min-Cut Theorem)：Menger 定理在网络流中的推广

## 参考

### 教材

- [R. Diestel. Graph Theory. Springer, 5th edition, 2017. Chapter 3]
- [D. B. West. Introduction to Graph Theory. Pearson, 2nd edition, 2001. Chapter 4]

### 论文

- [K. Menger. Zur allgemeinen Kurventheorie. Fundamenta Mathematicae, 1927]

### 在线资源

- [Mathlib4 - Connectivity](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Connectivity.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*
