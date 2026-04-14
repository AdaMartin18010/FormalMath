---
msc_primary: 00A99
processed_at: '2026-04-15'
title: Brooks 定理 (Brooks' Theorem)
---
# Brooks 定理 (Brooks' Theorem)

## Mathlib4 引用

```lean
import Mathlib.Combinatorics.SimpleGraph.Coloring

namespace SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Brooks 定理：连通图 G 的色数至多为 Δ(G)，
    除非 G 是完全图或奇圈 -/
theorem brooks_theorem (hG : G.Connected) :
    G.chromaticNumber ≤ G.maxDegree := by
  -- 对非完全图、非奇圈的连通图，证明存在 Δ(G)-着色
  sorry

end SimpleGraph
```

## 数学背景

Brooks 定理由英国数学家 R. Leonard Brooks 于1941年证明，是图着色理论中的经典结果。该定理指出：对于任何连通图，其色数不超过最大度 $\Delta(G)$，唯一的例外是完全图和奇圈。这一定理给出了色数的一个紧上界，弥补了显然上界 $\chi(G) \leq \Delta(G) + 1$ 与精确色数之间的差距。

## 直观解释

图着色问题要求为图的每个顶点分配颜色，使得相邻顶点颜色不同。一个显然的事实是：如果某个顶点有 $\Delta$ 个邻居，那么它最多需要 $\Delta + 1$ 种颜色。Brooks 定理将这个上界改进为 $\Delta$，除非图的结构"过于规则"——即完全图或奇圈。这两种例外情况确实需要 $\Delta + 1$ 种颜色，而对于其他所有图，邻接关系的某种"灵活性"使得 $\Delta$ 种颜色就足够了。

## 形式化表述

设 $G$ 是一个连通图，$\Delta(G)$ 是其最大度，则：

$$\chi(G) \leq \Delta(G)$$

等号成立当且仅当 $G$ 是完全图 $K_n$（$n \geq 3$）或奇圈 $C_{{2k+1}}$（$k \geq 1$）。

其中：

- $\chi(G)$ 表示图 $G$ 的色数
- $\Delta(G) = \max_{{v \in V}} \deg(v)$ 表示最大顶点度
- 完全图 $K_n$ 的色数为 $n = \Delta(K_n) + 1$
- 奇圈 $C_{{2k+1}}$ 的色数为 $3 = \Delta(C_{{2k+1}}) + 1$

## 证明思路

1. **排除例外**：验证完全图和奇圈确实需要 $\Delta + 1$ 种颜色\n2. **存在非最大度邻接**：对非例外图，证明存在两个不相邻的最大度顶点\n3. **顶点排序**：以这两个顶点为最后两个顶点，按度数降序排列其余顶点\n4. **贪心着色**：从前向后贪心着色，由于最后两个顶点颜色可以共享，故 $\Delta$ 种颜色足够

核心洞察在于非完全图中存在的"结构松弛"允许节省一种颜色。

## 示例

### 示例 1：完全图 $K_4$

$K_4$ 的最大度为 3，色数为 4。根据 Brooks 定理，这是等号成立的例外情况，需要 $\Delta + 1 = 4$ 种颜色。

### 示例 2：Petersen 图

Petersen 图是 3-正则图（$\Delta = 3$），且不是完全图或奇圈。Brooks 定理保证其色数 $\leq 3$。实际上 Petersen 图的色数恰好为 3。

### 示例 3：路径图 $P_n$

路径图的最大度为 2（端点度为 1，内部点度为 2），不是奇圈。Brooks 定理说明其色数 $\leq 2$。事实上所有路径图都是二部图，色数为 2。

## 应用

- **图着色算法**：为贪心着色和启发式着色算法提供理论保证
- **寄存器分配**：编译器优化中的图着色上界估计
- **频率分配**：无线电频谱分配中的干扰最小化
- **考试调度**：将冲突课程分配到最少时间段

## 相关概念

- 色数 (Chromatic Number)：正常顶点着色所需的最少颜色数
- 最大度 (Maximum Degree)：图中顶点度的最大值
- 贪心着色 (Greedy Coloring)：按顶点顺序依次分配可用最小颜色的算法
- 完全图 (Complete Graph)：每对顶点之间都有边相连的图
- 奇圈 (Odd Cycle)：长度为奇数的环

## 参考

### 教材

- [R. Diestel. Graph Theory. Springer, 5th edition, 2017. Chapter 5]
- [D. B. West. Introduction to Graph Theory. Pearson, 2nd edition, 2001. Section 5.1]

### 论文

- [R. L. Brooks. On colouring the nodes of a network. Proc. Cambridge Philos. Soc., 1941]

### 在线资源

- [Mathlib4 - Coloring](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Coloring.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*
