---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: Dirac 定理 (Dirac's Theorem)
---
# Dirac 定理 (Dirac's Theorem)

## Mathlib4 引用

```lean
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

namespace SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Dirac 定理：若 n ≥ 3 且每个顶点的度至少为 n/2，则 G 是哈密顿图 -/
theorem dirac_theorem (hn : 3 ≤ Fintype.card V)
    (h : ∀ v : V, G.degree v ≥ Fintype.card V / 2) :
    G.IsHamiltonian := by
  -- 证明基于最长路径的扩展论证
  sorry

end SimpleGraph
```

## 数学背景

Dirac 定理由丹麦-英国数学家 Gabriel Andrew Dirac 于1952年证明，是哈密顿图理论中的里程碑结果。该定理给出了判断一个图是否包含哈密顿圈的一个简单但强有力的充分条件：如果 $n \geq 3$ 个顶点的图中每个顶点的度至少为 $n/2$，则该图必为哈密顿图。这一定理开创了图论中度条件与哈密顿性研究的新方向。

## 直观解释

Dirac 定理可以通俗地理解为：在一个聚会中，如果每个人都至少认识一半以上的参加者，那么就一定存在一种方式让所有参加者手拉手围成一个圈，每个人恰好与两个人相邻。这个条件相当惊人——只需要"每个人都比较受欢迎"（认识至少一半人），就能保证存在一个包含所有人的完美环形排列。这揭示了高度连通性与遍历性之间的深刻联系。

## 形式化表述

设 $G$ 是一个具有 $n \geq 3$ 个顶点的简单图，若对任意顶点 $v \in V(G)$ 都有：

$$\deg(v) \geq \frac{n}{2}$$

则 $G$ 包含一个哈密顿圈，即 $G$ 是哈密顿图。

其中：

- $\deg(v)$ 表示顶点 $v$ 的度（邻居个数）
- $n = |V(G)|$ 表示图的顶点数
- 哈密顿圈是指经过图中每个顶点恰好一次的圈

## 证明思路

1. **连通性**：证明满足条件的图必然是连通的\n2. **最长路径**：取图中的一条最长路径 $P = v_1 v_2 \dots v_k$\n3. **圈构造**：证明存在连接 $v_1$ 和 $v_k$ 的边，从而将最长路径扩展为圈\n4. **哈密顿性**：若该圈不是哈密顿圈，则可利用连通性将其扩展为更长的路径，与最大性矛盾

核心洞察在于高度条件保证了路径端点之间存在足够多的"交叉连接"，从而可以闭合为圈。

## 示例

### 示例 1：完全图 $K_n$

在完全图 $K_n$（$n \geq 3$）中，每个顶点的度为 $n - 1 \geq n/2$。Dirac 定理保证 $K_n$ 是哈密顿图，这与直观完全一致——任何排列都能形成哈密顿圈。

### 示例 2：5 个顶点的图

考虑一个 5 顶点图，若每个顶点的度至少为 3（因为 $\lceil 5/2 \rceil = 3$），则 Dirac 定理保证该图是哈密顿图。即使图不是完全图，只要满足这个度条件，就必然存在哈密顿圈。

### 示例 3：条件不最优的例子

Petersen 图有 10 个顶点，是 3-正则图。每个顶点的度为 3，而 $10/2 = 5$，因此 Petersen 图不满足 Dirac 条件。事实上 Petersen 图不是哈密顿图，这说明 Dirac 条件的紧性在一定程度上是合理的。

## 应用

- **旅行商问题 (TSP)**：判断问题实例是否容易求解的充分条件
- **电路设计**：电子电路板布线和芯片设计中的遍历优化
- **基因组学**：DNA 序列组装中的哈密顿路径问题
- **社交网络分析**：发现包含所有成员的社交环或传播路径

## 相关概念

- 哈密顿圈 (Hamiltonian Cycle)：经过每个顶点恰好一次的圈
- 哈密顿图 (Hamiltonian Graph)：包含哈密顿圈的图
- 度条件 (Degree Condition)：基于顶点度判断图性质的准则
- Ore 定理 (Ore's Theorem)：Dirac 定理的推广，要求 $\deg(u) + \deg(v) \geq n$ 对任意非邻接顶点对成立
- 旅行商问题 (TSP)：寻找最短哈密顿圈的著名 NP-难问题

## 参考

### 教材

- [R. Diestel. Graph Theory. Springer, 5th edition, 2017. Chapter 10]
- [J. A. Bondy & U. S. R. Murty. Graph Theory. Springer, 2008. Chapter 18]

### 论文

- [G. A. Dirac. Some theorems on abstract graphs. Proc. London Math. Soc., 1952]

### 在线资源

- [Mathlib4 - Hamiltonian](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Hamiltonian.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*
