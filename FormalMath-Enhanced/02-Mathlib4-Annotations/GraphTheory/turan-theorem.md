---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: Turán 定理 (Turán's Theorem)
---
# Turán 定理 (Turán's Theorem)

## Mathlib4 引用

```lean
import Mathlib.Combinatorics.SimpleGraph.Turan

namespace SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Turán 定理：不含 (r+1)-团的 n 顶点图的最大边数由 Turán 图达到 -/
theorem turanDensity (hr : 0 < r) (h : CliqueFree G (r + 1)) :
    G.edgeFinset.card ≤ turanGraph (Fintype.card V) r edgeFinset.card := by
  -- 证明使用归纳法和双计数技术
  sorry

end SimpleGraph
```

## 数学背景

Turán 定理由匈牙利数学家保罗·图兰（Pál Turán）于1941年证明，是极值图论的奠基性结果。该定理精确刻画了在不包含完全子图 K_{r+1} 的条件下，一个图最多可以有多少条边。Turán 图是达到这个上界的唯一极值图，开启了极值图论这一蓬勃发展的研究领域。

## 直观解释

Turán 定理回答了一个简单的极值问题：如果一个聚会中有 n 个人，要求其中任意 r+1 个人不全是两两认识的，那么最多可能有多少对互相认识的人？答案是：将所有人尽量均匀地分成 r 个小组，不同小组之间的人都互相认识，而同一小组内的人互不认识。这种完全多部图的结构给出了最大边数。

## 形式化表述

设 $G$ 是一个具有 $n$ 个顶点且不含 $K_{{r+1}}$ 的图，则：

$$|E(G)| \leq \left(1 - \frac{{1}}{{r}}\right) \frac{{n^2}}{{2}}$$

等号成立当且仅当 $G$ 是 Turán 图 $T(n, r)$，即 $r$ 部完全多部图，各部大小之差不超过 1。

其中：

- $|E(G)|$ 表示图 $G$ 的边数
- $K_{{r+1}}$ 表示 $r+1$ 个顶点的完全图
- $T(n, r)$ 表示 $n$ 个顶点的 Turán 图

## 证明思路

1. **归纳基础**：对小规模图验证定理成立\n2. **极值图分析**：证明极值图必须不含 $(r+1)$-团且边数最大\n3. **度序列论证**：利用 Zykov 对称化或权重转移方法证明 Turán 图是唯一极值图\n4. **不等式推导**：通过完全多部图的结构计算精确边数上界

核心洞察在于完全多部图是避免大团的"最优"结构。

## 示例

### 示例 1：不含三角形的图

当 $r = 2$ 时，Turán 定理说明不含三角形 $K_3$ 的 $n$ 顶点图最多有 $\lfloor n^2/4 \rfloor$ 条边。这等价于 Mantel 定理。极值图是完全二部图 $K_{\lfloor n/2 \rfloor, \lceil n/2 \rceil}$。

### 示例 2：7 个顶点不含 $K_4$

设 $n = 7$, $r = 3$。Turán 图 $T(7, 3)$ 将 7 个顶点分为三部，大小为 3, 2, 2。边数为 $3 \cdot 2 + 3 \cdot 2 + 2 \cdot 2 = 16$。任何不含 $K_4$ 的 7 顶点图至多有 16 条边。

### 示例 3：5 个顶点的极值图

对于 $n = 5$, $r = 2$，Turán 图是 $K_{{2,3}}$，有 6 条边。如果添加任何一条同部边就会形成三角形，从而违反极值条件。

## 应用

- **极值图论**：作为研究图禁止子图问题的基本工具
- **拉姆齐理论**：与 Ramsey 数的研究密切相关
- **网络设计**：设计无大团的高效通信网络
- **社会网络分析**：理解社交圈中的关系密度限制

## 相关概念

- 极值图论 (Extremal Graph Theory)：研究满足某种性质时图的最大/最小参数
- 团 (Clique)：图中两两相邻的顶点集合
- 完全多部图 (Complete Multipartite Graph)：多部之间全连接的图
- Mantel 定理 (Mantel's Theorem)：Turán 定理 $r=2$ 的特例
- Erdős–Stone 定理：Turán 定理的渐近推广

## 参考

### 教材

- [B. Bollobás. Modern Graph Theory. Springer, 1998. Chapter 4]
- [R. Diestel. Graph Theory. Springer, 5th edition, 2017. Chapter 7]

### 论文

- [P. Turán. On an extremal problem in graph theory. Mat. Fiz. Lapok, 1941]

### 在线资源

- [Mathlib4 - Turán](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Turan.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*
