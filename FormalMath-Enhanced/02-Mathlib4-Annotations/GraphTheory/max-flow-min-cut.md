---
msc_primary: 00A99
processed_at: '2026-04-15'
title: 最大流最小割定理 (Max-Flow Min-Cut Theorem)
---
# 最大流最小割定理 (Max-Flow Min-Cut Theorem)

## Mathlib4 引用

```lean
import Mathlib.Combinatorics.Optimization.Flow

namespace Flow

variable {V : Type*} [Fintype V] (G : Digraph V) (c : V → V → ℝ≥0) (s t : V)

/-- 最大流最小割定理：网络中从源到汇的最大流值等于最小割的容量 -/
theorem maxFlowMinCut :
    IsMaxFlow G c s t (maxFlow G c s t) ↔
    IsMinCut G c s t (minCut G c s t) := by
  -- 证明基于增广路径和 Ford-Fulkerson 方法
  sorry

end Flow
```

## 数学背景

最大流最小割定理是网络流理论和组合优化的核心结果，由 Ford 和 Fulkerson 于1956年系统建立。该定理断言：在任何一个带容量的有向网络中，从源点到汇点所能输送的最大流量，恰好等于分离源点和汇点的所有割中容量最小的那个割的容量。这一定理是无数高效算法的理论基础。

## 直观解释

想象一个输水管道网络，每条管道有一定的流量上限。源点是水库，汇点是城市。最大流最小割定理告诉我们：能够输送到城市的最大水量，恰好等于网络中"最窄瓶颈"的容量。这个"瓶颈"就是最小割——将网络分成两部分后，从水库侧流向城市侧的所有管道的容量之和。无论网络多么复杂，最大输水量永远受限于这个最窄的通道。

## 形式化表述

设 $G = (V, E)$ 是一个带容量函数 $c: E \to \mathbb{{R}}_{{\geq 0}}$ 的有向图，$s$ 为源点，$t$ 为汇点，则：

$$\max |f| = \min_{{(S, T) \text{{ 割}}}} c(S, T)$$

其中：

- $|f|$ 表示流 $f$ 的值（从源点净流出的流量）
- $(S, T)$ 是一个 $s$-$t$ 割，满足 $s \in S$, $t \in T$, $S \cup T = V$, $S \cap T = \emptyset$
- $c(S, T) = \sum_{{u \in S, v \in T}} c(u, v)$ 表示割的容量

## 证明思路

1. **弱对偶性**：证明对任意可行流 $f$ 和任意 $s$-$t$ 割 $(S, T)$，有 $|f| \leq c(S, T)$\n2. **增广路径**：若当前流不是最大的，则存在一条从 $s$ 到 $t$ 的增广路径可以增加流量\n3. **残差网络**：构造残差网络，证明当不存在增广路径时，当前流达到最大\n4. **最小割构造**：当流最大时，在残差网络中从 $s$ 可达的顶点集构成一个容量等于流值的最小割

核心洞察在于流和割构成一对完美的对偶优化问题。

## 示例

### 示例 1：简单管道网络

设网络有源点 $s$，汇点 $t$，中间顶点 $a, b$。边及容量为：$s \to a$ (10), $s \to b$ (5), $a \to t$ (10), $b \to t$ (5), $a \to b$ (10)。最大流为 15，最小割容量也为 15。

### 示例 2：交通网络

城市道路网络中，各条道路的通行能力不同。最大流最小割定理说明高峰时段两个区域之间的最大车流量等于连接这两个区域的关键道路群的通行能力之和。这解释了为什么拓宽瓶颈道路可能显著提升整体通行能力。

### 示例 3：图像分割

在计算机视觉的图像分割中，将图像建模为图网络，源点和汇点分别代表前景和背景。最大流最小割算法可以找到最优的分割边界（即最小割），广泛应用于医学图像处理。

## 应用

- **网络路由**：互联网数据包传输和带宽分配优化
- **图像分割**：GrabCut 等基于图割的图像分割算法
- **项目调度**：关键路径法和资源约束项目调度
- **匹配问题**：二分图匹配和任务分配问题的转化与求解
- **可靠性分析**：通信网络和电力网络的容错性评估

## 相关概念

- 网络流 (Network Flow)：带容量限制的有向图上的流量分配
- 残差网络 (Residual Network)：表示还可以增加流量的网络
- 增广路径 (Augmenting Path)：可以增加流量的路径
- 割 (Cut)：将顶点集划分为两部分的划分
- Ford-Fulkerson 算法：求解最大流的经典算法

## 参考

### 教材

- [T. H. Cormen et al. Introduction to Algorithms. MIT Press, 3rd edition, 2009. Chapter 26]
- [A. Schrijver. Combinatorial Optimization. Springer, 2003. Chapters 9-10]

### 论文

- [L. R. Ford, D. R. Fulkerson. Maximal flow through a network. Canad. J. Math., 1956]

### 在线资源

- [Mathlib4 - Flow](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Optimization/Flow.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*
