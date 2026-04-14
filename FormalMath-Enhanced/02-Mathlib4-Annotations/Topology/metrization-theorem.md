---
msc_primary: 00A99
processed_at: '2026-04-15'
title: 度量化定理 (Metrization Theorem)
---
# 度量化定理 (Metrization Theorem)

## Mathlib4 引用

```lean
import Mathlib.Topology.MetricSpace.Metrizable

namespace Topology

variable {X : Type*} [TopologicalSpace X]

/-- Nagata-Smirnov 度量化定理：拓扑空间可度量化当且仅当它是正则的且
    具有 σ-局部有限基 -/
theorem nagata_smirnov_metrization :
    (∃ d : X → X → ℝ, IsMetric d ∧ Topology.induced (UniformSpace.toTopologicalSpace (UniformSpace.ofMetric d)) = ‹TopologicalSpace X›)
    ↔ RegularSpace X ∧ ∃ β : Set (Set X), IsTopologicalBasis β ∧ σLocallyFinite β := by
  -- 构造性证明，利用 σ-局部有限基显式定义度量
  sorry

end Topology
```

## 数学背景

度量化定理是点集拓扑学中的核心结果，它精确刻画了哪些拓扑空间可以被赋予度量（距离函数），使其拓扑由开球生成。最重要的度量化定理包括 Urysohn 度量化定理（1919-1925）和 Nagata-Smirnov 度量化定理（1950-1951）。Urysohn 定理断言：第二可数的正则空间是可度量化的。Nagata-Smirnov 定理则给出了更一般的充要条件：一个拓扑空间可度量化当且仅当它是正则的且具有 σ-局部有限基。

## 直观解释

度量化定理回答了一个基本问题：什么样的拓扑空间足够好，可以在其中定义两点之间的距离？在日常生活中，我们对距离有直观的理解——三维空间中的欧几里得距离。但在抽象的拓扑空间中，开集的定义可能非常奇特，不一定来自任何距离函数。度量化定理告诉我们：如果一个拓扑空间满足某些分离性和可数性条件（如正则性和第二可数性），那么就一定可以在其中引入一个度量，使得所有的拓扑性质都可以用距离来描述。

## 形式化表述

**Urysohn 度量化定理**：
一个拓扑空间 X 可度量化，如果 X 是正则的且第二可数的。

**Nagata-Smirnov 度量化定理**（更一般的充要条件）：
一个拓扑空间 X 可度量化当且仅当 X 是正则的且具有 σ-局部有限基。

其中：

- 可度量化（Metrizable）：存在度量 d: X × X → [0, +∞)，使得 X 的拓扑由开球 B(x, ε) 生成
- 正则空间（Regular Space）：T_1 且任意点和闭集可用不相交开集分离
- 第二可数（Second Countable）：拓扑有可数的基
- σ-局部有限基：基可以表示为可数个局部有限子族的并

一个集族 B 是局部有限的，如果每一点都有一个邻域只与 B 中有限多个集合相交。

## 证明思路

1. **必要性**：若 X 可度量化，则度量拓扑天然是正则的，且度量开球族可以构造出 σ-局部有限基
2. **Urysohn 方向**：利用 Urysohn 引理构造从 X 到 Hilbert 方体 [0, 1]^N 的嵌入，证明第二可数正则空间可嵌入度量空间，从而可度量化
3. **Nagata-Smirnov 充分性**：给定 σ-局部有限基，构造一族 Urysohn 型连续函数，然后利用这些函数将 X 嵌入到某个度量空间中
4. **度量显式构造**：定义 d(x, y) = \sup_i |f_i(x) - f_i(y)| 或类似的形式，验证其诱导的拓扑与原拓扑一致

核心洞察在于局部有限基允许用可数个分离函数来编码拓扑结构。

## 示例

### 示例 1：欧氏空间

R^n 配备标准拓扑是第二可数的（以有理中心、有理半径的开球为可数基），且是正则的。由 Urysohn 度量化定理，R^n 可度量化——其标准度量就是欧几里得距离。

### 示例 2：流形

任何第二可数的拓扑流形都是局部欧氏的、Hausdorff 的，从而也是正则和第二可数的。因此拓扑流形总是可度量化的。

### 示例 3：长直线不可度量化

长直线（long line）是局部类似于 R 的序拓扑空间，但不是第二可数的。因此它不可度量化，这说明第二可数性条件在度量化定理中是不可或缺的。

## 应用

- **微分几何**：流形的可度量化保证了黎曼度量的存在
- **泛函分析**：Banach 空间和 Hilbert 空间的拓扑结构研究
- **拓扑动力系统**：度量空间中的遍历理论和熵理论
- **概率论**：Polish 空间（可度量化可分完备空间）上的测度论
- **计算拓扑**：持久同调等算法拓扑学方法的基础

## 相关概念

- 度量空间 (Metric Space)：配备距离函数的拓扑空间
- 正则空间 (Regular Space)：点和闭集可分离的拓扑空间
- 第二可数 (Second Countable)：具有可数拓扑基的空间
- 局部有限 (Locally Finite)：每点邻域只与有限多个集合相交
- Urysohn 引理 (Urysohn's Lemma)：构造分离连续函数的关键工具

## 参考

### 教材

- [J. R. Munkres. Topology. Pearson, 2nd edition, 2000. Sections 34, 40]
- [S. Willard. General Topology. Addison-Wesley, 1970. Sections 22-23]

### 在线资源

- [Mathlib4 - Metrizable](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/MetricSpace/Metrizable.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*