---
msc_primary: 00A99
processed_at: '2026-04-03'
title: Arzelà-Ascoli定理 (Arzelà-Ascoli Theorem)
---
# Arzelà-Ascoli定理 (Arzelà-Ascoli Theorem)

## Mathlib4 引用

```lean
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.UniformSpace.Equicontinuity

namespace ArzelaAscoli

variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
  [MetricSpace Y] [CompleteSpace Y]

/-- Arzelà-Ascoli定理（与Ascoli-Arzelà等价表述） -/
theorem arzela_ascoli (F : Set (X → Y)) (hF₁ : ∀ x, IsCompact (closure {f x | f ∈ F}))
    (hF₂ : UniformEquicontinuous F) :
    IsCompact (closure F) := by
  -- 利用等度连续性和逐点紧致性证明函数族紧致
  sorry

/-- 序列紧性形式 -/
theorem arzela_ascoli_sequential (F : Set (X → Y)) (hF₁ : ∀ x, IsCompact (closure {f x | f ∈ F}))
    (hF₂ : UniformEquicontinuous F) (fn : ℕ → X → Y) (hfn : ∀ n, fn n ∈ F) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f, Tendsto (fn ∘ φ) atTop (𝓝 f) := by
  -- 提取一致收敛子列
  sorry

end ArzelaAscoli
```

## 数学背景

Arzelà-Ascoli定理（与Ascoli-Arzelà定理为同一结果的不同命名）是数学分析中关于函数族紧性的核心定理。该定理由意大利数学家Cesare Arzelà（1889年）和Giulio Ascoli（1883-1884年）共同建立，为证明函数序列的一致收敛性提供了强有力的工具，在微分方程、变分法和泛函分析中具有基础性地位。

## 直观解释

Arzelà-Ascoli定理告诉我们：**在紧致空间上，一致有界且"同步连续"的函数族必存在一致收敛的子序列**。想象一组运动员在跑道上跑步：如果他们保持相似的速度（等度连续）且不跑出特定范围（一致有界），那么总能找到一个子序列以相似的方式"同步"接近某个极限状态。

## 形式化表述

设 $X$ 是紧致度量空间，$Y$ 是完备度量空间，$\mathcal{F} \subset C(X, Y)$ 是连续函数族。

**Arzelà-Ascoli定理**：$\mathcal{F}$ 在一致拓扑下相对紧致当且仅当满足：
1. **逐点紧致性**：对每个 $x \in X$，集合 $\{f(x) : f \in \mathcal{F}\}$ 在 $Y$ 中相对紧致
2. **等度连续性**：$\mathcal{F}$ 在 $X$ 上等度连续

当 $Y = \mathbb{R}^n$ 时，条件1等价于一致有界性。

## 证明思路

1. **必要性证明**：
   - 紧致集的闭子集紧致
   - 一致收敛保持等度连续性

2. **充分性证明**：
   - 取 $X$ 的可数稠密子集 $\{x_n\}$
   - 对角线法提取逐点收敛子列
   - 利用等度连续性证明一致收敛
   - 完备性保证极限函数的连续性

## 示例

### 示例 1：Lipschitz函数族

设 $\mathcal{F} = \{f \in C[0,1] : |f(x)-f(y)| \leq L|x-y|, \|f\|_\infty \leq M\}$

满足等度连续（Lipschitz常数一致）和一致有界，故相对紧致。

### 示例 2：积分算子

定义 $(Tf)(x) = \int_a^b K(x,y)f(y)dy$，其中 $K$ 连续。

在适当条件下，$T$ 将有界集映射为等度连续集，故是紧算子。

## 应用

- **常微分方程**：Picard-Lindelöf存在性定理
- **偏微分方程**：Sobolev紧嵌入、紧性方法
- **变分法**：极小化序列的强收敛
- **复分析**：Montel定理（全纯函数族的正规族理论）
- **概率论**：Prohorov定理（测度族的紧性）

## 相关概念

- [Ascoli-Arzelà定理](./ascoli-arzela-theorem.md)：同一定理的等价表述
- 等度连续性：函数族同步变化的条件
- 紧性 (Compactness)：拓扑空间的基本性质
- 相对紧致：闭包紧致的概念

## 参考

### 教材

- [Royden & Fitzpatrick. Real Analysis. Pearson, 4th edition, 2010. Chapter 10]
- [Rudin. Principles of Mathematical Analysis. McGraw-Hill, 3rd edition, 1976. Chapter 7]

### 历史文献

- [Arzelà. Sulle serie di funzioni. 1889]

### 在线资源

- [Mathlib4 文档 - Compactness](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Compactness/Compact.html)[需更新]

---

*最后更新：2026-04-03 | 版本：v1.0.0*
