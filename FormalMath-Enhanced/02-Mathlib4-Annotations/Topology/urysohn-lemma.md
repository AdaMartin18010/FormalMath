---
msc_primary: 00A99
processed_at: '2026-04-15'
title: Urysohn 引理 (Urysohn's Lemma)
---
# Urysohn 引理 (Urysohn's Lemma)

## Mathlib4 引用

```lean
import Mathlib.Topology.UrysohnsLemma

namespace Topology

variable {X : Type*} [TopologicalSpace X] [NormalSpace X]

/-- Urysohn 引理：正规空间中不相交的闭集可用连续函数分离 -/
theorem urysohn_lemma {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hAB : Disjoint A B) :
    ∃ f : X → ℝ, Continuous f ∧ (∀ x ∈ A, f x = 0) ∧ (∀ x ∈ B, f x = 1) ∧
      ∀ x, f x ∈ Set.Icc 0 1 := by
  -- 利用正规性逐次构造开集，然后通过一致收敛定义连续函数
  sorry

end Topology
```

## 数学背景

Urysohn 引理由苏联数学家帕维尔·乌雷松（Pavel Urysohn）于1925年证明，是点集拓扑学中最重要的结果之一。该引理断言：在正规拓扑空间中，任意两个不相交的闭集都可以被一个连续函数完全分离——即存在一个从空间到 [0, 1] 的连续函数，在一个闭集上取值为 0，在另一个闭集上取值为 1。Urysohn 引理是理解正规空间结构的关键工具，也是 Tietze 扩张定理、度量化定理和大量泛函分析结果的基石。

## 直观解释

Urysohn 引理提供了一个从拓扑性质构造连续函数的桥梁。想象一个正规空间中的两个不相交的闭集 A 和 B，就像两块互不接触的领地。引理告诉我们：可以在这个空间中建造一个地形（连续函数），使得 A 领地的海拔为 0，B 领地的海拔为 1，而中间过渡区域的海拔平滑地从 0 渐变到 1。这看似直观的构造在一般的拓扑空间中却极其深刻——它要求空间具有足够的开集来缓冲闭集之间的冲突。

## 形式化表述

设 X 是一个正规拓扑空间，A 和 B 是 X 中两个不相交的闭子集，则存在连续函数 f: X → [0, 1] 使得：

$$f(x) = \begin{cases} 0 & x \in A \\ 1 & x \in B \end{cases}$$

更一般地，对任意闭集 A、开集 U ⊇ A，存在连续函数 f: X → [0, 1] 使得 f|_A = 0 且 f|_{X \setminus U} = 1。

其中：

- 正规空间（Normal Space）满足：任意两个不相交的闭集都有不相交的开邻域
- [0, 1] 是实数轴上的闭单位区间
- 连续函数是指在 X 的拓扑和 [0, 1] 的标准拓扑下连续的映射

## 证明思路

1. **二分法构造**：首先在 A 和 B 之间插入一个缓冲开集 U_{1/2}，使得 A ⊆ U_{1/2} ⊆ \overline{U}_{1/2} ⊆ X \setminus B
2. **递归加密**：对已有开集之间的空隙继续插入新的缓冲开集 U_q（q 为二进有理数）
3. **正规性利用**：每一步都利用正规空间的存在性保证可以找到合适的开集
4. **定义函数**：令 f(x) = \inf\{q : x \in U_q\}，证明这样定义的函数连续且满足边界条件

核心洞察在于二进有理数的稠密性使得可以通过可数多层缓冲来构造连续过渡。

## 示例

### 示例 1：度量空间

任何度量空间都是正规空间。设 A, B 是不相交闭集，可显式构造 f(x) = \frac{d(x, A)}{d(x, A) + d(x, B)}。这是 Urysohn 引理在度量空间中的具体实现。

### 示例 2：Tietze 扩张定理

Urysohn 引理是证明 Tietze 扩张定理的关键步骤：正规空间中闭子集上的任意有界连续函数都可以扩张到整个空间上。

### 示例 3：局部紧 Hausdorff 空间

局部紧 Hausdorff 空间上的 Urysohn 型引理允许构造具有紧支集的连续函数，这是调和分析和分布理论的基础。

## 应用

- **泛函分析**：C(X) 代数的研究和 Riesz 表示定理
- **度量化定理**：Nagata-Smirnov 和 Urysohn 度量化准则
- **代数拓扑**：连续映射的构造和同伦论
- **测度论**：正则有界测度的存在性和逼近性质
- **偏微分方程**：Sobolev 空间中截断函数（cutoff functions）的存在性

## 相关概念

- 正规空间 (Normal Space)：T_1 且任意不相交闭集有不相交开邻域
- 连续函数 (Continuous Function)：拓扑结构保持的映射
- Tietze 扩张定理 (Tietze Extension Theorem)：闭子集上连续函数的扩张
- 二进有理数 (Dyadic Rational)：形如 k/2^n 的有理数
- 度量空间 (Metric Space)：配备距离函数的拓扑空间

## 参考

### 教材

- [J. R. Munkres. Topology. Pearson, 2nd edition, 2000. Section 33]
- [S. Willard. General Topology. Addison-Wesley, 1970. Section 15]

### 在线资源

- [Mathlib4 - UrysohnsLemma](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/UrysohnsLemma.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*