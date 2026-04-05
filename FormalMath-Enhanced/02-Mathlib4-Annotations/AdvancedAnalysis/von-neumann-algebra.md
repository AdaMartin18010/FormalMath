---
msc_primary: 00A99
processed_at: '2026-04-03'
title: von Neumann代数
---
# von Neumann代数

## Mathlib4 引用

```lean
import Mathlib.Analysis.VonNeumannAlgebra.Basic

namespace Analysis

/-- von Neumann代数的定义 -/
theorem von_neumann_algebra_def
    {H : Type*} [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {M : StarSubalgebra ℂ (H →L[ℂ] H)} :
    IsVonNeumannAlgebra M ↔
      TopologicalSpace.IsClosed M.carrier := by
  -- von Neumann代数是B(H)的弱闭*-子代数
  rfl

/-- 双交换子定理 -/
theorem double_commutant
    {H : Type*} [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {S : Set (H →L[ℂ] H)} (hS : ∀ x ∈ S, star x ∈ S) :
    closure (Algebra.adjoin ℂ S) = (S.commutant).commutant := by
  -- 代数闭包等于双交换子
  sorry

end Analysis
```

## 数学背景

von Neumann代数理论由John von Neumann在1930年代创立，最初是为了给量子力学提供严格的数学基础。这是C*-代数理论的重要分支，研究Hilbert空间上弱闭的算子代数。双交换子定理（von Neumann密度定理）是该理论的基石，它表明一个*-子代数是弱闭的当且仅当它等于其双交换子。von Neumann代数在量子场论、遍历理论、子因子理论和自由概率论中有核心应用。

## 直观解释

von Neumann代数是"算子代数的完备化"。想象Hilbert空间上的算子作为"变换"，von Neumann代数包含所有可以通过"近似"（在弱算子拓扑下）得到的算子。交换子定理揭示了一个深刻对称性：一个代数完全由其交换子（与它交换的所有算子）决定。这如同一个"镜子"原则——代数A的交换子A'刻画了A的对称性，而A''（交换子的交换子）给出了A的"闭包"。

## 形式化表述

设 $H$ 是Hilbert空间，$B(H)$ 是有界算子代数。

**von Neumann代数**：$B(H)$ 的弱算子拓扑闭的*-子代数 $M \subseteq B(H)$。

**交换子**：$S' = \{T \in B(H) : TS = ST, \forall S \in S\}$

**双交换子定理**：若 $M$ 是*-子代数（含单位元），则
$$M^{''} = \overline{M}^{\text{WOT}}$$

即弱闭包等于双交换子。

**因子**：中心为复数倍的von Neumann代数，分类为 $I_n, I_\infty, II_1, II_\infty, III$ 型。

## 证明思路

1. **弱拓扑**：定义弱算子拓扑（WOT）和强算子拓扑（SOT）
2. **Kaplansky密度定理**：单位球在弱拓扑下的稠密性
3. **谱测度**：用投影值测度表示交换子代数
4. **直和分解**：中心投影分解为因子
5. **分类理论**：Murray-von Neumann因子分类

## 示例

### 示例 1：交换von Neumann代数

**问题**：描述 $L^\infty(X, \mu)$ 作为von Neumann代数。

**解答**：

$L^\infty(X, \mu)$ 通过乘法作用在 $L^2(X, \mu)$ 上：
$$M_f(g) = f \cdot g$$

这是一个交换von Neumann代数，其投影对应可测集的示性函数。

由谱定理，所有交换von Neumann代数都有这种形式。

### 示例 2：矩阵代数

**问题**：$M_n(\mathbb{C})$ 作为 $B(\mathbb{C}^n)$ 的子代数。

**解答**：

$M_n(\mathbb{C})$ 是有限维的，因此自动弱闭。

它是I$_n$型因子（有限维矩阵代数）。

其交换子是中心 $\mathbb{C} \cdot I$，双交换子是自身。

## 应用

- **量子场论**：局部可观测量的代数
- **遍历理论**：群作用的轨道等价
- **子因子理论**：Jones指标理论和结不变量
- **自由概率论**：Voiculescu的随机矩阵理论
- **非交换积分**：Segal的迹理论

## 相关概念

- [C*-代数](./c-star-algebra.md)：von Neumann代数的更广泛框架
- 双交换子定理：von Neumann代数的刻画
- 因子分类：Murray-von Neumann分类
- Tomita-Takesaki理论：模自同构群
- 循环向量：标准形式的构造

## 参考

### 教材

- Takesaki, M. Theory of Operator Algebras I, II, III. Springer, 1979-2003.
- Kadison, R.V. & Ringrose, J.R. Fundamentals of the Theory of Operator Algebras. AMS, 1997.

### 论文

- Murray, F.J. & von Neumann, J. On rings of operators. Ann. of Math., 37: 116-229, 1936.
- Jones, V.F.R. Index for subfactors. Invent. Math., 72: 1-25, 1983.

### 在线资源

- [Von Neumann Algebra Wikipedia](https://en.wikipedia.org/wiki/Von_Neumann_algebra)
- [nLab - Von Neumann Algebra](https://ncatlab.org/nlab/show/von+Neumann+algebra)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
