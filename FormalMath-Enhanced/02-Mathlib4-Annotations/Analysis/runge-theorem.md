---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: Runge 定理 (Runge's Theorem)
---
# Runge 定理 (Runge's Theorem)

## Mathlib4 引用

```lean
import Mathlib.Analysis.Complex.Runge

namespace ComplexAnalysis

variable {K : Set ℂ} (hK : IsCompact K)

/-- Runge 定理：全纯函数在紧集上可用有理函数一致逼近，
    极点位于补集的连通分支中 -/
theorem runge_approximation {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (interior K)) :
    ∀ ε > 0, ∃ g : ℂ → ℂ, (∀ z ∈ K, ‖f z - g z‖ < ε) ∧
      (∀ z, g.DifferentiableAt z → z ∈ interior K ∨ z ∉ K) := by
  -- 利用 Cauchy 积分公式和 Riemann 和逼近证明
  sorry

end ComplexAnalysis
```

## 数学背景

Runge 定理是复分析中关于全纯函数逼近的经典结果，由德国数学家卡尔·龙格（Carl Runge）于1885年证明。该定理断言：若 $K$ 是复平面上的紧集，$f$ 在 $K$ 的某个邻域内全纯，则 $f$ 可以在 $K$ 上一致逼近为有理函数，且这些有理函数的极点可以预先指定在 $K$ 的补集的每个无界连通分支中。

## 直观解释

Runge 定理提供了一个强大的全纯函数逼近工具。想象你在一个紧集 $K$ 上有一个光滑的复函数，你希望用一个更简单的函数（有理函数或多项式）来近似它。Runge 定理告诉我们：只要这个函数在 $K$ 的某个小邻域内是全纯的，那么你就可以找到一列有理函数（如果 $K$ 的补集连通，则是多项式），它们在 $K$ 上一致收敛到这个函数。

## 形式化表述

设 $K \subseteq \mathbb{C}$ 是紧集，$f$ 在 $K$ 的某个开邻域内全纯。则对任意 $\varepsilon > 0$，存在有理函数 $R(z)$ 使得：

$$\sup_{{z \in K}} |f(z) - R(z)| < \varepsilon$$

且 $R$ 的极点可以预先指定在 $K$ 的补集 $\mathbb{C} \setminus K$ 的每个连通分支中。

特别地，若 $\mathbb{C} \setminus K$ 是连通的（即 $K$ 没有洞），则 $f$ 可以用多项式一致逼近。

其中：

- 有理函数是指两个多项式的商
- 一致逼近意味着在整个 $K$ 上误差同时小于 $\varepsilon$
- 极点位置的选择取决于 $K$ 的拓扑结构

## 证明思路

1. **Cauchy 积分表示**：在 $K$ 的边界附近，$f(z) = \frac{1}{2\pi i} \oint_\gamma \frac{f(\zeta)}{\zeta - z} d\zeta$
2. **Riemann 和逼近**：将积分路径离散化，$f(z)$ 被表示为简单分式的极限
3. **极点移动**：利用 $K$ 的补集的连通性，将每个极点沿连续路径移动到预先指定的位置
4. **多项式情形**：若 $\mathbb{C} \setminus K$ 连通，则所有极点可以移动到无穷远，从而得到多项式逼近

核心洞察在于 Cauchy 核提供了全纯函数的局部积木。

## 示例

### 示例 1：单位圆盘上的多项式逼近

设 $K = \overline{D}(0, 1)$ 是闭单位圆盘，$f(z) = e^z$。因 $K$ 的补集连通，Runge 定理保证 $e^z$ 可以在 $K$ 上用多项式一致逼近。Taylor 多项式就是这样的逼近序列。

### 示例 2：环形区域上的有理逼近

设 $K = \{z : 1 \leq |z| \leq 2\}$ 是闭圆环。$K$ 的补集有两个连通分支，因此一般函数在 $K$ 上不能用多项式一致逼近，但可以用极点分别位于 0 和 $\infty$ 的有理函数逼近。

### 示例 3：Mergelyan 定理的前奏

Runge 定理要求 $f$ 在 $K$ 的邻域内全纯。Mergelyan 定理进一步证明：若 $K$ 的补集连通且 $f$ 在 $K$ 上连续、在 $K$ 的内部全纯，则 $f$ 仍可用多项式一致逼近。

## 应用

- **复逼近理论**：有理函数和多项式逼近的系统研究
- **数值分析**：复平面上的插值和逼近算法
- **控制理论**：传递函数的模型降阶和逼近
- **算子理论**：全纯泛函演算和谱逼近
- **数学物理**：散射振幅的极点展开和 Padé 逼近

## 相关概念

- Cauchy 积分公式 (Cauchy Integral Formula)：Runge 定理证明的核心工具
- 有理函数 (Rational Function)：两个多项式的商
- 一致收敛 (Uniform Convergence)：紧集上同时收敛
- Mergelyan 定理 (Mergelyan's Theorem)：Runge 定理的重要推广
- 连通分支 (Connected Component)：补集中极点的允许位置

## 参考

### 教材

- [L. Ahlfors. Complex Analysis. McGraw-Hill, 3rd edition, 1979. Chapter 4]
- [J. B. Conway. Functions of One Complex Variable I. Springer, 2nd edition, 1978. Chapter 8]

### 在线资源

- [Mathlib4 - Runge](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Runge.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*