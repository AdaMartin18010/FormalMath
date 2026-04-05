---
msc_primary: 00A99
processed_at: '2026-04-03'
title: Lebesgue控制收敛定理 (Lebesgue Dominated Convergence Theorem)
---
# Lebesgue控制收敛定理 (Lebesgue Dominated Convergence Theorem)

## Mathlib4 引用

```lean
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

namespace DominatedConvergence

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Lebesgue控制收敛定理 -/
theorem dominated_convergence {f : ℕ → X → E} {g : X → ℝ} {F : X → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg : Integrable g μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ g x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (λ n => f n x) atTop (𝓝 (F x))) :
    Integrable F μ ∧ Tendsto (λ n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, F x ∂μ)) := by
  constructor
  · -- 证明F的可积性
    apply Integrable.of_norm_le hg
    filter_upwards [hlim] with x hx
    have : ‖F x‖ ≤ g x := by
      apply le_of_tendsto' (fun n => ?_)
      · exact hbound n
      · exact fun n => ContinuousAt.norm (ContinuousAt.tendsto hx)
    exact this
  · -- 证明积分收敛
    sorry

theorem dominated_convergence_integral {f : ℕ → X → E} {g : X → ℝ} {F : X → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg : Integrable g μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ g x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (λ n => f n x) atTop (𝓝 (F x))) :
    Tendsto (λ n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, F x ∂μ)) := by
  exact (dominated_convergence hf hg hbound hlim).2

end DominatedConvergence
```

## 数学背景

Lebesgue控制收敛定理由Henri Lebesgue在1910年左右证明，是测度论和实分析中最重要的收敛定理。它建立了函数序列点态收敛与积分收敛之间的联系，解决了Riemann积分中极限与积分交换的问题。该定理是现代积分理论的基石，使Lebesgue积分成为分析学和概率论的标准工具。

## 直观解释

控制收敛定理告诉我们：**如果一个函数序列被一个可积函数"控制"，那么极限和积分可以交换**。

想象一列函数被一个"天花板"函数压制（$|f_n| \leq g$）。定理说，只要天花板是可积的（面积有限），函数序列的积分极限等于极限函数的积分。这就像说，如果一群人都在一个有限的"盒子"里移动，他们最终位置的总"影响"等于各个人影响的极限之和。

## 形式化表述

设 $(X, \mathcal{M}, \mu)$ 是测度空间，$E$ 是Banach空间。

**控制收敛定理**：设 $\{f_n\}$ 是可测函数序列，$F$ 是极限函数，$g$ 是可积函数，满足：
1. **点态收敛**：$f_n(x) \to F(x)$ 几乎处处
2. **控制条件**：$|f_n(x)| \leq g(x)$ 几乎处处，对所有 $n$

则：
1. $F$ 可积
2. $\displaystyle \lim_{n \to \infty} \int_X f_n \, d\mu = \int_X F \, d\mu$
3. $\displaystyle \lim_{n \to \infty} \int_X |f_n - F| \, d\mu = 0$（$L^1$ 收敛）

## 证明思路

1. **可积性**：由控制条件，$|F| \leq g$ a.e.，故 $F$ 可积
2. **Fatou引理**：
   - $\int \liminf |f_n| \leq \liminf \int |f_n|$（下界）
   - 对 $2g - |f_n - F|$ 应用Fatou引理得反向不等式
3. **控制收敛**：
   - $|f_n - F| \to 0$ a.e.
   - $|f_n - F| \leq 2g$ 可积
   - 由控制收敛（对有界收敛的简化）得结论

核心洞察是可积控制函数提供了"一致可积性"。

## 示例

### 示例 1：简单应用

设 $f_n(x) = \frac{n}{n+x^2}$ 在 $[0,1]$ 上。

逐点极限：$F(x) = 1$

控制函数：$g(x) = 1$（可积）

结果：$\lim_{n \to \infty} \int_0^1 \frac{n}{n+x^2} dx = \int_0^1 1 \, dx = 1$

### 示例 2：需要控制的例子

设 $f_n(x) = n \chi_{[0, 1/n]}(x)$ 在 $[0,1]$ 上。

逐点极限：$F(x) = 0$（$x > 0$）

无控制函数：$\int_0^1 f_n = 1$ 但 $\int_0^1 F = 0$

控制条件不满足，定理不适用。

### 示例 3：复值函数

设 $f_n(x) = e^{inx}/(1+x^2)$ 在 $\mathbb{R}$ 上。

逐点不收敛，但考虑 Cesàro 平均或在分布意义下。

控制函数：$g(x) = 1/(1+x^2)$（可积）

## 应用

- **测度论**：积分与极限的交换
- **概率论**：期望的连续性
- **泛函分析**：算子半群的生成元
- **偏微分方程**：弱解的构造
- **傅里叶分析**：Fourier变换的连续性

## 相关概念

- [Fatou引理 (Fatou's Lemma)](./fatou-lemma.md)：积分的下半连续性
- 单调收敛定理 (Monotone Convergence Theorem)：单调序列的收敛
- 一致可积性 (Uniform Integrability)：积分的紧性条件
- Vitali收敛定理 (Vitali Convergence Theorem)：控制定理的推广
- Bochner积分 (Bochner Integral)：向量值函数的积分

## 参考

### 教材

- [Folland. Real Analysis. Wiley, 2nd edition, 1999. Chapter 2]
- [Rudin. Real and Complex Analysis. McGraw-Hill, 3rd edition, 1987. Chapter 1]

### 历史文献

- [Lebesgue. Sur les intégrales singulières. Ann. Fac. Sci. Toulouse, 1910]

### 在线资源

- [Mathlib4 文档 - Bochner Integral](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Bochner.html)[需更新]
- [Terry Tao - Dominated Convergence](https://terrytao.wordpress.com/2009/01/11/the-dominated-convergence-theorem/)[需更新]

---

*最后更新：2026-04-03 | 版本：v1.0.0*
