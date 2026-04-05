---
msc_primary: 00A99
processed_at: '2026-04-03'
title: Weierstrass逼近定理 (Weierstrass Approximation Theorem)
---
# Weierstrass逼近定理 (Weierstrass Approximation Theorem)

## Mathlib4 引用

```lean
import Mathlib.Analysis.SpecialFunctions.Polynomials
import Mathlib.Topology.ContinuousFunction.Polynomial

namespace WeierstrassApproximation

variable {a b : ℝ} (f : C([a, b], ℝ))

/-- Weierstrass逼近定理 -/
theorem weierstrass_approximation (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Polynomial ℝ, ∀ x ∈ Set.Icc a b, |f x - p.eval x| < ε := by
  -- 构造Bernstein多项式并证明一致收敛
  sorry

/-- Bernstein多项式逼近 -/
def bernstein_polynomial (n : ℕ) (f : C([0, 1], ℝ)) (x : ℝ) : ℝ :=
  ∑ k in range (n + 1), Nat.choose n k * x^k * (1 - x)^(n - k) * f (k / n)

/-- Bernstein多项式一致收敛 -/
theorem bernstein_convergence (f : C([0, 1], ℝ)) :
    Tendsto (fun n => bernstein_polynomial n f) atTop (𝓝 f) := by
  -- 利用大数定律证明收敛
  sorry

end WeierstrassApproximation
```

## 数学背景

Weierstrass逼近定理由卡尔·维尔斯特拉斯（Karl Weierstrass）于1885年证明，是数学分析中最重要的结果之一。该定理表明多项式在连续函数空间中是稠密的，为函数逼近理论奠定了基础。Sergei Bernstein于1912年给出了构造性证明，引入了著名的Bernstein多项式。

## 直观解释

Weierstrass定理告诉我们：**任何连续函数都可以用多项式任意精确地逼近**。就像用越来越精细的"折线"逼近曲线，多项式提供了一种通用的"语言"来描述连续函数。这在计算上非常重要，因为多项式易于计算和分析。

## 形式化表述

设 $f: [a, b] \to \mathbb{R}$ 是连续函数，则对任意 $\varepsilon > 0$，存在多项式 $P$ 使得：

$$|f(x) - P(x)| < \varepsilon, \quad \forall x \in [a, b]$$

即多项式在连续函数空间 $C[a, b]$（配备上确界范数）中稠密。

**Bernstein多项式**（构造性证明）：
$$B_n(f)(x) = \sum_{k=0}^n \binom{n}{k} x^k (1-x)^{n-k} f\left(\frac{k}{n}\right)$$

当 $n \to \infty$ 时，$B_n(f) \to f$ 一致收敛。

## 证明思路

### Bernstein构造性证明：

1. **概率解释**：Bernstein多项式可解释为期望
2. **大数定律**：$k/n \to x$ 依概率收敛
3. **一致连续性**：控制 $f(k/n) - f(x)$ 的大小
4. **Chebyshev不等式**：估计偏差概率

### Weierstrass原始证明：

利用热核（heat kernel）或Landau核磨光函数。

## 示例

### 示例 1：绝对值函数

$f(x) = |x|$ 在 $[-1, 1]$ 上，可用多项式逼近。

构造：$|x| \approx \sqrt{x^2 + \varepsilon^2}$，再Taylor展开。

### 示例 2：Runge现象

注意：插值多项式可能不一致收敛。Weierstrass定理说的是存在某个多项式，不一定是插值多项式。

## 应用

- **数值分析**：函数逼近、数值积分
- **计算机图形学**：Bézier曲线（Bernstein多项式的变形）
- **概率论**：Bernstein多项式与二项分布的联系
- **逼近理论**：正交多项式、样条函数
- **复分析**：Mergelyan定理（复变推广）

## 相关概念

- Bernstein多项式：构造性逼近工具
- [Stone-Weierstrass定理](./stone-weierstrass-theorem.md)：拓扑推广
- Chebyshev多项式：最优一致逼近
- Fourier级数：三角多项式逼近

## 参考

### 教材

- [Cheney. Introduction to Approximation Theory. AMS Chelsea, 2nd edition, 1998. Chapter 2]
- [Rudin. Principles of Mathematical Analysis. McGraw-Hill, 3rd edition, 1976. Chapter 7]

### 历史文献

- [Weierstrass. Über die analytische Darstellbarkeit sogenannter willkürlicher Functionen. 1885]
- [Bernstein. Démonstration du théorème de Weierstrass fondée sur le calcul des probabilités. 1912]

### 在线资源

- [Mathlib4 文档 - Polynomial](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/ContinuousFunction/Polynomial.html)[需更新]

---

*最后更新：2026-04-03 | 版本：v1.0.0*
