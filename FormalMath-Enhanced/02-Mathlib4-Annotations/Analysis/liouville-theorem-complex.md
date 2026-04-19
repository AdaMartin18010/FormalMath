---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: Liouville 定理（复分析）(Liouville's Theorem in Complex Analysis)
---
# Liouville 定理（复分析）(Liouville's Theorem in Complex Analysis)

## Mathlib4 引用

```lean
import Mathlib.Analysis.Complex.Liouville

namespace ComplexAnalysis

/-- Liouville 定理：全纯有界函数必为常数 -/
theorem differentiable_bounded_imp_constant {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hB : ∃ M, ∀ z, ‖f z‖ ≤ M) :
    ∃ c, ∀ z, f z = c := by
  -- 参见 Mathlib4 Analysis.Complex.Liouville
  sorry

end ComplexAnalysis
```

## 数学背景

Liouville 定理是复分析中最优美且影响深远的结果之一，由法国数学家 Joseph Liouville 于19世纪中叶证明。该定理表明：在整个复平面上有界的全纯函数只能是常数。这一惊人结果将全纯函数（复可微函数）的刚性表现得淋漓尽致——与实分析中光滑有界函数种类繁多形成鲜明对比。该定理也是证明代数基本定理（任何非常数复多项式必有根）的标准工具。

## 直观解释

Liouville 定理告诉我们：**如果一个复函数在所有方向上都“光滑”且“有界”，那它根本没有任何变化**。想象一个气球被限制在一个有限的空间内，如果表面完全光滑（没有褶皱、没有尖点），那么它只能是一个平平无奇的点——任何膨胀或扭曲都会在某处突破边界。在复平面上，全纯条件要求函数在每个方向上都满足 Cauchy-Riemann 方程，这种极强的约束使得有界性排除了所有非常数的可能性。

## 形式化表述

设 $f: \mathbb{C} \to \mathbb{C}$ 为整函数（entire function），即 $f$ 在 $\mathbb{C}$ 上处处复可微。若存在常数 $M > 0$ 使得：

$$|f(z)| \leq M, \quad \forall z \in \mathbb{C}$$

则 $f$ 必为常数函数：存在 $c \in \mathbb{C}$ 使得 $f(z) = c$ 对所有 $z \in \mathbb{C}$ 成立。

## 证明思路

1. **Cauchy 积分公式**：对任意 $z_0 \in \mathbb{C}$，导数可表为圆周积分
   $$f'(z_0) = \frac{1}{2\pi i} \oint_{|z-z_0|=R} \frac{f(z)}{(z-z_0)^2} dz$$
2. **估计导数**：利用 $|f(z)| \leq M$ 估计得 $|f'(z_0)| \leq \frac{M}{R}$
3. **令半径趋于无穷**：$R \to \infty$ 时 $\frac{M}{R} \to 0$，故 $f'(z_0) = 0$
4. **结论**：$f'$ 恒为零，$f$ 为常数

核心洞察在于全纯函数的导数由远处值决定，而有界性迫使远处值对导数的贡献消失。

## 示例

### 示例 1：指数函数

$f(z) = e^z$ 是整函数，但在实轴正方向和虚轴上无界，不满足 Liouville 条件。

### 示例 2：正弦函数

$f(z) = \sin z$ 虽是整函数，但在虚轴上 $|\sin(iy)| = \frac{e^{|y|} - e^{-|y|}}{2} \to \infty$（当 $y \to \infty$），故不违反 Liouville 定理。

### 示例 3：代数基本定理的证明

设 $P(z)$ 是非常数复多项式且无零点，则 $f(z) = \frac{1}{P(z)}$ 是整函数。当 $|z| \to \infty$ 时 $|P(z)| \to \infty$，故 $f$ 有界。由 Liouville 定理，$f$ 为常数，矛盾。因此 $P$ 必有零点。

## 应用

- **代数基本定理**：任何非常数复系数多项式至少有一个复根
- **整函数分类**：整函数的增长性与零点分布理论
- **偏微分方程**：调和函数的 Liouville 型定理
- **动力系统**：复动力系统中 Fatou 集与 Julia 集的研究
- **几何函数论**：拟共形映射与值分布理论

## 相关概念

- 整函数 (Entire Function)：在整个复平面上全纯的函数
- Cauchy 积分公式 (Cauchy Integral Formula)：全纯函数的积分表示
- 最大模原理 (Maximum Modulus Principle)：非恒全纯函数的模不能在内部取极大
- 代数基本定理 (Fundamental Theorem of Algebra)：复多项式的根的存在性
- 调和函数 (Harmonic Function)：满足 Laplace 方程的实值函数

## 参考

### 教材

- [Ahlfors. Complex Analysis. McGraw-Hill, 3rd edition, 1979. Chapter 4]
- [Stein & Shakarchi. Complex Analysis. Princeton, 2003. Chapter 2]

### 在线资源

- [Mathlib4 文档 - Complex.Liouville][https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Liouville.html]

---

*最后更新：2026-04-15 | 版本：v1.0.0*
