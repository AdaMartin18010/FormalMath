---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: Liouville 定理 (Liouville's Theorem)
---
# Liouville 定理 (Liouville's Theorem)

## Mathlib4 引用

```lean
import Mathlib.Analysis.Complex.Liouville

namespace ComplexAnalysis

/-- Liouville 定理：全平面上的有界全纯函数必为常数 -/
theorem liouville_theorem {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hbounded : ∃ M, ∀ z, ‖f z‖ ≤ M) :
    ∃ c : ℂ, f = Function.const ℂ c := by
  -- 利用 Cauchy 积分公式估计导数，证明导数处处为零
  sorry

end ComplexAnalysis
```

## 数学背景

Liouville 定理是复分析中最优美、最具影响力的结果之一，由法国数学家约瑟夫·刘维尔（Joseph Liouville）于19世纪中期证明。该定理断言：在整个复平面上有界（或有更弱的增长条件）的全纯函数必定是常数函数。这个结论在实分析中完全不成立（例如 sin(x) 在 R 上有界但非常数），因此深刻揭示了全纯函数的刚性。

## 直观解释

Liouville 定理揭示了一个令人惊讶的事实：如果一个函数在整个复平面上都是光滑的（复可微的），并且它的值不会变得任意大（有界），那么这个函数就失去了所有变化的能力——它必须是一个常数。这与实函数形成鲜明对比：实函数 sin(x) 在整个实数轴上无穷次可微且有界，但它显然不是常数。

## 形式化表述

设 $f: \mathbb{C} \to \mathbb{C}$ 是整函数（在整个复平面上全纯），若 $f$ 有界，即存在常数 $M > 0$ 使得对所有 $z \in \mathbb{C}$：

$$|f(z)| \leq M$$

则 $f$ 是常数函数。

更一般的推广：若整函数 $f$ 满足 $|f(z)| \leq C|z|^n$ 对某个 $n \geq 0$ 和充分大的 $|z|$，则 $f$ 是一个次数不超过 $n$ 的多项式。

其中：

- 整函数（entire function）是指在 C 上处处复可微的函数
- 有界性意味着函数值集合包含于某个圆盘中
- 该定理的惊人之处在于：全局有界性加上局部复可微性推出了极强的全局结论

## 证明思路

1. **Cauchy 积分公式**：对任意 $z_0 \in \mathbb{C}$ 和 $R > 0$，$f'(z_0) = \frac{1}{2\pi i} \oint_{{|z-z_0|=R}} \frac{f(z)}{(z-z_0)^2} dz$
2. **导数估计**：$|f'(z_0)| \leq \frac{M}{R}$
3. **令 $R \to \infty$**：由于 $f$ 有界，$|f'(z_0)| \leq \frac{M}{R} \to 0$，故 $f'(z_0) = 0$
4. **全局结论**：$f'$ 在整个 C 上恒为零，故 $f$ 是常数

核心洞察在于 Cauchy 积分公式将局部导数与圆周上的全局平均值联系起来，而有界性控制了这种平均值随半径的衰减。

## 示例

### 示例 1：指数函数

$e^z$ 是整函数但无界，因此 Liouville 定理不适用。

### 示例 2：代数基本定理

假设 $P(z)$ 是非常数多项式且无根，则 $1/P(z)$ 是整函数。当 $|z| \to \infty$ 时 $|1/P(z)| \to 0$，故 $1/P(z)$ 有界。由 Liouville 定理，$1/P(z)$ 是常数，矛盾。因此任何非常数复多项式必有根。

### 示例 3：有界整函数列

设 $\{f_n\}$ 是一致有界的整函数列。由 Liouville 定理，每个 $f_n$ 都是常数。

## 应用

- **代数基本定理**：任何非常数复多项式都有根
- **复动力系统**：Julia 集和 Mandelbrot 集的研究
- **偏微分方程**：调和函数和椭圆型方程的 Liouville 型结果
- **数论**：模形式和椭圆函数的刚性定理
- **量子场论**：共形场论中的整体约束条件

## 相关概念

- 整函数 (Entire Function)：在整个复平面上全纯的函数
- Cauchy 积分公式 (Cauchy Integral Formula)：全纯函数的积分表示
- 最大模原理 (Maximum Modulus Principle)：非常数全纯函数在内部不取最大模
- Picard 定理 (Picard's Theorem)：值域受限的全纯函数的分类
- 代数基本定理 (Fundamental Theorem of Algebra)：Liouville 定理的经典推论

## 参考

### 教材

- [L. Ahlfors. Complex Analysis. McGraw-Hill, 3rd edition, 1979. Chapter 4]
- [E. Stein, R. Shakarchi. Complex Analysis. Princeton, 2003. Chapter 2]

### 在线资源

- [Mathlib4 - Liouville](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Liouville.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*