---
msc_primary: 00A99
processed_at: '2026-04-15'
title: Gamma 函数 (Gamma Function)
---
# Gamma 函数 (Gamma Function)

## Mathlib4 引用

```lean
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

namespace SpecialFunctions

/-- Gamma 函数：Γ(s) = ∫_0^∞ t^{s-1} e^{-t} dt -/
noncomputable def Gamma (s : ℂ) : ℂ :=
  ∫ t in Ioi 0, t ^ (s - 1) * Real.exp (-t)

/-- Gamma 函数的递推关系：Γ(s+1) = s Γ(s) -/
theorem Gamma_add_one {s : ℂ} (hs : s ≠ 0) :
    Gamma (s + 1) = s * Gamma s := by
  -- 利用分部积分证明
  sorry

/-- Gamma 函数在正整数处的值：Γ(n) = (n-1)! -/
theorem Gamma_nat_eq_factorial (n : ℕ) :
    Gamma (n + 1) = n.factorial := by
  -- 对 n 归纳，利用递推关系
  sorry

end SpecialFunctions
```

## 数学背景

Gamma 函数是数学分析中最重要、最著名的特殊函数之一，由瑞士数学家莱昂哈德·欧拉（Leonhard Euler）在18世纪初引入，后经勒让德（Legendre）和高斯（Gauss）等人发展和推广。它是阶乘函数在复数域上的自然解析延拓。

## 直观解释

Gamma 函数是阶乘的连续版本。在离散数学中，$n!$ 只对非负整数有定义。但自然界中的许多现象需要一种连续阶乘。Gamma 函数完美地解决了这个问题：$\Gamma(n) = (n-1)!$ 对正整数成立，而 $\Gamma(1/2) = \sqrt{\pi}$ 等值则将阶乘的概念优雅地推广到了所有复数（除了非正整数）。

## 形式化表述

Gamma 函数定义为（对 $\text{Re}(s) > 0$）：

$$\Gamma(s) = \int_0^\infty t^{{s-1}} e^{{-t}} \, dt$$

基本性质：

1. **递推关系**：$\Gamma(s+1) = s \Gamma(s)$（对 $s \neq 0, -1, -2, \dots$）
2. **正整数取值**：$\Gamma(n) = (n-1)!$（$n = 1, 2, 3, \dots$）
3. **特殊值**：$\Gamma(1/2) = \sqrt{\pi}$，$\Gamma(3/2) = \sqrt{\pi}/2$
4. **余元公式**：$\Gamma(s) \Gamma(1-s) = \frac{\pi}{\sin(\pi s)}$
5. **倍元公式**：$\Gamma(2s) = \frac{2^{{2s-1}}}{\sqrt{\pi}} \Gamma(s) \Gamma(s + 1/2)$

解析延拓：利用递推关系，$\Gamma(s)$ 可以延拓为整个复平面上的亚纯函数，在 $s = 0, -1, -2, \dots$ 处有一阶极点。

## 证明思路

1. **积分收敛性**：对 $\text{Re}(s) > 0$，积分在 $t = 0$ 和 $t = \infty$ 处均收敛
2. **分部积分**：$\Gamma(s+1) = \int_0^\infty t^s e^{{-t}} dt = s \int_0^\infty t^{{s-1}} e^{{-t}} dt = s \Gamma(s)$
3. **归纳得阶乘**：由 $\Gamma(1) = 1$ 和递推关系，$\Gamma(n+1) = n!$
4. **解析延拓**：对 $\text{Re}(s) \leq 0$，利用递推关系选足够大的 $n$ 定义

核心洞察在于递推关系 $\Gamma(s+1) = s\Gamma(s)$ 是阶乘性质的连续推广。

## 示例

### 示例 1：概率分布

Gamma 分布的密度函数为 $f(x) = \frac{\beta^\alpha}{\Gamma(\alpha)} x^{{\alpha-1}} e^{{-\beta x}}$。$\Gamma(\alpha)$ 作为归一化常数保证总概率为 1。当 $\alpha = n/2$, $\beta = 1/2$ 时，即为卡方分布。

### 示例 2：高斯积分

$\Gamma(1/2) = \sqrt{\pi}$。这是高斯积分 $\int_{{-\infty}}^\infty e^{{-x^2}} dx = \sqrt{\pi}$ 的重要推论。

### 示例 3：Riemann 假设

Riemann ζ 函数与 Gamma 函数通过函数方程联系。Gamma 函数的极点和增长性对 ζ 函数的零点分布研究至关重要。

## 应用

- **概率统计**：Gamma 分布、Beta 分布和卡方分布的定义
- **数论**：Riemann ζ 函数方程和素数定理
- **统计物理**：配分函数和玻色-爱因斯坦统计
- **量子场论**：维数正规化和 Feynman 积分
- **组合数学**：广义二项式系数和超几何级数

## 相关概念

- 阶乘 (Factorial)：Gamma 函数在正整数处的特例
- 解析延拓 (Analytic Continuation)：将函数定义域扩展到更大区域
- 亚纯函数 (Meromorphic Function)：除孤立极点外全纯的函数
- 余元公式 (Reflection Formula)：$\Gamma(s)\Gamma(1-s) = \pi / \sin(\pi s)$
- 高斯积分 (Gaussian Integral)：$\int_{{-\infty}}^\infty e^{{-x^2}} dx = \sqrt{\pi}$

## 参考

### 教材

- [E. Artin. The Gamma Function. Holt, Rinehart and Winston, 1964]
- [G. E. Andrews, R. Askey, R. Roy. Special Functions. Cambridge, 1999. Chapter 1]

### 在线资源

- [Mathlib4 - Gamma](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*
