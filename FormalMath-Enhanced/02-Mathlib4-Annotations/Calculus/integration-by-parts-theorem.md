---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: 分部积分定理 (Integration by Parts)
---
# 分部积分定理 (Integration by Parts)

## Mathlib4 引用

```lean
import Mathlib.MeasureTheory.Integral.IntervalIntegral

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ}
  {f g : ℝ → E} (hf : IntervalIntegrable f volume a b)
  (hg : IntervalIntegrable g volume a b)

/-- 分部积分定理：∫ u dv = uv - ∫ v du -/
theorem integration_by_parts (hu : ContinuousOn u (uIcc a b)) (hv : ContinuousOn v (uIcc a b))
    (hdu : ∀ x ∈ uIcc a b, HasDerivAt u (u' x) x) (hdv : ∀ x ∈ uIcc a b, HasDerivAt v (v' x) x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x * v' x = (u b * v b - u a * v a) - ∫ x in a..b, u' x * v x := by
  -- 由乘积求导法则 (uv)' = u'v + uv' 直接积分得到
  sorry

end MeasureTheory
```

## 数学背景

分部积分定理是微积分中最基本、应用最广泛的积分技巧之一，它是乘积求导法则 $(uv)' = u'v + uv'$ 的直接推论。分部积分的历史可以追溯到17世纪微积分的创立时期，莱布尼茨和牛顿都意识到了这一技巧。

## 直观解释

分部积分定理提供了一个将复杂积分转化为更简单积分的强大技巧。它的核心思想是：当你遇到一个被积函数是两个函数乘积的积分时，可以选择其中一个函数作为 u（待求导），另一个作为 dv（待积分），然后将原来的积分转换为边界项减去一个新的积分。这个新积分往往比原来的更容易计算。

## 形式化表述

设 $u$ 和 $v$ 是区间 $[a, b]$ 上的可微函数，且 $u', v'$ 可积，则：

$$\int_a^b u(x) v'(x) \, dx = [u(x)v(x)]_a^b - \int_a^b u'(x) v(x) \, dx$$

其中 $[u(x)v(x)]_a^b = u(b)v(b) - u(a)v(a)$ 是边界项。

不定积分形式：

$$\int u \, dv = uv - \int v \, du$$

其中：

- $u(x)$ 和 $v(x)$ 是被积函数的两个因子
- $u'(x)$ 和 $v'(x)$ 分别是它们的导数
- 边界项在无穷区间或周期边界条件下可能为零

## 证明思路

1. **乘积法则**：$(uv)' = u'v + uv'$
2. **两边积分**：$\int_a^b (uv)' dx = \int_a^b u'v \, dx + \int_a^b uv' \, dx$
3. **Newton-Leibniz 公式**：左边 $= [uv]_a^b$
4. **整理得证**：$\int_a^b uv' \, dx = [uv]_a^b - \int_a^b u'v \, dx$

核心洞察在于通过交换求导和积分的角色来简化被积函数的结构。

## 示例

### 示例 1：幂函数与指数函数

计算 $\int_0^1 x e^x dx$。令 $u = x$, $dv = e^x dx$，则 $du = dx$, $v = e^x$。
结果 $= [x e^x]_0^1 - \int_0^1 e^x dx = e - (e - 1) = 1$。

### 示例 2：对数函数

计算 $\int_1^e \ln x \, dx$。令 $u = \ln x$, $dv = dx$，则 $du = dx/x$, $v = x$。
结果 $= [x \ln x]_1^e - \int_1^e dx = e - (e - 1) = 1$。

### 示例 3：正交多项式

Legendre 多项式的正交性可以通过反复分部积分证明。

## 应用

- **定积分计算**：计算对数、反三角函数和幂次乘积的积分
- **偏微分方程**：弱解的定义和能量估计
- **概率论**：矩的计算和特征函数的推导
- **量子场论**：量子电动力学中的 Ward 恒等式
- **数值分析**：谱方法和有限元方法中的分部求和

## 相关概念

- 乘积法则 (Product Rule)：$(uv)' = u'v + uv'$
- Newton-Leibniz 公式：微积分基本定理的积分形式
- 广义函数 (Distribution)：分部积分在更广泛函数类上的推广
- Gamma 函数 (Gamma Function)：$\Gamma(n+1) = n!$ 的递推证明
- 变分法 (Calculus of Variations)：Euler-Lagrange 方程的推导

## 参考

### 教材

- [G. B. Thomas, R. L. Finney. Calculus and Analytic Geometry. Addison-Wesley, 9th edition, 1996. Chapter 8]
- [W. Rudin. Real and Complex Analysis. McGraw-Hill, 3rd edition, 1987. Chapter 6]

### 在线资源

- [Mathlib4 - IntervalIntegral](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/IntervalIntegral.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*
