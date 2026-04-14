---
msc_primary: 00A99
processed_at: '2026-04-15'
title: 微积分基本定理 (Fundamental Theorem of Calculus)
---
# 微积分基本定理 (Fundamental Theorem of Calculus)

## Mathlib4 引用

```lean
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace FundamentalTheoremCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E} {a b : ℝ}

/-- 微积分基本定理 FTC-2：若 f 在 [a,b] 上连续且在 (a,b) 可导，则
    f' 在 [a,b] 上的积分等于 f(b) - f(a) -/
theorem integral_eq_sub_of_hasDerivAt
    (hcont : ContinuousOn f (uIcc a b))
    (hderiv : ∀ x ∈ uIoo a b, HasDerivAt f (f' x) x)
    (hintegrable : IntervalIntegrable f' volume a b) :
    ∫ x in a..b, f' x = f b - f a := by
  -- 参见 Mathlib4 MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
  sorry

end FundamentalTheoremCalculus
```

## 数学背景

微积分基本定理被誉为数学史上最重要的定理之一，由 Isaac Newton 和 Gottfried Wilhelm Leibniz 在17世纪末独立发现。该定理建立了微分与积分之间的深刻对偶关系：导数的积分还原原函数，积分上限函数的导数还原被积函数。这一定理不仅统一了此前被视为独立领域的切线问题与面积问题，也为现代科学和工程中的数学建模提供了核心工具。

## 直观解释

微积分基本定理告诉我们：**变化率的累积等于总变化**。想象一辆汽车的速度表：如果你把每一时刻的速度（导数）累积起来（积分），结果就是汽车行驶的总路程（函数值的变化）。反过来，如果你知道汽车从起点出发后的累计里程（积分函数），那么里程表读数的变化率就是瞬时速度（导数）。

这一定理揭示了微分和积分是互为逆运算的两个方面，正如加法和减法、乘法和除法的关系。

## 形式化表述

**FTC-1**：设 $f$ 在 $[a, b]$ 上连续，定义 $F(x) = \int_a^x f(t) dt$，则 $F$ 在 $[a, b]$ 上可导，且：

$$F'(x) = f(x)$$

**FTC-2**：设 $f$ 在 $[a, b]$ 上连续且在 $(a, b)$ 上有原函数 $F$（即 $F' = f$），则：

$$\int_a^b f(x) dx = F(b) - F(a)$$

在 Mathlib4 中，FTC-2 表述为 `intervalIntegral.integral_eq_sub_of_hasDerivAt`，FTC-1 的相关结果亦在同一文件中建立。

## 证明思路

**FTC-1 的证明**：
1. 对 $F(x+h) - F(x) = \int_x^{x+h} f(t) dt$ 应用中值定理
2. 由 $f$ 的连续性，$f$ 在小区间 $[x, x+h]$ 上的平均值趋于 $f(x)$
3. 因此 $\frac{F(x+h) - F(x)}{h} \to f(x)$，即 $F'(x) = f(x)$

**FTC-2 的证明**：
1. 构造辅助函数 $G(x) = \int_a^x f(t) dt$
2. 由 FTC-1，$G' = f$
3. 若 $F$ 也是 $f$ 的原函数，则 $(F - G)' = 0$，故 $F - G$ 为常数
4. 计算端点值得 $F(b) - F(a) = G(b) - G(a) = \int_a^b f(t) dt$

## 示例

### 示例 1：多项式函数

计算 $\int_0^2 x^3 dx$。

原函数为 $F(x) = \frac{x^4}{4}$，故：

$$\int_0^2 x^3 dx = F(2) - F(0) = \frac{16}{4} - 0 = 4$$

### 示例 2：三角函数

计算 $\int_0^{\pi} \sin x dx$。

原函数为 $F(x) = -\cos x$，故：

$$\int_0^{\pi} \sin x dx = -\cos(\pi) + \cos(0) = 1 + 1 = 2$$

### 示例 3：变上限积分求导

设 $F(x) = \int_0^{x^2} e^{t^2} dt$，求 $F'(x)$。

由 FTC-1 和链式法则：

$$F'(x) = e^{(x^2)^2} \cdot 2x = 2x e^{x^4}$$

## 应用

- **物理学**：位移-速度-加速度关系、功与能量的计算
- **工程学**：梁的弯矩与剪力分析、流体流量的计算
- **经济学**：边际成本与总成本、消费者剩余的计算
- **概率论**：概率密度函数与累积分布函数的互逆关系
- **数值分析**：Newton-Leibniz 公式是数值积分方法的理论基础

## 相关概念

- 原函数 (Antiderivative)：导数等于给定函数的函数
- Riemann 积分：基于分割与求和的定积分
- Lebesgue 积分：基于测度论的更一般积分
- 变上限积分 (Integral with Variable Upper Limit)：FTC-1 的核心对象
- Newton-Leibniz 公式：FTC-2 的经典名称

## 参考

### 教材

- [Apostol. Calculus. Wiley, 2nd edition, 1967. Chapter 5]
- [Rudin. Principles of Mathematical Analysis. McGraw-Hill, 3rd edition, 1976. Chapter 6]

### 历史文献

- [Newton. Philosophiæ Naturalis Principia Mathematica. 1687]
- [Leibniz. Nova methodus pro maximis et minimis. Acta Eruditorum, 1684]

### 在线资源

- [Mathlib4 文档 - FundThmCalculus][https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.html]

---

*最后更新：2026-04-15 | 版本：v1.0.0*
