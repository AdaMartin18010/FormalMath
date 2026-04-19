---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: 微积分基本定理 (Fundamental Theorem of Calculus)
---
# 微积分基本定理 (Fundamental Theorem of Calculus)

## Mathlib4 引用

```lean
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.Integral

namespace IntervalIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- 微积分基本定理第一部分 -/
theorem fundamental_theorem_of_calculus_I (f : ℝ → E) (a b : ℝ)
    (hf : IntervalIntegrable f volume a b) (hF : ∀ x ∈ [[a, b]], HasDerivAt F (f x) x) :
    ∫ x in a..b, f x = F b - F a := by
  -- 原函数与定积分的关系
  sorry

/-- 微积分基本定理第二部分 -/
theorem fundamental_theorem_of_calculus_II (f : ℝ → E) (a b : ℝ)
    (hf : ContinuousOn f [[a, b]]) (x : ℝ) (hx : x ∈ [[a, b]]) :
    HasDerivAt (fun u => ∫ t in a..u, f t) (f x) x := by
  -- 变上限积分求导
  sorry

end IntervalIntegral
```

## 数学背景

微积分基本定理由艾萨克·牛顿和戈特弗里德·莱布尼茨在17世纪末独立发现并发展，是微积分学最核心的结果。它揭示了微分和积分作为互逆运算的本质联系，将看似不相关的切线问题（微分）和面积问题（积分）统一起来，为现代科学和工程奠定了数学基础。

## 直观解释

微积分基本定理告诉我们：**积分和微分是互逆运算**。第一部分说明，要计算曲线下的面积，只需找到原函数在端点处的差值；第二部分说明，对变上限积分求导就得到被积函数。这就像"先走后回"或"先爬上后爬下"，最终回到原点。

## 形式化表述

**第一部分**：若 $F$ 是 $f$ 在 $[a,b]$ 上的原函数（即 $F' = f$），则：
$$\int_a^b f(x)\,dx = F(b) - F(a)$$

**第二部分**：若 $f$ 连续，定义 $G(x) = \int_a^x f(t)\,dt$，则：
$$G'(x) = f(x)$$

## 证明思路

1. **第一部分**：利用微分中值定理，将区间分割为小区间，证明黎曼和收敛到 $F(b) - F(a)$
2. **第二部分**：利用连续性，证明差商的极限就是被积函数值
3. **核心洞察**：微分和积分的互逆性来自于它们描述变化率和累积量的对偶关系

## 示例

### 示例 1：多项式积分

计算 $\int_0^1 x^2\,dx$

原函数：$F(x) = \frac{x^3}{3}$

结果：$F(1) - F(0) = \frac{1}{3} - 0 = \frac{1}{3}$

### 示例 2：变上限积分

设 $G(x) = \int_0^x \sin t\,dt = 1 - \cos x$

则 $G'(x) = \sin x$，验证了第二部分。

## 应用

- **物理学**：功、能量、质心计算
- **工程学**：信号处理、控制系统
- **经济学**：累积收益、消费者剩余
- **概率论**：累积分布函数与密度函数的关系

## 相关概念

- 不定积分 (Indefinite Integral)：原函数族
- 定积分 (Definite Integral)：区间上的积分
- 牛顿-莱布尼茨公式：基本定理的另一种表述
- 格林定理：二维推广

## 参考

### 教材

- [Stewart. Calculus: Early Transcendentals. Cengage, 8th edition, 2015. Chapter 5]
- [Rudin. Principles of Mathematical Analysis. McGraw-Hill, 3rd edition, 1976. Chapter 6]

### 历史文献

- [Newton. Philosophiæ Naturalis Principia Mathematica. 1687]
- [Leibniz. Nova methodus pro maximis et minimis. 1684]

### 在线资源

- [Mathlib4 文档 - IntervalIntegral][https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/IntervalIntegral.html](需更新)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
