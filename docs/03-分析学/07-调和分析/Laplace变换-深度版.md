---
title: "Laplace变换 - 深度版"
msc_primary: "44A10"
msc_secondary: ['42A38', '65R10', '34A25', '35L05']
processed_at: '2026-04-05'
---

# Laplace变换 - 深度版

## 📋 目录

- [📚 概述](#-概述)
- [🏛️ 历史发展](#️-历史发展)
- [📐 定义与存在性](#-定义与存在性)
- [🔍 基本性质](#-基本性质)
- [📊 逆变换](#-逆变换)
- [🔬 应用](#-应用)
- [💻 形式化实现](#-形式化实现)
- [📖 参考文献](#-参考文献)
- [📊 术语对照表](#-术语对照表)

---

## 📚 概述

Laplace变换是工程和物理中最常用的积分变换。它将时域函数转换为复频域表示，将微分方程转化为代数方程，极大地简化了线性系统的分析。

---

## 🏛️ 历史发展

### 拉普拉斯的贡献

**皮埃尔-西蒙·拉普拉斯**（Pierre-Simon Laplace, 1749-1827）在概率论和天体力学中发展了生成函数方法。他在1812年的《概率分析理论》中系统研究了这种变换。

### 工程应用的发展

- **Oliver Heaviside** (1890s): 将算子方法应用于电路分析
- **Gustav Doetsch** (1920s): 建立了严格数学理论
- **现代控制理论**: Laplace变换成为传递函数分析的基础

---

## 📐 定义与存在性

### 定义

**定义 1.1** (Laplace变换)

设 $f(t)$ 在 $[0, \infty)$ 上定义，其Laplace变换定义为：
$$F(s) = \mathcal{L}\{f(t)\}(s) = \int_0^{\infty} e^{-st} f(t) dt$$

其中 $s \in \mathbb{C}$，$\text{Re}(s) > \sigma_0$（收敛横坐标）。

### 存在定理

**定理 1.1** (存在性)

若 $f$ 满足：
1. 在任意有限区间分段连续
2. 指数增长：$|f(t)| \leq Me^{\alpha t}$（$t$ 充分大）

则 $\mathcal{L}\{f\}(s)$ 在 $\text{Re}(s) > \alpha$ 存在且解析。

---

## 🔍 基本性质

### 线性性

$$\mathcal{L}\{af + bg\} = a\mathcal{L}\{f\} + b\mathcal{L}\{g\}$$

### 微分性质

**定理 2.1** (时域微分)

$$\mathcal{L}\{f'(t)\} = sF(s) - f(0)$$

$$\mathcal{L}\{f^{(n)}(t)\} = s^n F(s) - s^{n-1}f(0) - \cdots - f^{(n-1)}(0)$$

**证明**：分部积分。

### 积分性质

$$\mathcal{L}\left\{\int_0^t f(\tau) d\tau\right\} = \frac{F(s)}{s}$$

### 时移性质

$$\mathcal{L}\{f(t-a)u(t-a)\} = e^{-as}F(s)$$

### 频移性质

$$\mathcal{L}\{e^{at}f(t)\} = F(s-a)$$

### 卷积定理

**定理 2.2** (卷积)

$$\mathcal{L}\{f * g\} = \mathcal{L}\{f\} \cdot \mathcal{L}\{g\}$$

其中 $(f * g)(t) = \int_0^t f(\tau)g(t-\tau) d\tau$。

### 常用变换表

| $f(t)$ | $F(s)$ |
|--------|--------|
| $1$ | $\frac{1}{s}$ |
| $t^n$ | $\frac{n!}{s^{n+1}}$ |
| $e^{at}$ | $\frac{1}{s-a}$ |
| $\sin(\omega t)$ | $\frac{\omega}{s^2+\omega^2}$ |
| $\cos(\omega t)$ | $\frac{s}{s^2+\omega^2}$ |
| $\delta(t)$ | $1$ |

---

## 📊 逆变换

### 反演公式

**定理 3.1** (Bromwich积分)

$$f(t) = \mathcal{L}^{-1}\{F(s)\}(t) = \frac{1}{2\pi i} \int_{c-i\infty}^{c+i\infty} e^{st} F(s) ds$$

其中 $c > \sigma_0$（收敛横坐标）。

### 留数计算

若 $F(s)$ 为有理函数，$s_1, \ldots, s_n$ 为其极点：
$$f(t) = \sum_{k=1}^{n} \text{Res}(e^{st}F(s), s_k)$$

---

## 🔬 应用

### 微分方程求解

**例 4.1**：解 $y'' + y = 0$，$y(0) = 0$，$y'(0) = 1$

Laplace变换：$s^2Y - 1 + Y = 0$，$Y = \frac{1}{s^2+1}$

逆变换：$y(t) = \sin t$

### 电路分析

RLC电路的微分方程通过Laplace变换成为代数方程：
$$L s I(s) + R I(s) + \frac{1}{Cs} I(s) = V(s)$$

### 控制系统

传递函数：$H(s) = \frac{Y(s)}{X(s)}$

稳定性判据：所有极点位于左半平面。

---

## 💻 形式化实现

```lean
import measure_theory.integral.bochner
import analysis.complex.basic

namespace laplace_transform

-- Laplace变换定义
def laplace_transform (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ t in Ioi 0, complex.exp (-s * t) * f t

-- 存在性定理
theorem laplace_exists {f : ℝ → ℂ} (hf : continuous_on f (Ici 0))
  (hM : ∃ M α, ∀ t, 0 ≤ t → ‖f t‖ ≤ M * real.exp (α * t)) {s : ℂ}
  (hs : s.re > α) :
  ∃ L, tendsto (λ T, ∫ t in 0..T, complex.exp (-s * t) * f t) at_top (𝓝 L) :=
begin
  sorry -- 利用控制收敛定理
end

-- 微分性质
theorem laplace_derivative {f : ℝ → ℂ} (hf : differentiable ℝ f)
  {s : ℂ} (hs : s.re > 0) :
  laplace_transform (deriv f) s = s * laplace_transform f s - f 0 :=
begin
  sorry -- 分部积分
end

-- 卷积定理
theorem laplace_convolution {f g : ℝ → ℂ} (hf : continuous_on f (Ici 0))
  (hg : continuous_on g (Ici 0)) {s : ℂ} :
  laplace_transform (λ t, ∫ τ in 0..t, f τ * g (t - τ)) s =
    laplace_transform f s * laplace_transform g s :=
begin
  sorry -- Fubini定理
end

-- 逆变换（Bromwich积分）
def inverse_laplace (F : ℂ → ℂ) (t : ℝ) (c : ℝ) : ℂ :=
  (2 * π * I)⁻¹ • ∫ s in c + I • (-∞..∞), complex.exp (s * t) * F s

end laplace_transform
```

---

## 📖 参考文献

1. **Schiff, J.L.** (1999). *The Laplace Transform: Theory and Applications*.
2. **Oppenheim, A.V.** (1997). *Signals and Systems*.
3. **Doetsch, G.** (1974). *Introduction to the Theory and Application of the Laplace Transformation*.

---

## 📊 术语对照表

| 中文术语 | 英文术语 | MSC分类 |
|----------|----------|---------|
| Laplace变换 | Laplace transform | 44A10 |
| 逆Laplace变换 | Inverse Laplace transform | 44A10 |
| Bromwich积分 | Bromwich integral | 44A10 |
| 卷积 | Convolution | 44A35 |
| 传递函数 | Transfer function | 93C05 |
| 收敛横坐标 | Abscissa of convergence | 44A10 |

---

*文档生成时间: 2026-04-05*  
*分类: 分析学 - 调和分析*  
*版本: 深度版 (5,000+ 字节)*  
*关联数学家: 拉普拉斯、Heaviside、Doetsch、Bromwich*
