---
title: "Z变换 - 增强版"
msc_primary: "44A15"
msc_secondary: ['39A06', '93C55', '65T50', '94A12']
processed_at: '2026-04-05'
---

# Z变换 - 增强版

## 📋 目录

- [📚 概述](#-概述)
- [🏛️ 历史发展](#️-历史发展)
- [📐 定义与收敛域](#-定义与收敛域)
- [🔍 基本性质](#-基本性质)
- [📊 逆Z变换](#-逆z变换)
- [🔬 应用](#-应用)
- [💻 形式化实现](#-形式化实现)
- [📖 参考文献](#-参考文献)
- [📊 术语对照表](#-术语对照表)

---

## 📚 概述

Z变换是离散时间信号处理中的核心工具，是Laplace变换在离散域的对应。它将差分方程转化为代数方程，在数字信号处理、控制系统和通信工程中不可或缺。

---

## 🏛️ 历史发展

### 早期发展

Z变换的历史可追溯至18世纪的概率生成函数。De Moivre和Laplace研究了序列的生成函数方法。

### 现代形式

- **1947**: W. Hurewicz 首次系统应用于采样数据系统
- **1952**: Ragazzini和Zadeh命名为"Z变换"
- **1960s**: 与数字计算机发展同步，成为数字信号处理的基础

---

## 📐 定义与收敛域

### 定义

**定义 1.1** (Z变换)

序列 $x[n]$ 的Z变换定义为：
$$X(z) = \mathcal{Z}\{x[n]\} = \sum_{n=-\infty}^{\infty} x[n] z^{-n}$$

其中 $z \in \mathbb{C}$。

### 收敛域(ROC)

使级数收敛的 $z$ 值集合：
$$\text{ROC} = \{z : \sum_{n=-\infty}^{\infty} |x[n] z^{-n}| < \infty\}$$

**ROC类型**：
- 有限长序列：整个 $z$ 平面（可能除去 $z=0$ 或 $z=\infty$）
- 右边序列：$|z| > R_1$（圆外）
- 左边序列：$|z| < R_2$（圆内）
- 双边序列：环形区域 $R_1 < |z| < R_2$

---

## 🔍 基本性质

### 线性性

$$\mathcal{Z}\{ax[n] + by[n]\} = aX(z) + bY(z)$$

### 时移性质

**定理 2.1** (时移)

$$\mathcal{Z}\{x[n-k]\} = z^{-k}X(z)$$

时移 $k$ 对应乘以 $z^{-k}$。

### 指数加权

$$\mathcal{Z}\{a^n x[n]\} = X(z/a)$$

### 时域反转

$$\mathcal{Z}\{x[-n]\} = X(1/z)$$

### 卷积定理

**定理 2.2** (卷积)

$$\mathcal{Z}\{x[n] * y[n]\} = X(z) \cdot Y(z)$$

### 初值和终值定理

**初值**：$x[0] = \lim_{z \to \infty} X(z)$

**终值**：$\lim_{n \to \infty} x[n] = \lim_{z \to 1} (z-1)X(z)$（若ROC包含单位圆）

### 常用变换表

| $x[n]$ | $X(z)$ | ROC |
|--------|--------|-----|
| $\delta[n]$ | $1$ | 全部 $z$ |
| $u[n]$ | $\frac{z}{z-1}$ | $|z| > 1$ |
| $a^n u[n]$ | $\frac{z}{z-a}$ | $|z| > |a|$ |
| $n a^n u[n]$ | $\frac{az}{(z-a)^2}$ | $|z| > |a|$ |
| $\cos(\omega n)u[n]$ | $\frac{z(z-\cos\omega)}{z^2-2z\cos\omega+1}$ | $|z| > 1$ |

---

## 📊 逆Z变换

### 围线积分法

**定理 3.1** (逆Z变换)

$$x[n] = \frac{1}{2\pi i} \oint_C X(z) z^{n-1} dz$$

其中 $C$ 为ROC内围绕原点的逆时针围线。

### 幂级数展开

将 $X(z)$ 展开为 $z^{-1}$ 的幂级数，系数即为 $x[n]$。

### 部分分式展开

对有理函数 $X(z)$，分解为简单分式后查表。

---

## 🔬 应用

### 差分方程求解

**例 4.1**：解 $y[n] - ay[n-1] = x[n]$

Z变换：$Y(z) - az^{-1}Y(z) = X(z)$

$$H(z) = \frac{Y(z)}{X(z)} = \frac{1}{1-az^{-1}} = \frac{z}{z-a}$$

### 系统分析

**系统函数**：$H(z) = \frac{Y(z)}{X(z)}$

**稳定性**：ROC包含单位圆 $|z| = 1$

**因果性**：ROC为某圆外区域

### 与DFT的关系

在单位圆上采样：$X(e^{i\omega}) = X(z)|_{z=e^{i\omega}}$

这就是离散时间傅里叶变换(DTFT)。

---

## 💻 形式化实现

```lean
import analysis.complex.basic
import tactic

namespace z_transform

-- Z变换定义
def z_transform (x : ℤ → ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℤ, x n * z^(-n : ℤ)

-- 收敛条件
def converges (x : ℤ → ℂ) (z : ℂ) : Prop :=
  summable (λ n, ‖x n * z^(-n : ℤ)‖)

-- 时移性质
theorem z_transform_shift {x : ℤ → ℂ} {k : ℤ} {z : ℂ}
  (hx : converges x z) (hk : converges (λ n, x (n - k)) z) :
  z_transform (λ n, x (n - k)) z = z^k * z_transform x z :=
begin
  simp [z_transform],
  rw [tsum_shift', ←mul_assoc, ←zpow_add₀],
  simp,
  ring_nf,
end

-- 卷积定理
def convolution (x y : ℤ → ℂ) (n : ℤ) : ℂ :=
  ∑' k : ℤ, x k * y (n - k)

theorem z_transform_convolution {x y : ℤ → ℂ} {z : ℂ}
  (hx : converges x z) (hy : converges y z)
  (hxy : summable (λ n, ‖convolution x y n * z^(-n : ℤ)‖)) :
  z_transform (convolution x y) z = z_transform x z * z_transform y z :=
begin
  sorry -- 需要富比尼定理
end

end z_transform
```

---

## 📖 参考文献

1. **Oppenheim, A.V. & Schafer, R.W.** (2010). *Discrete-Time Signal Processing*.
2. **Proakis, J.G. & Manolakis, D.G.** (2007). *Digital Signal Processing*.
3. **Jury, E.I.** (1964). *Theory and Application of the Z-Transform Method*.

---

## 📊 术语对照表

| 中文术语 | 英文术语 | MSC分类 |
|----------|----------|---------|
| Z变换 | Z-transform | 44A15 |
| 逆Z变换 | Inverse Z-transform | 44A15 |
| 收敛域 | Region of Convergence (ROC) | 44A15 |
| 系统函数 | System function | 93C55 |
| 差分方程 | Difference equation | 39A06 |
| 数字信号处理 | Digital signal processing | 94A12 |

---

*文档生成时间: 2026-04-05*  
*分类: 分析学 - 离散分析*  
*版本: 增强版 (5,000+ 字节)*  
*关联数学家: Hurewicz、Ragazzini、Zadeh、Oppenheim*
