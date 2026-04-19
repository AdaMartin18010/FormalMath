---
title: "Gamma函数与Beta函数 - 深度版"
msc_primary: 33

  - 33B15
msc_secondary: ['33B20', '26A33', '30B10', '11M06']
processed_at: '2026-04-05'
---

# Gamma函数与Beta函数 - 深度版

## 📋 目录

- [Gamma函数与Beta函数 - 深度版](#gamma函数与beta函数---深度版)
  - [📋 目录](#目录)
  - [📚 概述](#概述)
  - [🏛️ 历史发展](#历史发展)
    - [欧拉的阶乘插值](#欧拉的阶乘插值)
    - [高斯与Weierstrass的表示](#高斯与weierstrass的表示)
  - [📐 Gamma函数](#gamma函数)
    - [定义](#定义)
    - [基本性质](#基本性质)
  - [🔍 Beta函数](#beta函数)
    - [定义](#定义)
    - [与Gamma函数的关系](#与gamma函数的关系)
    - [其他表示](#其他表示)
  - [📊 重要公式与性质](#重要公式与性质)
    - [特殊值](#特殊值)
    - [积分表示总结](#积分表示总结)
    - [Stirling公式](#stirling公式)
  - [🔬 应用](#应用)
    - [概率论](#概率论)
    - [数论](#数论)
    - [物理学](#物理学)
  - [💻 形式化实现](#形式化实现)
  - [📖 参考文献](#参考文献)
  - [📊 术语对照表](#术语对照表)

---

## 📚 概述

Gamma函数 $\Gamma(z)$ 和 Beta函数 $B(p,q)$ 是分析学中最重要的特殊函数。它们推广了阶乘概念，在概率论、数论、物理学中有广泛应用。

**核心关系**：$B(p,q) = \frac{\Gamma(p)\Gamma(q)}{\Gamma(p+q)}$

---

## 🏛️ 历史发展

### 欧拉的阶乘插值

**莱昂哈德·欧拉**（1729年）研究了如何将阶乘推广到非整数。他提出：
$$n! = \int_0^1 (-\ln x)^n dx$$

令 $x = e^{-t}$，得到现代Gamma函数形式：
$$\Gamma(n+1) = \int_0^{\infty} t^n e^{-t} dt = n!$$

### 高斯与Weierstrass的表示

**卡尔·弗里德里希·高斯**引入了无穷乘积表示：
$$\Gamma(z) = \lim_{n \to \infty} \frac{n! n^z}{z(z+1)\cdots(z+n)}$$

**卡尔·魏尔斯特拉斯**给出了Weierstrass形式：
$$\frac{1}{\Gamma(z)} = ze^{\gamma z} \prod_{n=1}^{\infty} \left(1 + \frac{z}{n}\right)e^{-z/n}$$

其中 $\gamma$ 是欧拉-马歇罗尼常数。

---

## 📐 Gamma函数

### 定义

**定义 1.1** (Gamma函数)

对 $\text{Re}(z) > 0$：
$$\Gamma(z) = \int_0^{\infty} t^{z-1} e^{-t} dt$$

### 基本性质

**定理 1.1** (递推公式)

$$\Gamma(z+1) = z \cdot \Gamma(z)$$

**证明**：分部积分
$$\Gamma(z+1) = \int_0^{\infty} t^z e^{-t} dt = [-t^z e^{-t}]_0^{\infty} + z\int_0^{\infty} t^{z-1} e^{-t} dt = z\Gamma(z)$$

**推论**：对 $n \in \mathbb{N}$，$\Gamma(n+1) = n!$

**定理 1.2** (余元公式 / Euler反射公式)

$$\Gamma(z)\Gamma(1-z) = \frac{\pi}{\sin(\pi z)}, \quad z \notin \mathbb{Z}$$

**推论**：$\Gamma(1/2) = \sqrt{\pi}$

**定理 1.3** (倍元公式 / Legendre倍元公式)

$$\Gamma(2z) = \frac{2^{2z-1}}{\sqrt{\pi}} \Gamma(z) \Gamma(z + 1/2)$$

---

## 🔍 Beta函数

### 定义

**定义 2.1** (Beta函数)

对 $\text{Re}(p) > 0, \text{Re}(q) > 0$：
$$B(p,q) = \int_0^1 x^{p-1}(1-x)^{q-1} dx$$

### 与Gamma函数的关系

**定理 2.1** (基本关系)

$$B(p,q) = \frac{\Gamma(p)\Gamma(q)}{\Gamma(p+q)}$$

**证明**：利用卷积和Fubini定理

$$\Gamma(p)\Gamma(q) = \int_0^{\infty}\int_0^{\infty} t^{p-1}s^{q-1} e^{-(t+s)} dt ds$$

换元 $t = xu, s = (1-x)u$（雅可比行列式为 $u$）：
$$= \int_0^1 x^{p-1}(1-x)^{q-1} dx \cdot \int_0^{\infty} u^{p+q-1} e^{-u} du = B(p,q) \cdot \Gamma(p+q)$$

### 其他表示

**三角表示**：
$$B(p,q) = 2\int_0^{\pi/2} \sin^{2p-1}\theta \cos^{2q-1}\theta d\theta$$

**无穷积分表示**：
$$B(p,q) = \int_0^{\infty} \frac{t^{p-1}}{(1+t)^{p+q}} dt$$

---

## 📊 重要公式与性质

### 特殊值

| $z$ | $\Gamma(z)$ |
|-----|-------------|
| 1 | 1 |
| 1/2 | $\sqrt{\pi}$ |
| 3/2 | $\frac{\sqrt{\pi}}{2}$ |
| 2 | 1 |
| 5/2 | $\frac{3\sqrt{\pi}}{4}$ |
| 3 | 2 |

### 积分表示总结

$$\Gamma(z) = \int_0^{\infty} t^{z-1}e^{-t}dt = 2\int_0^{\infty} t^{2z-1}e^{-t^2}dt$$

$$B(p,q) = \int_0^1 x^{p-1}(1-x)^{q-1}dx = \int_0^{\infty} \frac{t^{p-1}}{(1+t)^{p+q}}dt$$

### Stirling公式

**定理 3.1** (Stirling渐近公式)

$$\Gamma(z+1) \sim \sqrt{2\pi z} \left(\frac{z}{e}\right)^z, \quad |z| \to \infty, |\arg z| < \pi$$

特别地：
$$n! \sim \sqrt{2\pi n} \left(\frac{n}{e}\right)^n$$

---

## 🔬 应用

### 概率论

**Gamma分布**：若 $X \sim \text{Gamma}(\alpha, \beta)$，则：
$$f(x) = \frac{\beta^\alpha}{\Gamma(\alpha)} x^{\alpha-1} e^{-\beta x}$$

**Beta分布**：$X \sim \text{Beta}(\alpha, \beta)$：
$$f(x) = \frac{x^{\alpha-1}(1-x)^{\beta-1}}{B(\alpha, \beta)}$$

### 数论

**Riemann zeta函数与Gamma函数**（函数方程）：
$$\zeta(s) = 2^s \pi^{s-1} \sin\left(\frac{\pi s}{2}\right) \Gamma(1-s) \zeta(1-s)$$

### 物理学

**量子力学**：氢原子波函数归一化涉及Gamma函数。

**统计力学**：配分函数计算。

---

## 💻 形式化实现

```lean
import analysis.special_functions.gamma
import analysis.special_functions.beta

namespace special_functions

-- Gamma函数定义
def gamma (z : ℂ) : ℂ :=
  ∫ t in Ioi 0, complex.exp (-t) * t^(z-1)

-- Gamma函数递推公式
theorem gamma_add_one {z : ℂ} (hz : z ≠ 0) : gamma (z + 1) = z * gamma z :=
begin
  sorry -- 分部积分
end

-- Gamma函数在正整数点的值
theorem gamma_nat (n : ℕ) : gamma (n + 1) = n.factorial :=
begin
  induction n with n ih,
  { simp [gamma], sorry },
  { rw [nat.factorial_succ, gamma_add_one, ih],
    simp, ring_nf, simp [nat.cast_add_one] }
end

-- 余元公式
theorem gamma_reflection {z : ℂ} (hz : z ∉ ℤ) :
  gamma z * gamma (1 - z) = π / complex.sin (π * z) :=
begin
  sorry -- 需要复分析工具
end

-- Beta函数定义
def beta (p q : ℂ) : ℂ :=
  ∫ x in Ioo 0 1, x^(p-1) * (1-x)^(q-1)

-- Beta与Gamma的关系
theorem beta_gamma {p q : ℂ} (hp : re p > 0) (hq : re q > 0) :
  beta p q = gamma p * gamma q / gamma (p + q) :=
begin
  sorry -- 利用卷积和Fubini定理
end

-- Stirling公式
theorem stirling_formula {z : ℂ} (hz : re z > 0) :
  gamma (z + 1) ~[filter.at_top] real.sqrt (2 * π * z) * (z / complex.exp 1)^z :=
begin
  sorry -- 渐近分析
end

end special_functions
```

---

## 📖 参考文献

1. **Andrews, G.E., Askey, R., Roy, R.** (1999). *Special Functions*. Cambridge.
2. **Artin, E.** (1964). *The Gamma Function*. Holt, Rinehart and Winston.
3. **Euler, L.** (1729). *De progressionibus transcendentibus*.
4. **Whittaker, E.T. & Watson, G.N.** (1927). *A Course of Modern Analysis*.

---

## 📊 术语对照表

| 中文术语 | 英文术语 | MSC分类 |
|----------|----------|---------|
| Gamma函数 | Gamma function | 33B15 |
| Beta函数 | Beta function | 33B15 |
| 余元公式 | Reflection formula | 33B15 |
| 倍元公式 | Duplication formula | 33B15 |
| Stirling公式 | Stirling's formula | 33B15 |
| 欧拉-马歇罗尼常数 | Euler-Mascheroni constant | 11Y60 |
| 阶乘 | Factorial | 05A10 |

---

*文档生成时间: 2026-04-05*
*分类: 分析学 - 特殊函数*
*版本: 深度版 (5,000+ 字节)*
*关联数学家: 欧拉、高斯、Legendre、Stirling、Weierstrass*
