---
title: Sobolev空间-弱导数
description: 系统介绍弱导数的定义与基本性质、Sobolev空间Wk,p的构造、逼近定理、延拓定理与迹定理的陈述，建立现代PDE理论的函数空间基础。
msc_primary:
  - 46E35
msc_secondary:
  - 35D30
  - 35A01
  - 46F05
processed_at: '2026-04-20'
references:
  textbooks:
    - id: evans_pde
      type: textbook
      title: Partial Differential Equations
      authors:
        - Lawrence C. Evans
      publisher: American Mathematical Society
      year: 2010
      msc: 35-01
    - id: adams_sobolev
      type: textbook
      title: Sobolev Spaces
      authors:
        - Robert A. Adams
        - John J. F. Fournier
      publisher: Academic Press
      year: 2003
      msc: 46E35
---

# Sobolev空间-弱导数

**广义微分 — 从经典解到弱解的函数空间**

---

## 1. 弱导数的动机

### 1.1 经典解的局限

许多PDE（如带有不连续系数的方程或非线性方程）不存在经典解（$C^2$ 函数）。例如，一维Poisson方程 $-u'' = \delta$（点源）的解 $u(x) = |x|/2$ 在 $x=0$ 处不可微。

**需求**：扩展导数的概念，使更广泛的函数类可微，同时保留积分运算的合理性。

### 1.2 分布导数

对局部可积函数 $u \in L^1_{\text{loc}}(\Omega)$，若存在 $v \in L^1_{\text{loc}}(\Omega)$ 使得
$$\int_\Omega u \, \partial^\alpha \varphi \, dx = (-1)^{|\alpha|} \int_\Omega v \, \varphi \, dx, \quad \forall \varphi \in C_c^\infty(\Omega)$$
则称 $v$ 为 $u$ 的**$\alpha$-阶弱导数**（或分布导数），记为 $D^\alpha u = v$。

**注**：弱导数若存在则在 $L^1_{\text{loc}}$ 中唯一（a.e.）。

---

## 2. 弱导数的基本性质

### 2.1 与经典导数的关系

**命题**：若 $u \in C^k(\Omega)$，则经典导数与弱导数一致。

*证明*：分部积分。$\square$

**例1**：$u(x) = |x|$ 在 $\mathbb{R}$ 上。对任意 $\varphi \in C_c^\infty(\mathbb{R})$，
$$\int_{-\infty}^\infty |x| \varphi'(x) dx = \int_0^\infty x \varphi'(x) dx + \int_{-\infty}^0 (-x) \varphi'(x) dx$$
分部积分得
$$= -\int_0^\infty \varphi(x) dx + \int_{-\infty}^0 \varphi(x) dx = -\int_{-\infty}^\infty \text{sgn}(x) \varphi(x) dx$$
故 $u' = \text{sgn}(x)$（弱导数）。

再求一次：$\text{sgn}(x)$ 的弱导数为 $2\delta_0$（Dirac测度），不是局部可积函数。故 $|x| \notin W^{2,1}$。

### 2.2 弱导数的运算规则

- **线性**：$D^\alpha(au + bv) = a D^\alpha u + b D^\alpha v$
- **Leibniz法则**：对 $u \in W^{1,p}$，$\eta \in C^1$，$D(\eta u) = \eta Du + u D\eta$
- **链式法则**：对单调Lipschitz $f$，$D(f \circ u) = f'(u) Du$（在适当意义下）

---

## 3. Sobolev空间 $W^{k,p}$

### 3.1 定义

设 $k \geq 0$ 为整数，$1 \leq p \leq \infty$。**Sobolev空间**
$$W^{k,p}(\Omega) = \{u \in L^p(\Omega) \mid D^\alpha u \in L^p(\Omega) \text{ 对所有 } |\alpha| \leq k\}$$
配以范数
$$\|u\|_{W^{k,p}} = \left(\sum_{|\alpha| \leq k} \|D^\alpha u\|_{L^p}^p\right)^{1/p}$$
（$p=\infty$ 时取上确界）。

**定理**：$W^{k,p}(\Omega)$ 为Banach空间；$p=2$ 时 $H^k(\Omega) = W^{k,2}(\Omega)$ 为Hilbert空间。

### 3.2 零边界Sobolev空间

$W_0^{k,p}(\Omega)$ 定义为 $C_c^\infty(\Omega)$ 在 $W^{k,p}(\Omega)$ 中的闭包。直观上，$W_0^{1,p}(\Omega)$ 中的函数在边界上"为零"（在迹意义下）。

---

## 4. 逼近定理

### 4.1 局部逼近

**定理（Meyers-Serrin）**：$C^\infty(\Omega) \cap W^{k,p}(\Omega)$ 在 $W^{k,p}(\Omega)$ 中稠密。

即任何Sobolev函数可被光滑函数在 $W^{k,p}$ 范数下逼近。

### 4.2 整体逼近

若 $\Omega$ 有界且边界Lipschitz，则 $C^\infty(\overline{\Omega})$ 在 $W^{k,p}(\Omega)$ 中稠密。

对 $W_0^{1,p}(\Omega)$，$C_c^\infty(\Omega)$ 稠密（由定义）。

---

## 5. 延拓定理

### 5.1 有界域的延拓

**定理**：设 $\Omega \subset \subset \mathbb{R}^n$ 有 $C^1$ 边界。存在有界线性算子
$$E: W^{1,p}(\Omega) \to W^{1,p}(\mathbb{R}^n)$$
使得 $Eu|_\Omega = u$。

*构造*：局部拉直边界，对 $x_n > 0$ 的部分用反射延拓，再用单位分解拼合。

### 5.2 延拓的意义

延拓定理使Sobolev函数可视为全空间函数，从而应用Fourier分析等工具。

---

## 6. 迹定理

### 6.1 迹算子

对光滑函数，$u|_{\partial\Omega}$ 有明确意义。对Sobolev函数，边界值需通过**迹**定义。

**定理（迹定理）**：设 $\Omega$ 有 $C^1$ 边界。存在有界线性算子
$$T: W^{1,p}(\Omega) \to L^p(\partial\Omega)$$
使得 $Tu = u|_{\partial\Omega}$ 对 $u \in C(\overline{\Omega})$，且
$$\|Tu\|_{L^p(\partial\Omega)} \leq C\|u\|_{W^{1,p}(\Omega)}$$

### 6.2 迹的核

**定理**：$\ker T = W_0^{1,p}(\Omega)$。即 $W_0^{1,p}$ 恰为边界迹为零的 $W^{1,p}$ 函数。

### 6.3 高阶迹

对 $W^{k,p}(\Omega)$，可定义直到 $k-1$ 阶的法向导数迹：
$$T_j: W^{k,p}(\Omega) \to W^{k-j-1/p,p}(\partial\Omega), \quad j = 0, \dots, k-1$$
其中右侧为Sobolev-Slobodeckij空间（分数阶Sobolev空间）。

---

## 7. Poincaré不等式

### 7.1 标准形式

**定理（Poincaré不等式）**：设 $\Omega$ 有界。存在 $C = C(\Omega)$ 使得
$$\|u\|_{L^p(\Omega)} \leq C\|\nabla u\|_{L^p(\Omega)}, \quad \forall u \in W_0^{1,p}(\Omega)$$

*证明*（一维情形）：对 $u \in C_c^\infty(0,L)$，$u(x) = \int_0^x u'(t)dt$，由Hölder
$$|u(x)| \leq x^{1-1/p} \|u'\|_{L^p}$$
积分得 $\|u\|_{L^p} \leq C\|u'\|_{L^p}$。$\square$

### 7.2 Poincaré-Wirtinger

**定理**：对连通有界Lipschitz域，
$$\|u - \bar{u}\|_{L^p} \leq C\|\nabla u\|_{L^p}, \quad \bar{u} = \frac{1}{|\Omega|}\int_\Omega u$$

这是Neumann问题强制性的来源。

---

## 8. 小结

弱导数与Sobolev空间是现代PDE理论的基石。通过将微分运算从点态推广到积分意义，Sobolev空间包含了足够广泛的函数类以容纳PDE的解，同时保留了良好的分析性质（完备性、逼近、延拓、迹）。Poincaré不等式与迹定理为边值问题的变分表述提供了关键工具，而Meyers-Serrin逼近定理则架起了经典分析与广义函数之间的桥梁。没有Sobolev空间，Lax-Milgram定理、椭圆正则性与现代非线性PDE理论都将无从立足。
