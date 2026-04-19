---
title: Poisson方程-边值问题
description: 系统介绍Poisson方程的Dirichlet问题、Neumann问题、Robin问题、Poincaré不等式、Lax-Milgram定理应用，以及弱解的存在性、唯一性与正则性理论。
msc_primary:
  - 35J05
msc_secondary:
  - 35J25
  - 35A01
  - 35D30
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
    - id: gilbarg_trudinger
      type: textbook
      title: Elliptic Partial Differential Equations of Second Order
      authors:
        - David Gilbarg
        - Neil S. Trudinger
      publisher: Springer
      year: 2001
      msc: 35-02
---

# Poisson方程-边值问题

**从Dirichlet到Robin — 椭圆边值问题的变分框架**

---

## 1. 边值问题的分类

### 1.1 三类经典边值问题

设 $\Omega \subset \mathbb{R}^n$ 为有界光滑区域，考虑Poisson方程
$$-\Delta u = f \quad \text{in } \Omega$$

**第一类：Dirichlet问题**
$$u = g \quad \text{on } \partial\Omega$$
（给定边界上的函数值）

**第二类：Neumann问题**
$$\frac{\partial u}{\partial \nu} = g \quad \text{on } \partial\Omega$$
（给定边界上的法向导数/通量）

**第三类：Robin问题**
$$\frac{\partial u}{\partial \nu} + \alpha u = g \quad \text{on } \partial\Omega, \quad \alpha > 0$$
（混合边界条件，描述边界上的对流热损失等）

---

## 2. Dirichlet问题

### 2.1 变分表述

对 $g = 0$（齐次Dirichlet），定义Hilbert空间 $H_0^1(\Omega)$（Sobolev空间，见后续章节）及双线性型
$$a(u,v) = \int_\Omega \nabla u \cdot \nabla v \, dx$$
线性泛函
$$L(v) = \int_\Omega f v \, dx$$

**变分问题**：求 $u \in H_0^1(\Omega)$ 使得
$$a(u,v) = L(v), \quad \forall v \in H_0^1(\Omega)$$

### 2.2 Lax-Milgram定理

**定理（Lax-Milgram）**：设 $H$ 为Hilbert空间，$a: H \times H \to \mathbb{R}$ 为连续、强制的双线性型（即 $|a(u,v)| \leq C\|u\|\|v\|$，$a(u,u) \geq \alpha\|u\|^2$），$L \in H^*$。则存在唯一的 $u \in H$ 使得 $a(u,v) = L(v)$ 对所有 $v \in H$，且 $\|u\| \leq \frac{1}{\alpha}\|L\|$。

对 $a(u,v) = \int_\Omega \nabla u \cdot \nabla v$，由Poincaré不等式强制：
$$a(u,u) = \int_\Omega |\nabla u|^2 \geq C\|u\|_{H^1}^2$$

**定理**：齐次Dirichlet问题对任意 $f \in H^{-1}(\Omega)$ 存在唯一弱解 $u \in H_0^1(\Omega)$。

### 2.3 非齐次Dirichlet

对 $u = g$ 在 $\partial\Omega$，设 $g$ 可延拓为 $\tilde{g} \in H^1(\Omega)$。令 $w = u - \tilde{g}$，则 $w \in H_0^1(\Omega)$ 满足
$$-\Delta w = f + \Delta \tilde{g}$$
化为齐次情形。

---

## 3. Neumann问题

### 3.1 相容性条件

Neumann问题 $-\Delta u = f$，$\partial_\nu u = g$ 有解的必要条件：由Green第一恒等式，
$$\int_\Omega f \, dx = -\int_\Omega \Delta u \, dx = -\int_{\partial\Omega} \partial_\nu u \, dS = -\int_{\partial\Omega} g \, dS$$
即
$$\int_\Omega f \, dx + \int_{\partial\Omega} g \, dS = 0$$

### 3.2 解的唯一性

若 $u$ 为解，则 $u + C$（任意常数）也是解。故解在相差常数意义下唯一。

### 3.3 变分表述

在商空间 $H^1(\Omega)/\mathbb{R}$（模常数）上，双线性型 $a(u,v) = \int_\Omega \nabla u \cdot \nabla v$ 由Poincaré-Wirtinger不等式强制：
$$\int_\Omega |\nabla u|^2 \geq C \int_\Omega (u - \bar{u})^2$$
其中 $\bar{u} = \frac{1}{|\Omega|}\int_\Omega u$ 为平均值。

**定理**：在相容性条件下，Neumann问题在 $H^1(\Omega)/\mathbb{R}$ 中存在唯一解。

---

## 4. Robin问题

### 4.1 变分框架

Robin问题自动满足唯一性（无需模常数）。双线性型
$$a(u,v) = \int_\Omega \nabla u \cdot \nabla v \, dx + \alpha \int_{\partial\Omega} u v \, dS$$
在 $H^1(\Omega)$ 上强制（由迹不等式与Poincaré不等式）。

**定理**：Robin问题对任意 $f \in L^2(\Omega)$，$g \in L^2(\partial\Omega)$ 存在唯一弱解 $u \in H^1(\Omega)$。

---

## 5. 正则性理论

### 5.1 内部正则性

**定理（Weyl引理/内部正则性）**：设 $u$ 为 $-\Delta u = f$ 的弱解。若 $f \in H^k(\Omega)$，则 $u \in H^{k+2}_{\text{loc}}(\Omega)$。特别地，若 $f \in C^\infty(\Omega)$，则 $u \in C^\infty(\Omega)$。

### 5.2 边界正则性

**定理（全局椭圆正则性）**：设 $\Omega$ 为 $C^{k+2}$ 区域。若 $f \in H^k(\Omega)$，$g \in H^{k+3/2}(\partial\Omega)$，则Dirichlet问题的解 $u \in H^{k+2}(\Omega)$。

特别地，$f \in C^\infty(\overline{\Omega})$，$g \in C^\infty(\partial\Omega)$，$\partial\Omega$ 光滑，则 $u \in C^\infty(\overline{\Omega})$。

### 5.3 Schauder估计

对Hölder连续数据，有**Schauder估计**：
$$\|u\|_{C^{2,\alpha}(\overline{\Omega})} \leq C(\|f\|_{C^\alpha(\overline{\Omega})} + \|g\|_{C^{2,\alpha}(\partial\Omega)} + \|u\|_{C^0(\overline{\Omega})})$$

---

## 6. 特征值问题

### 6.1 Laplace算子的谱

**定理**：$-\Delta$ 在 $H_0^1(\Omega)$ 上有离散谱
$$0 < \lambda_1 \leq \lambda_2 \leq \dots \to \infty$$
对应标准正交特征函数 $\{\phi_k\} \subset L^2(\Omega)$。

**变分刻画**：
$$\lambda_1 = \inf_{u \in H_0^1(\Omega), u \neq 0} \frac{\int_\Omega |\nabla u|^2}{\int_\Omega u^2}$$

**例1（区间）**：$\Omega = (0,\pi)$，$\lambda_k = k^2$，$\phi_k(x) = \sin(kx)$。

**例2（圆盘）**：$\Omega = B(0,R) \subset \mathbb{R}^2$，$\lambda$ 由Bessel函数 $J_n(\sqrt{\lambda}R) = 0$ 的根给出。

### 6.2 谱分解

Dirichlet问题的解可形式展开为
$$u = \sum_{k=1}^\infty \frac{\langle f, \phi_k \rangle}{\lambda_k} \phi_k$$

---

## 7. 小结

Poisson方程的三类边值问题各有其变分框架与适定性特征：Dirichlet问题由强制性与Poincaré不等式保证唯一可解性；Neumann问题需要相容性条件且解在相差常数下唯一；Robin问题则自动适定。正则性理论揭示了椭圆方程的磨光性质：弱解在内部自动提升光滑性，在光滑边界上整体正则。特征值问题将椭圆算子与泛函分析相联结，为分离变量法、热方程与波动方程的长时间行为提供了谱分解工具。Lax-Milgram定理是这一整套理论的基石，将PDE的存在性转化为抽象的Hilbert空间问题，是现代偏微分方程理论中最优雅也最有力的成果之一。
