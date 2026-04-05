---
title: "05 变分法与Euler–Lagrange方程"
msc_primary: "49J10"
msc_secondary: ['35A15', '49K20', '58E05']
processed_at: '2026-04-05'
---
# 05 变分法与Euler–Lagrange方程 / Calculus of Variations and Euler–Lagrange Equations

**主题编号**: B.03.06.05  
**创建日期**: 2026年4月3日  
**最后更新**: 2026年4月3日  
**MSC分类**: 49J10 (变分法中的存在性理论), 35A15 (变分方法), 49K20 (高阶必要条件), 58E05 (抽象临界点理论)  
**国际对齐**: Evans *PDE* Chapter 8; Dacorogna *Introduction to the Calculus of Variations*; Giaquinta *Multiple Integrals in the Calculus of Variations*; Princeton MAT 218

---

## 目录 / Table of Contents

- [1 引言 / Introduction](#1-引言-introduction)
- [2 经典变分法：Euler–Lagrange方程](#2-经典变分法eulerlagrange方程)
  - [2.1 第一变分与EL方程](#21-第一变分与el方程)
  - [2.2 自然边界条件](#22-自然边界条件)
  - [2.3 等周问题与Lagrange乘子](#23-等周问题与lagrange乘子)
- [3 直接法与下半连续性](#3-直接法与下半连续性)
  - [3.1 Tonelli直接法](#31-tonelli直接法)
  - [3.2 凸性与弱下半连续性](#32-凸性与弱下半连续性)
  - [3.3 极小化序列与弱收敛](#33-极小化序列与弱收敛)
- [4 二阶变分与正则性](#4-二阶变分与正则性)
  - [4.1 Legendre–Hadamard条件](#41-legendrehadamard条件)
  - [4.2 Jacobi方程与共轭点](#42-jacobi方程与共轭点)
  - [4.3 极小解的内部正则性](#43-极小解的内部正则性)
- [5 现代变分法与几何应用](#5-现代变分法与几何应用)
  - [5.1 调和映射](#51-调和映射)
  - [5.2 极小曲面与Plateau问题](#52-极小曲面与plateau问题)
  - [5.3 Mountain Pass定理](#53-mountain-pass定理)
- [6 例子 / Examples](#6-例子-examples)
- [7 参考文献 / References](#7-参考文献-references)

---

## 1 引言 / Introduction

变分法的历史可以追溯到1696年Johann Bernoulli提出的最速降线问题（brachistochrone problem）：求连接两点的曲线，使得质点在重力作用下沿之滑下所需时间最短。Euler和Lagrange在18世纪中叶系统发展了这一领域，建立了寻找泛函极值的必要条件——Euler–Lagrange方程。19世纪，Dirichlet原理将Laplace方程的边值问题与能量泛函的极小化联系起来，尽管Weierstrass后来指出其严格性缺陷，但这一思想在20世纪由Hilbert、Tonelli等人完善，催生了现代直接法（direct method）。

今天，变分法不仅是经典力学和几何光学的基础，更是偏微分方程、微分几何、控制论和材料科学的核心工具。从调和映射到Yang–Mills方程，从极小曲面到 mountain pass 临界点理论，变分思想无处不在。本文将从Euler–Lagrange方程的经典推导出发，深入讨论直接法、二阶变分、正则性理论以及现代几何应用，内容对齐Evans《PDE》第8章和Dacorogna的经典教材。

---

## 2 经典变分法：Euler–Lagrange方程

### 2.1 第一变分与EL方程

考虑泛函

$$
J(u) = \int_\Omega F(x, u, \nabla u) \, dx,
$$

其中 $\Omega \subset \mathbb{R}^n$ 为有界区域，$F: \Omega \times \mathbb{R} \times \mathbb{R}^n \to \mathbb{R}$ 为光滑的Lagrange函数，$u: \Omega \to \mathbb{R}$ 满足边界条件 $u|_{\partial\Omega} = g$。

**定理 2.1** (Euler–Lagrange方程)  
若 $u \in C^2(\overline{\Omega})$ 是 $J$ 的极小点（或更一般地，临界点），则 $u$ 满足：

$$
-\sum_{i=1}^n \frac{\partial}{\partial x_i} \Bigl( \frac{\partial F}{\partial p_i}(x, u, \nabla u) \Bigr) + \frac{\partial F}{\partial z}(x, u, \nabla u) = 0 \quad \text{在 } \Omega \text{ 内}.
$$

其中 $p = (p_1, \dots, p_n)$ 表示 $\nabla u$ 的占位变量，$z$ 表示 $u$ 的占位变量。

*证明思路*：对任意 $\phi \in C_c^\infty(\Omega)$，考虑单参数变分 $u_\varepsilon = u + \varepsilon \phi$。由于 $u$ 是临界点，$\frac{d}{d\varepsilon} J(u_\varepsilon)|_{\varepsilon=0} = 0$。计算得：

$$
\int_\Omega \Bigl( F_z \phi + \sum_i F_{p_i} \phi_{x_i} \Bigr) dx = 0.
$$

分部积分并利用 $\phi$ 的任意性，即得EL方程。

**例 2.1** (Dirichlet积分)  
$F(p) = |p|^2/2$，则 $F_{p_i} = p_i$，$F_z = 0$。EL方程为 $-\Delta u = 0$，即Laplace方程。

**例 2.2** ($p$-Dirichlet能量)  
$F(p) = |p|^p/p$（$1 < p < \infty$），则EL方程为 $-\Delta_p u = -\operatorname{div}(|\nabla u|^{p-2} \nabla u) = 0$，即 $p$-Laplace方程。

### 2.2 自然边界条件

若变分问题不固定边界值，则极小点除满足EL方程外，还需满足 **自然边界条件**。

**定理 2.2** (自然边界条件)  
设 $u$ 在自由边界问题中极小化 $J(u)$，则

$$
\sum_{i=1}^n F_{p_i}(x, u, \nabla u) \, \nu_i = 0 \quad \text{在 } \partial\Omega \text{ 上},
$$

其中 $\nu = (\nu_1, \dots, \nu_n)$ 为外法向。

对Dirichlet积分，这退化为Neumann边界条件 $\partial u / \partial \nu = 0$。

### 2.3 等周问题与Lagrange乘子

**等周问题**：在所有固定长度的闭曲线中，求围成最大面积的曲线。抽象化后，问题变为在约束 $K(u) = c$ 下极小化 $J(u)$。

**定理 2.3** (Lagrange乘子法则)  
设 $u$ 是 $J$ 在约束 $K(u) = c$ 下的极值点，且 $K$ 在 $u$ 处的变分非退化。则存在 $\lambda \in \mathbb{R}$ 使得

$$
\delta J(u) = \lambda \, \delta K(u).
$$

*应用*：在平面上，固定周长 $L$ 求最大面积，得到圆。EL方程结合约束给出曲率为常数，即圆。

---

## 3 直接法与下半连续性

经典变分法假设解具有 $C^2$ 光滑性，但许多物理和几何问题并不保证这一点。Tonelli在20世纪初提出的 **直接法** 将问题放在Sobolev空间中，利用泛函分析的紧性工具来证明极小点的存在。

### 3.1 Tonelli直接法

**定理 3.1** (Tonelli直接法)  
设 $X$ 为自反Banach空间（如 $W^{1,p}(\Omega)$），$J: X \to \mathbb{R} \cup \{+\infty\}$ 满足：

1. **强制性**（coercivity）：$J(u) \to +\infty$ 当 $\|u\|_X \to \infty$；

2. **弱下半连续性**（weak lower semicontinuity）：若 $u_k \rightharpoonup u$ 弱收敛，则 $J(u) \le \varliminf J(u_k)$。

则 $J$ 在 $X$ 上达到下确界。

*证明思路*：
1. 取极小化序列 $u_k$ 使得 $J(u_k) \to \inf J$。
2. 由强制性，$\{u_k\}$ 在 $X$ 中有界。
3. 自反空间中闭单位球弱紧（Eberlein–Šmulian），故存在弱收敛子列 $u_{k_j} \rightharpoonup u$。
4. 由弱下半连续性，$J(u) \le \varliminf J(u_{k_j}) = \inf J$，故 $u$ 是极小点。

### 3.2 凸性与弱下半连续性

对于积分泛函 $J(u) = \int_\Omega F(x, u, \nabla u) dx$，弱下半连续性与Lagrange函数 $F$ 的凸性密切相关。

**定理 3.2** (弱下半连续的Ioffe定理 / 凸性判据)  
设 $F(x, z, p)$ 对 $(z, p)$ 是Carathéodory的，且对 $p$ 是 **凸的**。则 $J$ 在 $W^{1,p}(\Omega)$ 的弱拓扑下是下半连续的。

*证明思路*：凸泛函在有限维空间中是下半连续的；通过局部化、Fatou引理和凸分析的标准技巧，可将其推广到Sobolev空间的弱拓扑。

**关键点**：若 $F$ 对 $p$ 非凸，则极小点可能不存在，或解可能出现微结构（microstructure），这在材料科学中的变分模型中极为常见。

### 3.3 极小化序列与弱收敛

**例 3.1** (Dirichlet原理的严格化)  
设 $J(u) = \frac{1}{2} \int_\Omega |\nabla u|^2 dx$，$u \in H_0^1(\Omega)$。$J$ 是凸的、强制的。取极小化序列 $u_k$，其在 $H_0^1$ 中有界，从而弱收敛子列 $u_k \rightharpoonup u$。由凸性，$J(u) \le \varliminf J(u_k)$，故 $u$ 是唯一的极小点，满足 $-\Delta u = 0$。

**注意**：弱收敛一般不能保持范数。例如，在 $H_0^1(0,1)$ 中，$u_k(x) = \sin(k\pi x)/k$ 弱收敛到0，但 $J(u_k) = \frac{\pi^2}{4} \not\to 0 = J(0)$。不过在这个特例中极小化序列并不趋于0，因为边界条件固定了非零趋势。

---

## 4 二阶变分与正则性

### 4.1 Legendre–Hadamard条件

对泛函 $J(u) = \int_\Omega F(\nabla u) dx$（为了简化，设 $F$ 只依赖于 $p$），其二阶变分为：

$$
\delta^2 J(u)[\phi, \phi] = \int_\Omega \sum_{i,j} F_{p_i p_j}(\nabla u) \, \phi_{x_i} \phi_{x_j} \, dx.
$$

**定理 4.1** (Legendre–Hadamard必要条件)  
若 $u$ 是 $J$ 的局部极小点，则对任意 $\xi \in \mathbb{R}^n$，$\eta \in \mathbb{R}$（或对向量值情形 $\eta \in \mathbb{R}^m$）：

$$
\sum_{i,j} F_{p_i p_j}(\nabla u) \, \xi_i \xi_j \, \eta^2 \ge 0.
$$

这称为 **Legendre–Hadamard椭圆性条件**。它是保证EL方程为椭圆型方程的变分来源。

若不等式严格成立（对非零 $\xi, \eta$），则称 $F$ 满足 **强Legendre–Hadamard条件**。

### 4.2 Jacobi方程与共轭点

**定义 4.1** (Jacobi算子)  
设 $u$ 满足EL方程。其 **Jacobi算子** $L$ 定义为二阶变分的Euler–Lagrange算子：

$$
L\phi = -\sum_{i,j} \frac{\partial}{\partial x_i} \Bigl( F_{p_i p_j}(\nabla u) \frac{\partial \phi}{\partial x_j} \Bigr) + \cdots.
$$

在一维情形，$L\phi = -(a(x) \phi')' + c(x) \phi = 0$ 称为 **Jacobi方程**。

**定义 4.2** (共轭点)  
若存在非平凡解 $\phi$ 使得 $\phi(x_0) = \phi(x_1) = 0$，则称 $x_1$ 为 $x_0$ 的 **共轭点**。经典结果表明：若极值曲线在 $[x_0, x_1]$ 内无共轭点，则它是局部极小点。

### 4.3 极小解的内部正则性

**定理 4.2** (De Giorgi–Nash关于变分极小)  
设 $F(p)$ 满足强Legendre–Hadamard条件，$u \in H^1(\Omega)$ 是 $J$ 的局部极小点。则 $u \in C^{0,\gamma}_{\text{loc}}(\Omega)$ 对某个 $\gamma > 0$。

**定理 4.3** (Schauder型正则性)  
若进一步 $F \in C^{2,\alpha}$，则 $u \in C^{1,\alpha}_{\text{loc}}(\Omega)$。

**定理 4.4** (极小曲面的解析性)  
对面积泛函 $F(p) = \sqrt{1 + |p|^2}$，极小曲面方程的解实际上是 **实解析的**（$C^\omega$）。这是更高阶正则性的特例。

---

## 5 现代变分法与几何应用

### 5.1 调和映射

**定义 5.1** (调和映射)  
设 $M, N$ 为Riemann流形。映射 $u: M \to N$ 称为 **调和映射**，若它是能量泛函

$$
E(u) = \frac{1}{2} \int_M |du|^2 \, dV_M

$$

的临界点。其EL方程为 **调和映射方程**（tension field 消失）：

$$
\tau(u) = \Delta u + A(u)(\nabla u, \nabla u) = 0,
$$

其中 $A$ 为 $N$ 的第二基本形式。

**定理 5.1** (Eells–Sampson)  
若目标流形 $N$ 的截面曲率非正，则任意光滑映射 $u_0: M \to N$ 都同伦于一个调和映射。

### 5.2 极小曲面与Plateau问题

**Plateau问题**：给定 $\mathbb{R}^3$ 中的一条闭曲线 $\Gamma$，求以 $\Gamma$ 为边界的面积最小的曲面。

**定理 5.2** (Douglas–Rado, 1930s)  
对任意Jordan曲线 $\Gamma$，Plateau问题存在解，且解是平均曲率为零的曲面（即极小曲面）。

现代方法利用 **几何测度论**（geometric measure theory）和 ** currents** 来证明高维Plateau问题的存在性（Federer–Fleming, Almgren）。

### 5.3 Mountain Pass定理

并非所有变分问题的能量泛函都有全局最小值。在某些情况下，鞍点型临界点对应于物理上不稳定的平衡态或过渡态。

**定理 5.3** (Ambrosetti–Rabinowitz Mountain Pass)  
设 $X$ 为Banach空间，$J \in C^1(X, \mathbb{R})$ 满足：

1. $J(0) = 0$，且存在 $r, \alpha > 0$ 使得 $J|_{\partial B_r} \ge \alpha$；
2. 存在 $e \in X$ 且 $\|e\| > r$ 使得 $J(e) \le 0$。

定义 mountain pass 水平

$$
c = \inf_{\gamma \in \Gamma} \max_{t \in [0,1]} J(\gamma(t)),
$$

其中 $\Gamma = \{ \gamma \in C([0,1], X) : \gamma(0) = 0, \gamma(1) = e \}$。若 $J$ 满足Palais–Smale条件，则 $c \ge \alpha$ 是 $J$ 的一个临界点值。

这一定理在寻找半线性椭圆方程的非平凡解时极为有用，如 $-\Delta u = u^p - u$ 在 $H_0^1$ 中的非零解。

---

## 6 例子 / Examples

**例 6.1** (最速降线问题)  
求连接 $(0,0)$ 与 $(a,b)$（$b>0$）的曲线 $y(x)$，使质点在重力 $g$ 下从静止滑下的时间最短。时间泛函为

$$
T(y) = \int_0^a \sqrt{\frac{1 + (y')^2}{2gy}} \, dx.
$$

Euler–Lagrange方程可积分为参数形式的摆线（cycloid）：

$$
x(\theta) = r(\theta - \sin\theta), \quad y(\theta) = r(1 - \cos\theta).
$$

这是变分法历史上第一个被完全解决的经典问题，展示了EL方程将几何优化问题转化为微分方程的强大能力。

**例 6.2** (肥皂膜/悬链面)  
将两个平行的圆环浸入肥皂水中，取出的肥皂膜形状由面积泛函极小化决定。若两个圆环距离较近，解是 **悬链面**（catenoid），即悬链线绕轴旋转得到的曲面。若距离超过某一临界值，悬链面不稳定，极小解“爆破”为两个分离的圆盘（disk）。这是变分问题中 **非唯一性** 和 **鞍点失稳** 的经典演示。

**例 6.3** (Mountain Pass在半线性方程中的应用)  
考虑

$$
\begin{cases}
-\Delta u = u^3 - u & \text{in } \Omega, \\
u = 0 & \text{on } \partial\Omega.
\end{cases}
$$

能量泛函 $J(u) = \frac{1}{2} \int |\nabla u|^2 + \frac{1}{4} \int u^4 - \frac{1}{2} \int u^2$ 在 $H_0^1(\Omega)$ 上。显然 $u=0$ 是一个平凡解，且是局部极小点。取足够大的 $e = t \phi_1$（$\phi_1$ 为正主特征函数），则 $J(e) < 0$。由Mountain Pass定理，存在非零临界点 $u \neq 0$，对应方程的非平凡解。

---

## 7 参考文献 / References

### 经典教材

1. **Evans, L. C.** (2010). *Partial Differential Equations* (2nd ed.). AMS. Chapter 8.
2. **Dacorogna, B.** (2008). *Introduction to the Calculus of Variations* (3rd ed.). Imperial College Press.
3. **Giaquinta, M.** (1983). *Multiple Integrals in the Calculus of Variations and Nonlinear Elliptic Systems*. Princeton.
4. **Struwe, M.** (2008). *Variational Methods* (4th ed.). Springer.

### 进阶文献

5. **Jost, J., & Li-Jost, X.** (1998). *Calculus of Variations*. Cambridge.
6. **Ambrosetti, A., & Rabinowitz, P. H.** (1973). Dual variational methods in critical point theory and applications. *J. Funct. Anal.* 14, 349–381.
7. **Morse, M.** (1934). *The Calculus of Variations in the Large*. AMS Colloquium Publications.
8. **Nitsche, J. C. C.** (1989). *Lectures on Minimal Surfaces*. Cambridge.

### 中文参考

9. **张恭庆** (2011). *临界点理论及其应用*. 上海科学技术出版社.
10. **陆文端** (2003). *微分方程中的变分方法*（修订版）. 清华大学出版社.

---

**文档状态**: 完成  
**字数**: 约5,800字  
**数学公式数**: 35+  
**例子数**: 3  
**最后更新**: 2026年4月3日
