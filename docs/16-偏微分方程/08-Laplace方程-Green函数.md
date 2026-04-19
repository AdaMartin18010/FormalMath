---
title: Laplace方程-Green函数
description: 系统介绍Green函数的定义与性质、对称性与正性、球与半空间上的显式公式、Dirichlet问题的表示公式，以及Neumann-Green函数与边界积分方程。
msc_primary:
  - 35J05
msc_secondary:
  - 31B10
  - 31B25
  - 35A08
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

# Laplace方程-Green函数

## 引言

Green函数是偏微分方程理论中最具统一性的概念之一。它将椭圆边值问题的求解转化为一个核函数的构造与积分，不仅适用于Laplace方程，也推广到热方程、波动方程乃至更一般的椭圆算子。从物理上看，Green函数代表了点源在特定边界条件下的响应；从数学上看，它是偏微分算子在函数空间中的广义逆。Green函数的方法论——以基本解为出发点、通过镜像法或本征函数展开满足边界条件——贯穿了经典分析与现代PDE理论。

本教程从Green函数的严格定义出发，证明其对称性与正性，建立Dirichlet问题的积分表示公式，推导球与半空间上的显式表达式，并分析边界积分方程的数学基础。

---

## 1. Green函数的定义与存在性

### 1.1 基本解

回顾Laplace方程的基本解。对 $n \geq 3$：
$$\Phi(x) = \frac{1}{n(2-n)\omega_n} |x|^{2-n} = \frac{1}{(2-n)\omega_n} |x|^{2-n},$$
其中 $\omega_n = 2\pi^{n/2}/\Gamma(n/2)$ 为单位球面面积。对 $n=2$：
$$\Phi(x) = -\frac{1}{2\pi} \log |x|.$$

**定理 1.1**。在分布意义下，$-\Delta \Phi = \delta_0$（Dirac delta函数）。

**证明**：对 $n \geq 3$，$\Phi$ 在 $\mathbb{R}^n \setminus \{0\}$ 上调和。对检验函数 $\varphi \in C_c^\infty(\mathbb{R}^n)$，
$$\langle -\Delta\Phi, \varphi \rangle = \int_{\mathbb{R}^n} \Phi(-\Delta\varphi) = \lim_{\varepsilon \to 0} \int_{|x|>\varepsilon} \Phi(-\Delta\varphi).$$
分部积分两次，利用 $\Delta\Phi = 0$ 于 $|x|>\varepsilon$：
$$= \lim_{\varepsilon \to 0} \int_{|x|=\varepsilon} \left( \Phi \frac{\partial\varphi}{\partial\nu} - \frac{\partial\Phi}{\partial\nu} \varphi \right) dS.$$
在 $|x|=\varepsilon$ 上，$\Phi = O(\varepsilon^{2-n})$，$\partial\Phi/\partial\nu = (2-n)^{-1}\omega_n^{-1} (2-n)\varepsilon^{1-n} = \omega_n^{-1}\varepsilon^{1-n}$。第一项面积分为 $O(\varepsilon^{2-n}) \cdot O(1) \cdot \varepsilon^{n-1} = O(\varepsilon) \to 0$；第二项为
$$-\omega_n^{-1}\varepsilon^{1-n} \cdot \omega_n \varepsilon^{n-1} \cdot \varphi(0) + o(1) = -\varphi(0).$$
故 $\langle -\Delta\Phi, \varphi \rangle = \varphi(0) = \langle \delta_0, \varphi \rangle$。∎

### 1.2 Green函数的定义

设 $\Omega \subset \mathbb{R}^n$ 为具有 $C^1$ 边界的有界区域。

**定义 1.1（Dirichlet-Green函数）**。$\Omega$ 的 **Dirichlet-Green函数** 是函数 $G: \overline{\Omega} \times \overline{\Omega} \setminus \{(x,x)\} \to \mathbb{R}$，对固定 $x \in \Omega$，$G(x,\cdot)$ 满足
$$\begin{cases} -\Delta_y G(x,y) = \delta_x(y) & \text{在 } \Omega \text{ 内（分布意义）}, \\ G(x,y) = 0 & y \in \partial\Omega. \end{cases}$$

等价地，$G$ 可分解为
$$G(x,y) = \Phi(x-y) - \phi^x(y),$$
其中 **校正函数** $\phi^x(y)$ 满足
$$\begin{cases} \Delta_y \phi^x = 0 & \text{在 } \Omega \text{ 内}, \\ \phi^x(y) = \Phi(x-y) & y \in \partial\Omega. \end{cases}$$

**定理 1.2（存在性）**。对任意有界区域 $\Omega$ 及 $x \in \Omega$，Dirichlet问题 (1.2) 存在唯一解 $\phi^x \in C^2(\Omega) \cap C(\overline{\Omega})$。故Green函数 $G(x,y)$ 唯一存在。

**证明**：由Perron方法或直接应用Dirichlet问题解的存在唯一性定理（对连续边界数据 $\Phi(x-\cdot)|_{\partial\Omega}$）。∎

---

## 2. Green函数的性质

### 2.1 对称性

**定理 2.1**。$G(x,y) = G(y,x)$ 对所有 $x \neq y \in \Omega$。

**证明**：固定 $x_1 \neq x_2$。令 $u(y) = G(x_1,y)$，$v(y) = G(x_2,y)$。对充分小的 $\varepsilon$，在 $\Omega_\varepsilon = \Omega \setminus (B(x_1,\varepsilon) \cup B(x_2,\varepsilon))$ 上，$u, v$ 均为调和函数。Green第二恒等式给出
$$\int_{\Omega_\varepsilon} (u\Delta v - v\Delta u) = \int_{\partial\Omega_\varepsilon} \left( u \frac{\partial v}{\partial\nu} - v \frac{\partial u}{\partial\nu} \right) dS.$$
左端为零。右端边界 $\partial\Omega_\varepsilon = \partial\Omega \cup \partial B(x_1,\varepsilon) \cup \partial B(x_2,\varepsilon)$。在 $\partial\Omega$ 上，$u=v=0$，贡献为零。

在 $\partial B(x_1,\varepsilon)$ 上，$v$ 光滑，$u(y) \sim \Phi(x_1-y)$。计算：
$$\int_{\partial B(x_1,\varepsilon)} u \frac{\partial v}{\partial\nu} \to 0 \quad (\varepsilon \to 0),$$
因 $u = O(\varepsilon^{2-n})$，面积 $= O(\varepsilon^{n-1})$。而
$$-\int_{\partial B(x_1,\varepsilon)} v \frac{\partial u}{\partial\nu} \to -v(x_1) \cdot (-1) = v(x_1) = G(x_2, x_1),$$
由基本解的法向导数在球面上的积分性质。

同理，$\partial B(x_2,\varepsilon)$ 贡献 $-u(x_2) = -G(x_1, x_2)$。总和为零给出 $G(x_2, x_1) - G(x_1, x_2) = 0$。∎

### 2.2 正性与比较原理

**定理 2.2**。$G(x,y) > 0$ 对所有 $x, y \in \Omega$，$x \neq y$。

**证明**：固定 $x$。函数 $G(x,\cdot)$ 在 $\Omega \setminus \{x\}$ 上调和，在 $\partial\Omega$ 上为零，且在 $y=x$ 附近 $G(x,y) \sim \Phi(x-y) > 0$（对 $n \geq 3$；$n=2$ 时 $-\log|x-y| > 0$ 对充分小的 $|x-y|$）。由强最大值原理，$G(x,\cdot)$ 不能在内部取非正最小值（因边界已为零且 $x$ 处趋向 $+\infty$）。故 $G(x,y) > 0$。∎

---

## 3. Dirichlet问题的表示公式

### 3.1 Green表示定理

**定理 3.1**。设 $u \in C^2(\overline{\Omega})$。则对 $x \in \Omega$，
$$u(x) = \int_\Omega G(x,y) (-\Delta u)(y) \, dy - \int_{\partial\Omega} \frac{\partial G}{\partial \nu_y}(x,y) u(y) \, dS_y. \tag{GR}$$

**证明**：对 $u$ 和 $v(y) = G(x,y)$ 在 $\Omega_\varepsilon = \Omega \setminus B(x,\varepsilon)$ 上应用Green第二恒等式。左端：
$$\int_{\Omega_\varepsilon} (u\Delta v - v\Delta u) = -\int_{\Omega_\varepsilon} G(x,y) \Delta u(y) \, dy.$$
右端：$\partial\Omega$ 上 $v=0$，贡献为 $-\int_{\partial\Omega} u \partial G/\partial\nu$；$\partial B(x,\varepsilon)$ 上计算得 $u(x)$（类似定理2.1的证明）。令 $\varepsilon \to 0$ 即得。∎

### 3.2 Poisson核与Poisson积分公式

**定义 3.1（Poisson核）**。对 $x \in \Omega$，$y \in \partial\Omega$，定义
$$K(x,y) := -\frac{\partial G}{\partial \nu_y}(x,y).$$

由定理2.2和Hopf边界点引理，$K(x,y) > 0$。

**推论 3.1**。若 $u$ 在 $\Omega$ 上调和（$\Delta u = 0$）且 $u \in C(\overline{\Omega})$，则
$$u(x) = \int_{\partial\Omega} K(x,y) u(y) \, dS_y. \tag{PI}$$

**定理 3.2**。Poisson核满足
$$\int_{\partial\Omega} K(x,y) \, dS_y = 1 \quad \forall x \in \Omega.$$

**证明**：对 $u \equiv 1$ 应用 (PI)。∎

---

## 4. 显式Green函数

### 4.1 上半空间 $\mathbb{R}^n_+$

设 $\Omega = \mathbb{R}^n_+ = \{x = (x', x_n) : x_n > 0\}$。对 $x \in \mathbb{R}^n_+$，定义关于边界 $\{x_n = 0\}$ 的 **镜像点**
$$\tilde{x} = (x', -x_n).$$

**定理 4.1**。上半空间的Green函数为
$$G(x,y) = \Phi(y-x) - \Phi(y-\tilde{x}), \quad y \in \mathbb{R}^n_+.$$

**证明**：$\Phi(y-\tilde{x})$ 在 $y_n > 0$ 上调和（奇点 $y=\tilde{x}$ 位于 $y_n < 0$）。当 $y_n = 0$ 时，$|y-x| = |y-\tilde{x}|$，故 $G(x,y) = 0$。∎

**Poisson核**：对 $y = (y', 0) \in \partial\mathbb{R}^n_+$，
$$K(x,y) = \frac{2x_n}{\omega_n |x-y|^n}.$$

**Dirichlet问题的解**：
$$u(x) = \frac{2x_n}{\omega_n} \int_{\mathbb{R}^{n-1}} \frac{g(y')}{(|x'-y'|^2 + x_n^2)^{n/2}} \, dy'.$$

对 $n=2$：$K(x,y) = \frac{1}{\pi} \frac{x_2}{(x_1-y)^2 + x_2^2}$，即Cauchy分布密度。

### 4.2 球 $B(0,R)$

设 $\Omega = B(0,R) \subset \mathbb{R}^n$。对 $x \neq 0$，定义关于球面 $|y|=R$ 的 **反演点**
$$x^* = \frac{R^2}{|x|^2} x, \quad |x^*| > R.$$

**定理 4.2**。球的Green函数为（$n \geq 3$）
$$G(x,y) = \Phi(y-x) - \Phi\left(\frac{|x|}{R}(y - x^*)\right) = \frac{1}{(2-n)\omega_n}\left(|y-x|^{2-n} - \left|\frac{|x|y}{R} - \frac{Rx}{|x|}\right|^{2-n}\right).$$
对 $n=2$ 有类似对数形式。

**证明**：需验证 $y \in \partial B(0,R)$ 时 $G(x,y) = 0$。对 $|y|=R$：
$$\left|\frac{|x|y}{R} - \frac{Rx}{|x|}\right|^2 = \frac{|x|^2|y|^2}{R^2} - 2R(x \cdot y) \frac{|x|}{|x|} + \frac{R^2|x|^2}{|x|^2} = |x|^2 - 2x \cdot y + R^2$$
不对——正确计算：
$$\left|\frac{|x|}{R}y - \frac{R}{|x|}x\right|^2 = \frac{|x|^2}{R^2}|y|^2 - 2(y \cdot x) + \frac{R^2}{|x|^2}|x|^2 = |x|^2 - 2x \cdot y + R^2 = |y-x|^2$$
（因 $|y|=R$）。故两项相等，$G=0$。∎

**Poisson核**：对 $|y| = R$，
$$K(x,y) = \frac{R^2 - |x|^2}{\omega_n R |x-y|^n}.$$

**Poisson积分公式**：
$$u(x) = \frac{R^2 - |x|^2}{\omega_n R} \int_{|y|=R} \frac{u(y)}{|x-y|^n} \, dS_y.$$

**推论 4.2（平均值性质）**。取 $x=0$，$|x-y|=R$，得
$$u(0) = \frac{1}{\omega_n R^{n-1}} \int_{|y|=R} u(y) \, dS_y.$$

---

## 5. Neumann-Green函数与边界积分方程

### 5.1 Neumann-Green函数

Dirichlet-Green函数满足齐次Dirichlet边界条件。对Neumann问题，边界条件为 $\partial u/\partial\nu = g$，Green函数需满足齐次Neumann边界条件。然而，由Green恒等式，$\int_\Omega \Delta G = \int_{\partial\Omega} \partial G/\partial\nu$，若 $-\Delta G = \delta_x$ 且 $\partial G/\partial\nu = 0$，则 $-1 = 0$，矛盾。

**定义 5.1（Neumann-Green函数）**。修正后的Neumann-Green函数 $N(x,y)$ 满足
$$\begin{cases} -\Delta_y N(x,y) = \delta_x(y) - \frac{1}{|\Omega|} & \text{在 } \Omega \text{ 内}, \\ \frac{\partial N}{\partial \nu_y}(x,y) = 0 & y \in \partial\Omega, \end{cases}$$
其中减去常数 $1/|\Omega|$ 使右端在 $\Omega$ 上的积分为零，与Neumann数据的相容性条件 $\int_\Omega f + \int_{\partial\Omega} g = 0$ 一致。

### 5.2 边界积分方程

利用Green恒等式，可将边值问题转化为边界上的积分方程，实现问题的"降维"。

**定义 5.2（位势）**。**双层位势**（double-layer potential）
$$D[\mu](x) = \int_{\partial\Omega} \frac{\partial\Phi}{\partial\nu_y}(x,y) \mu(y) \, dS_y, \quad x \notin \partial\Omega.$$
**单层位势**（single-layer potential）
$$S[\mu](x) = \int_{\partial\Omega} \Phi(x-y) \mu(y) \, dS_y.$$

**定理 5.1（跳跃关系）**。当 $x \to x_0 \in \partial\Omega$ 时：
$$\lim_{x \to x_0^\pm} D[\mu](x) = D[\mu](x_0) \pm \frac{1}{2}\mu(x_0),$$
$$\lim_{x \to x_0^\pm} \frac{\partial S[\mu]}{\partial\nu}(x) = \frac{\partial S[\mu]}{\partial\nu}(x_0) \mp \frac{1}{2}\mu(x_0),$$
其中 $+$ 为从内部趋近，$-$ 为从外部趋近。

**Dirichlet问题的边界积分方程**：设解表示为双层位势 $u = D[\mu]$。令 $x \to \partial\Omega^-$，由跳跃关系：
$$\frac{1}{2}\mu + D[\mu] = g \quad \text{在 } \partial\Omega.$$
这是关于未知密度 $\mu$ 的第二类Fredholm积分方程，可用配置法或Galerkin法数值求解。

---

## 6. 与已有文档的关联

- [07-Laplace方程-调和函数](07-Laplace方程-调和函数.md)：调和函数的基本性质与平均值定理。
- [09-Poisson方程-边值问题](09-Poisson方程-边值问题.md)：Poisson方程Dirichlet问题的变分框架。
- [13-椭圆方程正则性](13-椭圆方程正则性.md)：Green函数的正则性与Schauder估计。
- [谱方法-增强版](../../10-应用数学/谱方法-增强版.md)：本征函数展开法构造Green函数。
- [有限元方法-深度版](../../10-应用数学/有限元方法-深度版.md)：数值PDE中边界元方法的基础。

---

## 参考文献

1. L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS, 2010. (Ch. 2)
2. D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, Springer, 2001. (Ch. 2, 4)
3. G. B. Folland, *Introduction to Partial Differential Equations*, 2nd ed., Princeton Univ. Press, 1995. (Ch. 2)
4. R. Dautray, J.-L. Lions, *Mathematical Analysis and Numerical Methods for Science and Technology*, Vol. 1, Springer, 1990.

---

**适用**：docs/16-偏微分方程/
