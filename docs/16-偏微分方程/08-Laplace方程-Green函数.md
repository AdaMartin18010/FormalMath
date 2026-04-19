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

**边值问题的核 — 从镜像法到积分表示**

---

## 1. Green函数的定义

### 1.1 动机

对Poisson方程的Dirichlet问题
$$\begin{cases} -\Delta u = f & \text{in } \Omega \\ u = g & \text{on } \partial\Omega \end{cases}$$
希望找到核函数 $G(x,y)$ 使得解可表示为
$$u(x) = \int_\Omega G(x,y)f(y)dy + \text{(边界项)}$$

### 1.2 定义

设 $\Omega \subset \mathbb{R}^n$ 为光滑有界区域。$\Omega$ 的**Dirichlet-Green函数** $G(x,y)$ 对固定 $x \in \Omega$ 满足
$$\begin{cases} -\Delta_y G(x,y) = \delta_x(y) & y \in \Omega \\ G(x,y) = 0 & y \in \partial\Omega \end{cases}$$

即 $G(x,y) = \Phi(x-y) - \phi^x(y)$，其中 $\Phi$ 为Laplace方程基本解，$\phi^x(y)$ 为**校正函数**，满足
$$\begin{cases} \Delta_y \phi^x = 0 & \text{in } \Omega \\ \phi^x(y) = \Phi(x-y) & \text{on } \partial\Omega \end{cases}$$

校正函数 $\phi^x$ 抵消了 $\Phi(x-y)$ 在边界上的奇异性，使 $G$ 满足齐次Dirichlet边界条件。

---

## 2. Green函数的性质

### 2.1 对称性

**定理**：$G(x,y) = G(y,x)$ 对 $x \neq y$。

*证明*：对 $x_1 \neq x_2$，在 $\Omega \setminus (B(x_1,\varepsilon) \cup B(x_2,\varepsilon))$ 上对 $u(y) = G(x_1,y)$，$v(y) = G(x_2,y)$ 应用Green第二恒等式。令 $\varepsilon \to 0$，奇异性贡献给出 $u(x_2) = v(x_1)$。$\square$

### 2.2 正性

**定理**：$G(x,y) > 0$ 对 $x, y \in \Omega$，$x \neq y$。

*证明*：固定 $x$，$G(x,y)$ 在 $\Omega \setminus \{x\}$ 上调和，在边界为零。由强最大值原理，内部为正（因在 $x$ 附近 $G \sim \Phi > 0$）。$\square$

### 2.3 边界奇异性

当 $y \to \partial\Omega$，$G(x,y) \to 0$；当 $y \to x$，$G(x,y) \sim \Phi(x-y)$ 发散。

---

## 3. 表示公式

### 3.1 Dirichlet问题

**定理**：设 $u \in C^2(\overline{\Omega})$。则
$$u(x) = \int_\Omega G(x,y) (-\Delta u)(y) dy - \int_{\partial\Omega} \frac{\partial G}{\partial \nu_y}(x,y) u(y) dS_y$$

对Dirichlet问题 $-\Delta u = f$，$u|_{\partial\Omega} = g$，
$$u(x) = \int_\Omega G(x,y) f(y) dy - \int_{\partial\Omega} \frac{\partial G}{\partial \nu_y}(x,y) g(y) dS_y$$

特别地，调和函数（$f=0$）完全由边界值决定：
$$u(x) = -\int_{\partial\Omega} \frac{\partial G}{\partial \nu_y}(x,y) g(y) dS_y$$

### 3.2 Poisson核

定义**Poisson核**
$$K(x,y) = -\frac{\partial G}{\partial \nu_y}(x,y), \quad x \in \Omega, \, y \in \partial\Omega$$

对Laplace方程Dirichlet问题，$u(x) = \int_{\partial\Omega} K(x,y) g(y) dS_y$。

**性质**：$K(x,y) > 0$ 且 $\int_{\partial\Omega} K(x,y) dS_y = 1$。

---

## 4. 显式Green函数

### 4.1 上半空间

设 $\Omega = \mathbb{R}^n_+ = \{x_n > 0\}$。对 $x = (x', x_n)$，其关于边界的**镜像点**为 $\tilde{x} = (x', -x_n)$。

**Green函数**：
$$G(x,y) = \Phi(y-x) - \Phi(y-\tilde{x})$$

因 $\Phi(y-\tilde{x})$ 在 $y_n > 0$ 上调和，且在 $y_n = 0$ 上等于 $\Phi(y-x)$（因 $|y-x| = |y-\tilde{x}|$ 当 $y_n = 0$）。

**Poisson核**：
$$K(x,y) = \frac{2x_n}{\omega_n |x-y|^n}, \quad y \in \partial\mathbb{R}^n_+$$

Dirichlet问题的解：
$$u(x) = \frac{2x_n}{\omega_n} \int_{\mathbb{R}^{n-1}} \frac{g(y')}{(|x'-y'|^2 + x_n^2)^{n/2}} dy'$$

**例1（$n=2$）**：上半平面的Poisson核为 $K(x,y) = \frac{1}{\pi} \frac{x_2}{(x_1-y)^2 + x_2^2}$，即Cauchy分布。这正是Poisson积分公式的核心。

### 4.2 球

设 $\Omega = B(0,R)$。对 $x \neq 0$，定义反演点 $x^* = \frac{R^2}{|x|^2} x$。

**Green函数**（$n \geq 3$）：
$$G(x,y) = \Phi(y-x) - \Phi\left(\frac{|x|}{R}(y - x^*)\right)$$
（$n=2$ 有类似对数形式）。

**Poisson核**（球面 $|y| = R$）：
$$K(x,y) = \frac{R^2 - |x|^2}{\omega_n R |x-y|^n}$$

**定理（Poisson积分公式）**：若 $u$ 在 $B(0,R)$ 上调和且 $u \in C(\overline{B})$，则
$$u(x) = \frac{R^2 - |x|^2}{\omega_n R} \int_{|y|=R} \frac{u(y)}{|x-y|^n} dS_y$$

**例2（均值性质的重获）**：取 $x=0$，$|x-y| = R$，得
$$u(0) = \frac{1}{\omega_n R^{n-1}} \int_{|y|=R} u(y) dS_y$$
即球面平均值公式。

---

## 5. Neumann-Green函数

### 5.1 定义

**Neumann-Green函数** $N(x,y)$ 满足
$$\begin{cases} -\Delta_y N = \delta_x - \frac{1}{|\Omega|} & y \in \Omega \\ \frac{\partial N}{\partial \nu_y} = 0 & y \in \partial\Omega \end{cases}$$

（需减去常数 $1/|\Omega|$ 以使相容性条件 $\int_\Omega \delta_x = \int_\Omega \frac{1}{|\Omega|}$ 成立）。

### 5.2 表示公式

对Neumann问题 $-\Delta u = f$，$\partial_\nu u = g$（需满足相容性 $\int_\Omega f + \int_{\partial\Omega} g = 0$），
$$u(x) = \int_\Omega N(x,y) f(y) dy + \int_{\partial\Omega} N(x,y) g(y) dS_y + C$$
（解在相差常数意义下唯一）。

---

## 6. 边界积分方程

### 6.1 单层与双层位势

利用Green恒等式，可将边值问题转化为边界上的积分方程。

**双层位势**：$D[\mu](x) = \int_{\partial\Omega} \frac{\partial \Phi}{\partial \nu_y}(x,y) \mu(y) dS_y$

**单层位势**：$S[\mu](x) = \int_{\partial\Omega} \Phi(x-y) \mu(y) dS_y$

### 6.2 跳跃关系

当 $x \to \partial\Omega$，双层位势有跳跃：
$$\lim_{x \to x_0^\pm} D[\mu](x) = D[\mu](x_0) \pm \frac{1}{2}\mu(x_0)$$
（内部取 $+$，外部取 $-$）。

单层位势的法向导数有类似跳跃：
$$\lim_{x \to x_0^\pm} \frac{\partial S[\mu]}{\partial \nu}(x) = \frac{\partial S[\mu]}{\partial \nu}(x_0) \mp \frac{1}{2}\mu(x_0)$$

### 6.3 Dirichlet问题的积分方程

设Dirichlet问题解表示为双层位势 $u = D[\mu]$。令 $x \to \partial\Omega^-$，得边界积分方程
$$\frac{1}{2}\mu + D[\mu] = g$$
这是关于未知密度 $\mu$ 的第二类Fredholm积分方程，可用数值方法求解。

---

## 7. 小结

Green函数将Poisson方程Dirichlet问题的求解约化为核函数的构造与积分。镜像法给出对称区域（半空间、球、矩形等）的显式公式，而一般区域则需要数值或渐近方法。Poisson核的存在性与正性保证了Dirichlet问题解的正则性与最大值原理。边界积分方程方法则将PDE问题降维到边界，在计算数学与散射理论中有重要应用。Green函数的思想贯穿椭圆方程、抛物方程乃至随机过程（Brown运动的离开概率），是数学中最具统一性的概念之一。
