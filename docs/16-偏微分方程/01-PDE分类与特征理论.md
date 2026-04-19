---
title: PDE分类与特征理论
description: 系统介绍二阶线性偏微分方程的分类（椭圆、抛物、双曲）、特征方程与特征流形、Cauchy-Kovalevskaya定理的陈述，建立PDE理论的基础框架。
msc_primary:
  - 35A01
msc_secondary:
  - 35A09
  - 35G50
  - 35M10
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
    - id: john_pde
      type: textbook
      title: Partial Differential Equations
      authors:
        - Fritz John
      publisher: Springer
      year: 1982
      msc: 35-01
---

# PDE分类与特征理论

**方程的类型决定解的性质 — 从特征到适定性**

---

## 1. 偏微分方程的基本概念

### 1.1 定义与记号

设 $\Omega \subset \mathbb{R}^n$ 为开集，$u: \Omega \to \mathbb{R}$（或 $\mathbb{C}$）为未知函数。**偏微分方程**（PDE）是涉及 $u$ 及其偏导数的函数关系：
$$F(x, u, Du, D^2u, \dots, D^mu) = 0, \quad x \in \Omega$$
其中 $Du = (\partial_{x_1}u, \dots, \partial_{x_n}u)$ 为梯度，$D^2u = (\partial_{x_ix_j}u)$ 为Hessian，$D^ku$ 为 $k$-阶导数张量。

- **阶**（order）：方程中出现的最高阶导数的阶数 $m$；
- **线性**：$F$ 关于 $u$ 及其各阶导数为线性；
- **半线性**：最高阶导数项线性，低阶项可非线性；
- **拟线性**：最高阶导数项线性，但系数可依赖于 $u$ 及其低阶导数；
- **完全非线性**：最高阶导数以非线性方式出现。

### 1.2 经典例子

**例1（线性方程）**：
- Laplace方程：$\Delta u = 0$
- 热方程：$\partial_t u - \Delta u = 0$
- 波动方程：$\partial_t^2 u - \Delta u = 0$

**例2（非线性方程）**：
- Burgers方程：$\partial_t u + u\partial_x u = 0$（拟线性）
- Monge-Ampère方程：$\det(D^2u) = f$（完全非线性）

---

## 2. 二阶线性PDE的分类

### 2.1 主符号与分类

考虑一般二阶线性PDE
$$\sum_{i,j=1}^n a_{ij}(x) \frac{\partial^2 u}{\partial x_i \partial x_j} + \sum_{i=1}^n b_i(x) \frac{\partial u}{\partial x_i} + c(x)u = f(x)$$
其中 $A(x) = (a_{ij}(x))$ 为对称矩阵（必要时对称化）。

**主符号**（principal symbol）定义为
$$p(x, \xi) = \sum_{i,j=1}^n a_{ij}(x) \xi_i \xi_j = \xi^T A(x) \xi$$

**分类**（在点 $x$ 处）：
- **椭圆型**（elliptic）：$A(x)$ 正定（或负定），即 $p(x, \xi) \neq 0$ 对所有 $\xi \neq 0$；
- **双曲型**（hyperbolic）：$A(x)$ 有 $n-1$ 个正特征值和1个负特征值（或反之），即存在方向使 $p=0$ 给出两个不同的实锥；
- **抛物型**（parabolic）：$A(x)$ 半正定，恰有一个零特征值，且低阶项（时间导数）补充了退化方向。

### 2.2 标准形式

通过坐标变换（对角化 $A$），方程可局部化为标准形式：

1. **椭圆型**（$n=2$）：$u_{xx} + u_{yy} + \dots = f$（如Laplace方程）
2. **双曲型**（$n=2$）：$u_{xx} - u_{yy} + \dots = f$（如波动方程）
3. **抛物型**（$n=2$）：$u_{xx} - u_y + \dots = f$（如热方程）

**例3（Tricomi方程）**：$y u_{xx} + u_{yy} = 0$ 在 $y > 0$ 时椭圆，$y < 0$ 时双曲，$y = 0$ 为**变型线**。这类方程属于**混合型**（mixed type）。

---

## 3. 特征理论

### 3.1 特征方程

对二阶PDE，**特征方程**定义为
$$p(x, \nabla \phi) = 0$$
即对曲面 $\Sigma = \{\phi(x) = \text{const}\}$，其法向量 $\nabla \phi$ 满足主符号为零。

满足特征方程的曲面称为**特征曲面**。特征曲面是信息传播的"波前"。

### 3.2 特征流形

更一般地，对 $m$-阶PDE，**特征流形** $(x, \xi) \in T^*\Omega$ 满足
$$p_m(x, \xi) = 0$$
其中 $p_m$ 为 $m$-阶主符号（齐次多项式）。

**定理**：若初值曲面 $\Sigma$ 处处非特征，则Cauchy数据（$u$ 及其法向导数在 $\Sigma$ 上的值）可唯一确定 $u$ 在 $\Sigma$ 附近的各阶导数。

*证明概要*：在 $\Sigma$ 上，切向导数由Cauchy数据已知。法向导数通过PDE本身确定，当且仅当 $\Sigma$ 非特征（即主符号在法向非零）。$\square$

### 3.3 不同型方程的特征

1. **椭圆型**：无实特征曲面（$p(x,\xi) = 0$ 只有 $\xi = 0$ 为实解）。信息传播无方向性。
2. **双曲型**：特征锥给出两个族特征曲面（前向与后向）。信息沿特征传播，有限传播速度。
3. **抛物型**：特征曲面为 $t = \text{const}$。信息沿时间单向传播，无穷传播速度（对热方程）。

---

## 4. Cauchy-Kovalevskaya定理

### 4.1 定理陈述

**定理（Cauchy-Kovalevskaya）**：考虑解析PDE（系数与右端为实解析函数）及解析初值曲面 $\Sigma$（处处非特征）。则对解析Cauchy数据，存在 $\Sigma$ 的邻域内唯一的**解析解**。

形式地，设方程关于某变量的最高阶导数可解出（如 $\partial_t^m u = F(x, t, \dots)$），且 $F$ 解析，初值在 $t=0$ 上解析，则存在唯一的解析解 $u(x,t)$。

### 4.2 意义与局限

- **意义**：证明了解析数据下局部存在唯一性；
- **局限**：
  1. 要求解析性，而物理问题通常只有有限光滑性；
  2. 解的定义域可能极小；
  3. 对混合型方程或特征初值问题不适用。

**例4（热方程反向不适定）**：热方程 $u_t = u_{xx}$ 反向求解（$t < 0$）时，即使初值光滑，解也可能不存在或不唯一。这属于**不适定问题**（ill-posed）。

---

## 5. 适定性（Well-posedness）

### 5.1 Hadamard适定性

**定义（Hadamard）**：PDE的定解问题称为**适定的**（well-posed），若：
1. **存在性**：解存在；
2. **唯一性**：解唯一；
3. **稳定性**：解连续依赖于数据（小扰动导致小变化）。

### 5.2 各类方程的适定问题

| 类型 | 适定问题 | 不适定问题 |
|------|---------|-----------|
| 椭圆型 | Dirichlet/Neumann边值问题 | Cauchy初值问题 |
| 抛物型 | 初边值问题（时间正向） | 反向时间演化 |
| 双曲型 | Cauchy初值问题 | Dirichlet边值问题（一般不适定） |

**例5（Laplace方程的Cauchy问题）**：设 $\Delta u = 0$ 在 $y > 0$，$u(x,0) = 0$，$\partial_y u(x,0) = \frac{1}{n}\sin(nx)$。解为 $u(x,y) = \frac{1}{n^2}\sin(nx)\sinh(ny)$。当 $n \to \infty$，初值趋于0，但解在 $y > 0$ 剧烈振荡，违反稳定性。

---

## 6. 一阶方程组与高阶分类

### 6.1 一阶对称双曲组

**定义**：一阶方程组
$$\partial_t u + \sum_{j=1}^n A_j(x,t) \partial_{x_j} u + B(x,t)u = f$$
称为**对称双曲组**，若 $A_j$ 为对称矩阵。

**定理（Friedrichs）**：对称双曲组对光滑初值有唯一光滑解，解在有限时间内存在。

### 6.2 Petrovsky抛物组

对高阶方程组，Petrovsky推广了抛物型的定义，要求主符号关于时间变量有特定根分布。

---

## 7. 小结

二阶线性PDE按主符号的定性行为分为椭圆、双曲、抛物三大类，每类有截然不同的解析性质：椭圆型方程描述稳态平衡，信息全域耦合；双曲型方程描述波动传播，信息沿特征线有限速度传播；抛物型方程描述扩散与耗散，时间单向演化。特征理论揭示了初值/边值问题的适定性根源，Cauchy-Kovalevskaya定理提供了解析框架下的局部存在性，而Hadamard适定性原则为定解问题的正确提法提供了准则。理解分类是掌握PDE理论的第一步。
