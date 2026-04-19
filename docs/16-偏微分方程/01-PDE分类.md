---
title: PDE分类
description: 系统介绍偏微分方程的分类体系，包括椭圆型、抛物型、双曲型方程的定义、典型例子及其数学特征。
msc_primary:
  - 35A01
msc_secondary:
  - 35Jxx
  - 35Kxx
  - 35Lxx
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
  databases:
    - id: nlab
      type: database
      name: nLab
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
---

# PDE分类

## 引言

偏微分方程（Partial Differential Equations, PDE）是描述多变量函数及其偏导数之间关系的方程。与常微分方程（ODE）不同，PDE涉及多个自变量，其理论更加丰富、复杂且深刻。物理、工程、金融和生物学中的绝大多数基本定律都以PDE的形式表达：电磁学的Maxwell方程、流体力学的Navier-Stokes方程、量子力学的Schrödinger方程、广义相对论的Einstein场方程，等等。

对PDE进行系统的分类是理解其数学性质的第一步。二阶线性PDE按照其最高阶项的系数矩阵的特征值，被分为三大类：椭圆型（elliptic）、抛物型（parabolic）和双曲型（hyperbolic）。每类方程都有其独特的性质：适定性（well-posedness）、正则性、传播行为等。

本教程系统介绍PDE的分类体系及其数学特征。

---

## 1. 二阶线性PDE的一般形式

### 1.1 一般形式

设 $\Omega \subseteq \mathbb{R}^n$ 为开集。二阶线性PDE的一般形式为

$$\sum_{i,j=1}^n a_{ij}(x) \frac{\partial^2 u}{\partial x_i \partial x_j} + \sum_{i=1}^n b_i(x) \frac{\partial u}{\partial x_i} + c(x) u = f(x),$$

其中 $a_{ij}, b_i, c, f$ 为给定函数，$a_{ij} = a_{ji}$（可假设对称）。

### 1.2 主符号与特征形式

**定义 1.1**。方程的**主符号**（principal symbol）为

$$A(x, \xi) := \sum_{i,j} a_{ij}(x) \xi_i \xi_j, \quad \xi \in \mathbb{R}^n.$$

对应的矩阵 $A(x) = (a_{ij}(x))$ 是对称的。

---

## 2. 分类标准

### 2.1 基于特征值的分类

**定义 2.1**。在点 $x \in \Omega$ 处：
1. **椭圆型**：$A(x)$ 的所有特征值同号（全正或全负）。等价地，$A(x, \xi) \neq 0$ 对所有 $\xi \neq 0$。
2. **抛物型**：$A(x)$ 的一个特征值为零，其余同号。
3. **双曲型**：$A(x)$ 的一个特征值为正，其余为负（或相反）。

**定义 2.2**。方程在区域 $\Omega$ 上称为椭圆/抛物/双曲的，如果在每点都如此。

---

## 3. 典型例子

### 3.1 椭圆型方程

**例子 3.1（Laplace方程）**。$$\Delta u = \sum_{i=1}^n \frac{\partial^2 u}{\partial x_i^2} = 0.$$

$a_{ij} = \delta_{ij}$，特征值全为 $1$。描述稳态现象（静电势、热平衡等）。

**例子 3.2（Poisson方程）**。$$-\Delta u = f.$$

### 3.2 抛物型方程

**例子 3.3（热方程）**。$$\frac{\partial u}{\partial t} - \Delta u = 0.$$

时间变量 $t$，空间变量 $x$。$a_{ij}$ 矩阵有一个零特征值（时间方向），其余为正。描述扩散过程。

### 3.3 双曲型方程

**例子 3.4（波动方程）**。$$\frac{\partial^2 u}{\partial t^2} - \Delta u = 0.$$

时间特征值为 $1$，空间特征值为 $-1$。描述波动传播。

---

## 4. 各类方程的基本特征

### 4.1 椭圆型

- **适定性**：Dirichlet边值问题适定。
- **正则性**：解在内部无限光滑（若系数光滑）。
- **极值原理**：解在区域内部不取极值（除非常数）。
- **传播**：无特征传播，信息瞬间影响全空间。

### 4.2 抛物型

- **适定性**：初值-边值问题适定（时间向前）。
- **正则化**：即使初值不光滑，解在 $t > 0$ 时变得光滑。
- **极值原理**：有强最大值原理。
- **传播**：信息以无限速度传播（对热方程）。

### 4.3 双曲型

- **适定性**：初值问题适定（需两个初值条件）。
- **正则性**：解的正则性不高于初值（无奇性磨光）。
- **有限传播速度**：扰动以有限速度传播。
- **特征线/面**：信息沿特征传播。

---

## 5. 更广泛的分类

### 5.1 高阶方程与方程组

对高阶方程或方程组，分类基于主符号的代数性质。

### 5.2 非线性方程

非线性PDE的分类通常在线性化后进行，即考察其关于解的线性化方程的类型。

---

## 6. 与已有文档的关联

- [02-一阶方程与特征线法](02-一阶方程与特征线法.md)：特征线是双曲型方程的核心工具。
- [03-波动方程-D'Alembert公式](03-波动方程-D'Alembert公式.md)：双曲型方程的典型解法。
- [05-热方程-基本解](05-热方程-基本解.md)：抛物型方程的基本解。
- [07-Laplace方程-调和函数](07-Laplace方程-调和函数.md)：椭圆型方程的核心理论。

---

## 练习

1. 对 $u_{xx} + 4u_{xy} + 3u_{yy} = 0$，在 $\mathbb{R}^2$ 上分类并化为标准形。
2. 判断Tricomi方程 $y u_{xx} + u_{yy} = 0$ 在各点的类型。
3. 解释为什么热方程的信息传播速度无限，而波动方程有限。

---

## 参考文献

1. L. C. Evans, *Partial Differential Equations*, AMS, 2010. (Ch. 2-4)
2. F. John, *Partial Differential Equations*, Springer, 1982.
3. R. Courant and D. Hilbert, *Methods of Mathematical Physics*, Vol. 2, Wiley, 1962.
