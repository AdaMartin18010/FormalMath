---
title: Levi-Civita联络
description: 阐述Levi-Civita联络的基本定理，包括存在唯一性证明、Koszul公式及其在Riemann几何中的核心地位。
msc_primary:
  - 53B20
msc_secondary:
  - 53B21
  - 53C05
processed_at: '2026-04-20'
references:
  textbooks:
    - id: lee_riemannian
      type: textbook
      title: Riemannian Manifolds
      authors:
        - John M. Lee
      publisher: Springer
      year: 1997
      msc: 53-01
    - id: do_carmo_riemannian
      type: textbook
      title: Riemannian Geometry
      authors:
        - Manfredo P. do Carmo
      publisher: Birkhäuser
      year: 1992
      msc: 53-01
  databases:
    - id: nlab
      type: database
      name: nLab
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
---

# Levi-Civita联络

## 引言

在Riemann流形上，度量结构为我们提供了长度、角度和体积的概念。自然的几何问题 arises：是否存在一种与度量相容的联络，使得平行移动保持内积，并且是无挠的？Levi-Civita的基本定理给出了肯定的答案：这样的联络存在且唯一。它就是**Levi-Civita联络**。

这一定理是Riemann几何的基石。它不仅保证了曲率张量、测地线、指数映射等核心概念的良定义性，也为物理中的广义相对论提供了数学框架——Einstein场方程正是在Levi-Civita联络下表述的。

本教程详细阐述Levi-Civita联络的基本定理及其证明。

---

## 1. 相容性条件

### 1.1 度量相容

**定义 1.1**。联络 $\nabla$ 与度量 $g$ **相容**，如果对任意向量场 $X, Y, Z$：

$$X(g(Y,Z)) = g(\nabla_X Y, Z) + g(Y, \nabla_X Z).$$

等价地，沿任意曲线平行移动保持内积。

### 1.2 无挠性

**定义 1.2**。$\nabla$ **无挠**如果挠率 $T(X,Y) = \nabla_X Y - \nabla_Y X - [X,Y] = 0$。

---

## 2. 基本定理

### 2.1 陈述

**定理 2.1（Levi-Civita）**。设 $(M, g)$ 为Riemann流形。存在唯一的联络 $\nabla$ 满足：
1. **无挠**：$\nabla_X Y - \nabla_Y X = [X, Y]$；
2. **度量相容**：$X(g(Y,Z)) = g(\nabla_X Y, Z) + g(Y, \nabla_X Z)$。

### 2.2 证明

*唯一性*。假设 $\nabla$ 存在。由度量相容和无挠性，通过循环置换 $X, Y, Z$ 并加减：

$$X g(Y,Z) + Y g(Z,X) - Z g(X,Y) = g([X,Y], Z) + g([Y,Z], X) + g([Z,X], Y) + 2g(\nabla_X Y, Z).$$

解出

$$g(\nabla_X Y, Z) = \frac{1}{2}\left(X g(Y,Z) + Y g(Z,X) - Z g(X,Y) - g([X,Y],Z) - g([Y,Z],X) - g([Z,X],Y)\right).$$

此式右侧仅依赖于 $g$ 和Lie括号，与联络无关。由于 $Z$ 任意，$\nabla_X Y$ 被唯一确定。

*存在性*。用上述Koszul公式右端定义 $\nabla_X Y$。验证它满足联络公理、无挠性和度量相容性。$\square$

### 2.3 Koszul公式

上述推导给出的显式公式称为**Koszul公式**：

$$\langle \nabla_X Y, Z \rangle = \frac{1}{2}(X\langle Y,Z\rangle + Y\langle Z,X\rangle - Z\langle X,Y\rangle - \langle [X,Y],Z\rangle - \langle [Y,Z],X\rangle + \langle [Z,X],Y\rangle).$$

---

## 3. Christoffel符号的显式公式

在坐标下，$g_{ij} = \langle \partial_i, \partial_j \rangle$，$[\partial_i, \partial_j] = 0$：

$$\Gamma^k_{ij} = \frac{1}{2} \sum_l g^{kl} \left(\partial_i g_{jl} + \partial_j g_{il} - \partial_l g_{ij}\right).$$

---

## 4. 重要例子

### 例子 1：欧氏空间

**例 4.1**。$g_{ij} = \delta_{ij}$ 为常数，故 $\Gamma^k_{ij} = 0$。Levi-Civita联络就是分量求导。

### 例子 2：球面

**例 4.2**。$S^n \subseteq \mathbb{R}^{n+1}$，诱导度量。在球坐标中，

$$\Gamma^\theta_{\phi\phi} = -\sin\theta \cos\theta, \quad \Gamma^\phi_{\theta\phi} = \cot\theta$$

（$n=2$ 情形）。

### 例子 3：双曲空间

**例 4.3**。Poincaré圆盘 $|z| < 1$，$ds^2 = \frac{4|dz|^2}{(1-|z|^2)^2}$。Levi-Civita联络给出常负曲率几何。

---

## 5. 与已有文档的关联

- [06-仿射联络](06-仿射联络.md)：Levi-Civita联络是度量相容无挠的仿射联络。
- [08-曲率张量](08-曲率张量.md)：曲率由Levi-Civita联络的二次协变微分定义。
- [11-测地线方程](11-测地线方程.md)：测地线方程使用Levi-Civita联络的Christoffel符号。

---

## 练习

1. 从Koszul公式推导坐标下的Christoffel符号公式。
2. 计算 $\mathbb{H}^2$（上半平面，$ds^2 = (dx^2 + dy^2)/y^2$）的Christoffel符号。
3. 证明度量相容性等价于沿曲线平行移动保持长度和角度。

---

## 参考文献

1. M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992. (Ch. 2, §3)
2. J. M. Lee, *Riemannian Manifolds*, Springer, 1997. (Ch. 5)
3. T. Levi-Civita, "Nozione di parallelismo in una varietà qualunque", *Rend. Circ. Mat. Palermo*, 1917.
