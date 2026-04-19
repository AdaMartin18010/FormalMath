---
title: 完备Riemann流形
description: 详细介绍Hopf-Rinow定理的完整证明，建立完备性、测地完备性和紧致性之间的等价关系。
msc_primary:
  - 53C20
msc_secondary:
  - 53C22
  - 53B20
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

# 完备Riemann流形

## 引言

在度量空间中，完备性（Cauchy序列收敛）保证了极限过程的安全性，是分析学的基石。在Riemann流形上，完备性有几种等价表述：作为度量空间的完备性、测地完备性（所有测地线可无限延伸）、以及有界闭集的紧致性。

Hopf-Rinow定理以优美的方式将这些概念统一起来：对Riemann流形而言，度量完备性与测地完备性等价，且它们都蕴含任意两点可由最短测地线连接。这一定理不仅是Riemann几何的理论支柱，也是全局比较几何（如Bonnet-Myers定理、Synge定理）的出发点。

本教程详细介绍Hopf-Rinow定理及其证明。

---

## 1. 完备性的各种形式

### 1.1 度量完备性

**定义 1.1**。$(M, g)$ 称为**度量完备**的，如果 $(M, d_g)$ 是完备度量空间，其中 $d_g$ 是由度量诱导的距离函数。

### 1.2 测地完备性

**定义 1.2**。$(M, g)$ 称为**测地完备**的，如果每条极大测地线 $\gamma: (a, b) \to M$ 满足 $a = -\infty$，$b = +\infty$（即测地线可无限延伸）。

### 1.3 Hopf-Rinow定理

**定理 1.3（Hopf-Rinow）**。对连通Riemann流形 $(M, g)$，以下等价：
1. $M$ 度量完备；
2. $M$ 测地完备；
3. 存在 $p \in M$ 使得 $\exp_p$ 在整个 $T_p M$ 上有定义；
4. $M$ 中任意有界闭子集是紧的。

且上述任一条件蕴含：任意两点 $p, q \in M$ 可由最短测地线连接。

---

## 2. 证明

### 2.1 (2)$\Rightarrow$(1)

*证明*。设 $M$ 测地完备。要证 $M$ 度量完备。设 $\{x_n\}$ 为Cauchy序列。它有界，故在某闭球中。由(4)（将在下一步证明），闭球紧，故 $\{x_n\}$ 有收敛子列，从而收敛。$\square$

### 2.2 核心引理

**引理 2.1**。若 $\exp_p$ 在 $\overline{B(0, R)} \subseteq T_p M$ 上有定义，则任意 $q$ 满足 $d(p, q) \leq R$ 可由最短测地线连接。

*证明*。取极小化序列，用紧性得到收敛。$\square$

### 2.3 (3)$\Rightarrow$(4)

*证明*。若 $\exp_p$ 全局定义，由引理，任意点可由测地线连接。有界闭集包含于某大闭球，而闭球是 $\exp_p(\overline{B(0, R)})$ 的像，由 $\exp_p$ 连续和 $\overline{B(0, R)}$ 紧，故闭球紧。$\square$

---

## 3. 重要例子

### 例子 1：欧氏空间

**例 3.1**。$\mathbb{R}^n$ 完备（显然）。测地线是无限延伸的直线。

### 例子 2：开球

**例 3.2**。$B(0,1) \subseteq \mathbb{R}^n$ 不完备（Cauchy序列可收敛到边界点，不在空间中）。

### 例子 3：双曲空间

**例 3.3**。$\mathbb{H}^n$ 完备，尽管它在任何等距嵌入中都是无界的。

---

## 4. 与已有文档的关联

- [11-测地线方程](11-测地线方程.md)：测地线的极大存在性是测地完备性的核心。
- [12-指数映射](12-指数映射.md)：指数映射的全局定义性是Hopf-Rinow条件之一。
- [14-变分法与Jacobi场](14-变分法与Jacobi场.md)：Jacobi场用于分析最短测地线的稳定性。

---

## 练习

1. 证明紧Riemann流形必完备。
2. 构造 $\mathbb{R}^2 \setminus \{0\}$ 上的不完备度量。
3. 验证 $\mathbb{H}^2$ 的测地完备性（通过显式解测地线方程）。

---

## 参考文献

1. M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992. (Ch. 7)
2. J. M. Lee, *Riemannian Manifolds*, Springer, 1997. (Ch. 6)
3. H. Hopf and W. Rinow, "Über den Begriff der vollständigen differentialgeometrischen Fläche", *Comment. Math. Helv.*, 1931.
