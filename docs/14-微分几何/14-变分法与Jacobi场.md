---
title: 变分法与Jacobi场
description: 介绍测地线变分法、第一和第二变分公式、Jacobi场、共轭点与测地线的稳定性理论。
msc_primary:
  - 53C22
msc_secondary:
  - 53B20
  - 58E10
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

# 变分法与Jacobi场

## 引言

测地线作为能量泛函的临界点，其性质的深入研究需要变分法（calculus of variations）的工具。第一变分公式告诉我们测地线恰是弧长/能量的临界点；第二变分公式则揭示了这些临界点是极小值、极大值还是鞍点——这直接关联到测地线的稳定性。

Jacobi场（Jacobi field）是沿测地线满足Jacobi方程的向量场，它们描述了测地线族的无穷小行为。共轭点（conjugate points）是Jacobi场的零点，标志着指数映射的奇异性，也是测地线失去最短性的位置。

本教程介绍测地线变分法的第一、第二变分公式，Jacobi场的定义与性质，以及共轭点理论。

---

## 1. 第一变分公式

### 1.1 弧长变分

**定理 1.1（第一变分公式）**。设 $\gamma: [a,b] \to M$ 为光滑曲线，$\gamma_s$ 为固定端点的变分，$V = \partial_s \gamma_s|_{s=0}$。则

$$\left.\frac{d}{ds}\right|_{s=0} L(\gamma_s) = -\int_a^b \left\langle V, \frac{D}{dt}\frac{\gamma'}{|\gamma'|} \right\rangle dt.$$

**推论 1.2**。弧长参数化的曲线是弧长泛函的临界点当且仅当它是测地线。

---

## 2. 第二变分公式

**定理 2.1（第二变分公式）**。设 $\gamma$ 为测地线，$V$ 为沿 $\gamma$ 的变分向量场（固定端点）。则

$$\left.\frac{d^2}{ds^2}\right|_{s=0} E(\gamma_s) = \int_a^b \left( \left\langle \frac{DV}{dt}, \frac{DV}{dt} \right\rangle - \langle R(V, \gamma')\gamma', V \rangle \right) dt.$$

---

## 3. Jacobi场

### 3.1 定义

**定义 3.1**。沿测地线 $\gamma$ 的向量场 $J$ 称为**Jacobi场**，如果满足**Jacobi方程**

$$\frac{D^2 J}{dt^2} + R(J, \gamma')\gamma' = 0.$$

### 3.2 几何意义

**命题 3.2**。Jacobi场一一对应于测地线变分的变分向量场。

### 3.3 共轭点

**定义 3.3**。$\gamma(t_0)$ 与 $\gamma(0)$ **共轭**，如果存在非零Jacobi场 $J$ 沿 $\gamma$ 使得 $J(0) = J(t_0) = 0$。

**定理 3.4**。$\gamma(0)$ 与 $\gamma(t_0)$ 共轭当且仅当 $t_0 \gamma'(0)$ 是 $\exp_p$ 的临界点。

---

## 4. 重要例子

### 例子 1：常曲率空间

**例 4.1**。常曲率 $K$ 空间中，Jacobi方程为 $J'' + KJ = 0$。
- $K = 0$（欧氏）：$J(t) = At + B$，无共轭点。
- $K > 0$（球面）：$J(t) = A \sin(\sqrt{K}t) + B \cos(\sqrt{K}t)$，对径点共轭。
- $K < 0$（双曲）：$J(t) = A \sinh(\sqrt{-K}t) + B \cosh(\sqrt{-K}t)$，无共轭点。

---

## 5. 与已有文档的关联

- [11-测地线方程](11-测地线方程.md)：Jacobi场是测地线变分的无穷小描述。
- [12-指数映射](12-指数映射.md)：共轭点是指数映射的临界点。
- [13-完备Riemann流形](13-完备Riemann流形.md)：完备性保证测地线无限延伸，是变分理论的前提。

---

## 练习

1. 从能量泛函推导第二变分公式。
2. 验证球面上对径点是共轭点。
3. 证明Jacobi场的维数为 $2n$（$n = \dim M$）。

---

## 参考文献

1. M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992. (Ch. 10)
2. J. M. Lee, *Riemannian Manifolds*, Springer, 1997. (Ch. 10)
