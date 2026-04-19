---
title: Lie群与Lie代数
description: 系统介绍Lie群与Lie代数的基本理论，包括矩阵Lie群、指数映射、Lie对应定理，以及伴随表示。
msc_primary:
  - 22E15
msc_secondary:
  - 22E60
  - 17Bxx
  - 53C30
processed_at: '2026-04-20'
references:
  textbooks:
    - id: hall_lie
      type: textbook
      title: Lie Groups, Lie Algebras, and Representations
      authors:
        - Brian C. Hall
      publisher: Springer
      year: 2015
      msc: 22-01
    - id: lee_sm
      type: textbook
      title: Introduction to Smooth Manifolds
      authors:
        - John M. Lee
      publisher: Springer
      year: 2013
      msc: 53-01
  databases:
    - id: nlab
      type: database
      name: nLab
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
---

# Lie群与Lie代数

## 引言

Lie群是同时具有群结构和微分流形结构的数学对象，且这两种结构相容（群运算是光滑的）。Lie群论由Sophus Lie在19世纪末创立，旨在用连续对称性来研究微分方程。今天，Lie群已成为现代数学和理论物理的基石：从代数几何中的代数群到粒子物理中的规范群，从表示论到微分几何中的对称空间，Lie群无处不在。

Lie代数是Lie群的"无穷小"版本——它是Lie群在单位元处的切空间，配备了一个反对称双线性运算（Lie括号）。Lie的第三定理和Lie对应定理建立了Lie群与Lie代数之间的深刻联系，使得许多Lie群问题可以转化为更简单的线性代数问题。

本教程介绍Lie群与Lie代数的基本理论，重点关注矩阵Lie群和指数映射。

---

## 1. Lie群与Lie代数的定义

### 1.1 Lie群

**定义 1.1**。流形 $G$ 称为**Lie群**，如果 $G$ 是群且乘法 $G \times G \to G$ 和逆元 $G \to G$ 都是光滑映射。

### 1.2 Lie代数

**定义 1.2**。向量空间 $\mathfrak{g}$ 配备双线性映射 $[-,-]: \mathfrak{g} \times \mathfrak{g} \to \mathfrak{g}$ 称为**Lie代数**，如果满足：

1. 反对称性：$[X, Y] = -[Y, X]$；
2. Jacobi恒等式：$[X, [Y, Z]] + [Y, [Z, X]] + [Z, [X, Y]] = 0$。

---

## 2. 矩阵Lie群

### 2.1 经典群

**例子 2.1**（矩阵Lie群）：

- $GL(n, \mathbb{R})$：可逆实矩阵。
- $SL(n, \mathbb{R})$：行列式为1。
- $O(n)$：正交矩阵，$A^T A = I$。
- $SO(n)$：特殊正交矩阵，$\det = 1$。
- $U(n)$：酉矩阵。
- $SU(n)$：特殊酉矩阵。

### 2.2 Lie代数

**命题 2.2**。若 $G$ 为矩阵Lie群，则其Lie代数

$$\mathfrak{g} = \{X \in M_n(\mathbb{R}) \mid e^{tX} \in G \text{ 对所有 } t \in \mathbb{R}\}.$$

- $\mathfrak{gl}(n) = M_n(\mathbb{R})$；
- $\mathfrak{sl}(n) = \{X \mid \operatorname{tr} X = 0\}$；
- $\mathfrak{so}(n) = \{X \mid X^T + X = 0\}$；
- $\mathfrak{u}(n) = \{X \mid X^* + X = 0\}$。

---

## 3. 指数映射

**定义 3.1**。矩阵指数

$$e^X := \sum_{k=0}^{\infty} \frac{X^k}{k!}.$$

**命题 3.2**。对矩阵Lie群 $G$，$\exp: \mathfrak{g} \to G$ 在 $0$ 附近是局部微分同胚。

---

## 4. Lie对应定理

**定理 4.1**。

1. 连通单连通Lie群由其Lie代数唯一确定（在同构意义下）。
2. 任意有限维Lie代数是某Lie群的Lie代数。

---

## 5. 重要例子

### 例子 1：$SU(2)$ 与 $SO(3)$

**例 5.1**。$\mathfrak{su}(2)$ 的基为Pauli矩阵。$SU(2)$ 是 $SO(3)$ 的二重覆盖。

### 例子 2：Heisenberg群

**例 5.2**。上三角 $3 \times 3$ 矩阵，对角元为1。其Lie代数满足 $[X, Y] = Z$，$[X, Z] = [Y, Z] = 0$。

---

## 6. 与已有文档的关联

- [01-微分流形定义](01-微分流形定义.md)：Lie群是特殊的微分流形。
- [03-切丛与向量场](03-切丛与向量场.md)：Lie代数是左不变向量场的Lie括号。
- [15-等距与Killing场](15-等距与Killing场.md)：等距群是Lie群。

---

## 练习

1. 证明 $e^{X+Y} = e^X e^Y$ 当 $[X,Y] = 0$。
2. 计算 $\mathfrak{so}(3)$ 的结构常数。
3. 证明 $SU(2) \to SO(3)$ 的覆盖映射的核为 $\{\pm I\}$。

---

## 参考文献

1. B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, Springer, 2015.
2. J. M. Lee, *Introduction to Smooth Manifolds*, Springer, 2013. (Ch. 20)
3. W. Fulton and J. Harris, *Representation Theory*, Springer, 1991.
