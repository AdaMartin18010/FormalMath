---
title: Ricci曲率与标量曲率
description: 详细介绍Ricci曲率和标量曲率的定义、几何意义、缩并过程，以及Einstein流形和Einstein场方程的数学基础。
msc_primary:
  - 53B20
msc_secondary:
  - 53C25
  - 83C05
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

# Ricci曲率与标量曲率

## 引言

Riemann曲率张量是一个庞大的对象（$n^4$ 个分量，尽管对称性减少了独立分量），在物理和几何中直接使用起来往往过于复杂。通过适当的"缩并"（contraction），我们可以得到更简洁但仍富含信息的不变量：Ricci曲率张量和标量曲率。

Ricci曲率 $Ric$ 是一个对称 $(0,2)$-张量，描述体积元在测地线收敛/发散时的变化率。标量曲率 $S$ 是一个函数，是Ricci曲率的进一步缩并，度量某点处体积元与欧氏空间的偏差。

在广义相对论中，Einstein场方程将时空的几何（Einstein张量，由Ricci曲率构造）与物质的能量-动量分布联系起来。Einstein流形——满足 $Ric = \lambda g$ 的流形——是Riemann几何的重要研究对象。

本教程介绍Ricci曲率、标量曲率的定义、几何意义以及Einstein流形。

---

## 1. Ricci曲率

### 1.1 定义

**定义 1.1**。Riemann曲率张量 $R^l_{\,kij}$ 对第一和第三指标的**缩并**给出 **Ricci曲率张量**：

$$R_{ij} := R^k_{\,ikj} = \sum_k R^k_{\,ikj}.$$

等价地，$Ric(X,Y) = \operatorname{tr}(Z \mapsto R(Z,X)Y)$。

### 1.2 对称性

**命题 1.2**。$R_{ij} = R_{ji}$（Ricci张量对称）。

*证明*。由Riemann张量的对称性 $R_{ikjl} = R_{jlik}$ 和第一Bianchi恒等式。$\square$

---

## 2. 标量曲率

**定义 2.1**。对Ricci张量再次缩并（通过度量提升一个指标后缩并）：

$$S := g^{ij} R_{ij} = \sum_{i,j} g^{ij} R_{ij}.$$

**命题 2.2**。标量曲率是坐标无关的光滑函数 $S: M \to \mathbb{R}$。

---

## 3. Einstein流形

### 3.1 定义

**定义 3.1**。Riemann流形 $(M, g)$ 称为**Einstein流形**，如果存在常数 $\lambda$ 使得

$$Ric = \lambda g.$$

### 3.2 例子

**例子 3.2**。常曲率空间是Einstein的：$Ric = (n-1)Kg$。

**例子 3.3**。Calabi-Yau流形：Ricci平坦（$\lambda = 0$），Kähler，具有平行旋量。

---

## 4. Einstein场方程

**定义 4.1**。**Einstein张量**定义为

$$G := Ric - \frac{1}{2} S g.$$

**Einstein场方程**（无宇宙学常数）：

$$G = 8\pi T,$$

其中 $T$ 为能量-动量张量。

**等价形式**：$Ric = 8\pi(T - \frac{1}{2} \operatorname{tr}(T) g)$。

---

## 5. 与已有文档的关联

- [08-曲率张量](08-曲率张量.md)：Ricci和标量曲率由Riemann张量缩并得到。
- [10-截面曲率](10-截面曲率.md)：截面曲率是Riemann张量的二维限制。

---

## 练习

1. 计算 $S^n$ 的Ricci曲率和标量曲率。
2. 证明二维流形总是Einstein的（因Ricci只有一个独立分量）。
3. 推导真空Einstein方程 $Ric = 0$ 等价于 $G = 0$。

---

## 参考文献

1. M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992. (Ch. 4)
2. J. M. Lee, *Riemannian Manifolds*, Springer, 1997. (Ch. 7)
3. A. Besse, *Einstein Manifolds*, Springer, 1987.
