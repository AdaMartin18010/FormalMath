---
title: 等距与Killing场
description: 系统介绍Riemann流形上的等距映射、Killing向量场、等距群与对称空间的基础理论。
msc_primary:
  - 53C20
msc_secondary:
  - 53C35
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

# 等距与Killing场

## 引言

等距（isometry）是保持度量的微分同胚，它是Riemann几何中的"对称"。一个Riemann流形的等距群（isometry group）是其最大的保度量对称群，反映了流形的内在对称性。

Killing向量场（Killing vector field）是等距群的无穷小生成元——它们是流形上的向量场，其流（flow）产生单参数等距群。Killing方程 $L_X g = 0$（度量关于 $X$ 的Lie导数为零）是判断向量场是否为Killing场的微分判据。

本教程介绍等距映射、Killing向量场、等距群的基本性质以及对称空间的概念。

---

## 1. 等距映射

### 1.1 定义

**定义 1.1**。微分同胚 $\phi: M \to M$ 称为**等距**（isometry），如果 $\phi^* g = g$（保持度量）。

**命题 1.2**。等距保持距离函数：$d(\phi(p), \phi(q)) = d(p, q)$。

### 1.2 等距群

**定义 1.3**。$M$ 的所有等距在复合下构成群 $\operatorname{Isom}(M)$。

**定理 1.4（Myers-Steenrod）**。$\operatorname{Isom}(M)$ 是Lie群，其作用光滑。

---

## 2. Killing向量场

### 2.1 定义

**定义 2.1**。向量场 $X$ 称为**Killing场**，如果其流 $\theta_t$ 是单参数等距群。

**命题 2.2**。$X$ 是Killing场当且仅当 **Killing方程**成立：

$$L_X g = 0, \quad \text{即} \quad X^i \partial_i g_{jk} + g_{ik} \partial_j X^i + g_{ji} \partial_k X^i = 0.$$

等价地，$\langle \nabla_Y X, Z \rangle + \langle Y, \nabla_Z X \rangle = 0$ 对所有 $Y, Z$。

### 2.2 Killing场的Lie代数

**命题 2.3**。所有Killing场构成Lie代数 $\mathfrak{isom}(M)$，它是 $\operatorname{Isom}(M)$ 的Lie代数。

---

## 3. 对称空间

**定义 3.1**。Riemann流形 $M$ 称为**对称空间**，如果对每点 $p \in M$ 存在等距 $s_p: M \to M$（**对合**），使得 $s_p(p) = p$ 且 $d(s_p)_p = -\operatorname{id}$。

**命题 3.2**。对称空间的曲率张量平行：$\nabla R = 0$。

---

## 4. 与已有文档的关联

- [02-切空间与切向量](02-切空间与切向量.md)：等距的切映射保持内积。
- [03-切丛与向量场](03-切丛与向量场.md)：Killing场是特殊的向量场。
- [20-Lie群与Lie代数](20-Lie群与Lie代数.md)：等距群是Lie群。

---

## 练习

1. 证明 $\mathbb{R}^n$ 的Killing场恰为 $X(x) = Ax + b$，$A$ 反对称。
2. 验证 $S^n$ 的Killing场由 $\mathbb{R}^{n+1}$ 的反对称线性映射诱导。
3. 证明对称空间的Killing场在任意点张成切空间。

---

## 参考文献

1. S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. 1-2, Wiley, 1963-1969.
2. J. M. Lee, *Riemannian Manifolds*, Springer, 1997. (Ch. 11)
