---
title: 高斯方程与Codazzi方程
description: 详细介绍子流形几何中的Gauss-Codazzi-Mainardi方程组，包括它们的推导、几何意义以及在等距嵌入中的应用。
msc_primary:
  - 53B25
msc_secondary:
  - 53A07
  - 53C42
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

# 高斯方程与Codazzi方程

## 引言

Gauss方程和Codazzi-Mainardi方程是子流形几何的两大基石。它们将环境空间的曲率、子流形的内蕴曲率和外蕴的第二基本形式联系起来，构成了子流形结构方程的完备组。

Gauss的绝妙定理（Theorema Egregium）——曲面的Gauss曲率只依赖于第一基本形式——正是Gauss方程在二维情形下的直接推论。Codazzi方程则给出了第二基本形式必须满足的可积性条件，它在等距嵌入问题中起着决定性作用。

本教程详细推导Gauss-Codazzi-Mainardi方程，并讨论其几何意义和应用。

---

## 1. Gauss方程

### 1.1 推导

设 $M \subseteq \widetilde{M}$ 为子流形，$\widetilde{\nabla}$ 和 $\nabla$ 分别为环境联络和诱导联络。

对 $X, Y, Z \in \mathfrak{X}(M)$：

$$\widetilde{\nabla}_X \widetilde{\nabla}_Y Z = \widetilde{\nabla}_X(\nabla_Y Z + II(Y,Z)) = \nabla_X \nabla_Y Z + II(X, \nabla_Y Z) + \nabla_X^\perp II(Y,Z) - A_{II(Y,Z)}X.$$

类似计算 $\widetilde{\nabla}_Y \widetilde{\nabla}_X Z$ 和 $\widetilde{\nabla}_{[X,Y]} Z$，代入Riemann曲率定义：

$$\widetilde{R}(X,Y)Z = R(X,Y)Z + II(X, \nabla_Y Z) - II(Y, \nabla_X Z) + \nabla_X^\perp II(Y,Z) - \nabla_Y^\perp II(X,Z) - A_{II(Y,Z)}X + A_{II(X,Z)}Y.$$

取切分量得 **Gauss方程**：

$$(\widetilde{R}(X,Y)Z)^\top = R(X,Y)Z - A_{II(Y,Z)}X + A_{II(X,Z)}Y.$$

取法分量得 **Codazzi方程**：

$$(\widetilde{R}(X,Y)Z)^\perp = (\nabla_X^\perp II)(Y,Z) - (\nabla_Y^\perp II)(X,Z).$$

---

## 2. 曲面情形的Gauss绝妙定理

**推论 2.1（Theorema Egregium）**。曲面 $M^2 \subseteq \mathbb{R}^3$ 的Gauss曲率 $K$ 只依赖于诱导度量 $g$。

*证明*。在 $\mathbb{R}^3$ 中 $\widetilde{R} = 0$。Gauss方程给出

$$0 = \langle R(X,Y)Y, X \rangle + \langle II(X,Y), II(Y,X) \rangle - \langle II(X,X), II(Y,Y) \rangle.$$

故 $K = \frac{\langle R(X,Y)Y,X \rangle}{|X|^2|Y|^2 - \langle X,Y \rangle^2}$ 只涉及 $g$ 和 $R$，即只依赖于内蕴度量。$\square$

---

## 3. 可积性定理

**定理 3.1（Bonnet）**。给定单连通流形 $M$ 上的Riemann度量 $g$ 和对称的 $NM$-值 $(0,2)$-张量 $II$，若它们满足Gauss和Codazzi方程（对某环境曲率 $\widetilde{R}$），则存在到 $\widetilde{M}$ 的等距浸入以 $g$ 和 $II$ 为第一、第二基本形式。

---

## 4. 与已有文档的关联

- [16-子流形几何](16-子流形几何.md)：第一、第二基本形式的定义。
- [18-超曲面曲率](18-超曲面曲率.md)：超曲面中Gauss-Codazzi方程的特殊形式。

---

## 练习

1. 对 $S^2(r) \subseteq \mathbb{R}^3$，用Gauss方程计算 $K$。
2. 验证平坦环面 $T^2 \subseteq \mathbb{R}^4$ 的 $II$ 满足Codazzi方程。
3. 推导Ricci方程（法丛的曲率与第二基本形式的关系）。

---

## 参考文献

1. M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992. (Ch. 6)
2. J. M. Lee, *Riemannian Manifolds*, Springer, 1997. (Ch. 8)
3. C. F. Gauss, *Disquisitiones generales circa superficies curvas*, 1827.
