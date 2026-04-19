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

Gauss方程和Codazzi-Mainardi方程是子流形几何的两大基石，它们将环境空间的曲率、子流形的内蕴曲率和外蕴的第二基本形式联系起来，构成了子流形结构方程的完备组。高斯于1827年在其杰作《曲面的一般研究》中发现了Gauss方程在曲面情形的推论——曲面的Gauss曲率仅依赖于第一基本形式（Theorema Egregium），这一发现开创了微分几何的内蕴时代。Codazzi方程则给出了第二基本形式必须满足的可积性条件，在等距嵌入问题中起着决定性作用。

本教程从子流形的Gauss-Weingarten方程出发，严格推导Gauss-Codazzi-Mainardi-Ricci方程组，证明Gauss绝妙定理，并给出Bonnet可积性定理。

---

## 1. 子流形的基本方程回顾

设 $(\widetilde{M}, \widetilde{g})$ 为Riemann流形，$M \subseteq \widetilde{M}$ 为嵌入子流形。记：

- $\widetilde{\nabla}$：$\widetilde{M}$ 上的Levi-Civita联络；
- $\nabla$：$M$ 上的诱导Levi-Civita联络；
- $\nabla^\perp$：法丛 $NM$ 上的法联络；
- $II$：第二基本形式；
- $A_\xi$：关于法向量 $\xi$ 的形状算子。

**Gauss公式**：对 $X, Y \in \mathfrak{X}(M)$，
$$\widetilde{\nabla}_X Y = \nabla_X Y + II(X,Y).$$

**Weingarten公式**：对 $X \in \mathfrak{X}(M)$，$\xi \in \Gamma(NM)$，
$$\widetilde{\nabla}_X \xi = -A_\xi X + \nabla_X^\perp \xi.$$

---

## 2. Gauss方程的推导

### 2.1 曲率张量的分解

对 $X, Y, Z \in \mathfrak{X}(M)$，计算环境Riemann曲率：
$$\widetilde{R}(X,Y)Z = \widetilde{\nabla}_X \widetilde{\nabla}_Y Z - \widetilde{\nabla}_Y \widetilde{\nabla}_X Z - \widetilde{\nabla}_{[X,Y]} Z.$$

展开 $\widetilde{\nabla}_Y Z = \nabla_Y Z + II(Y,Z)$，再对 $X$ 求导：
$$\widetilde{\nabla}_X(\widetilde{\nabla}_Y Z) = \widetilde{\nabla}_X(\nabla_Y Z) + \widetilde{\nabla}_X(II(Y,Z))$$
$$= \nabla_X \nabla_Y Z + II(X, \nabla_Y Z) - A_{II(Y,Z)}X + \nabla_X^\perp II(Y,Z).$$

类似展开 $\widetilde{\nabla}_Y \widetilde{\nabla}_X Z$ 和 $\widetilde{\nabla}_{[X,Y]} Z$，代入曲率定义。

### 2.2 Gauss方程（切分量）

取切向分量（投影到 $TM$），法联络项和 $II$ 项的部分消去，得：

**定理 2.1（Gauss方程）**。对 $X,Y,Z,W \in \mathfrak{X}(M)$，
$$\langle \widetilde{R}(X,Y)Z, W \rangle = \langle R(X,Y)Z, W \rangle + \langle II(X,Z), II(Y,W) \rangle - \langle II(X,W), II(Y,Z) \rangle. \tag{Gauss}$$

等价地，用形状算子：
$$\langle \widetilde{R}(X,Y)Z, W \rangle = \langle R(X,Y)Z, W \rangle + \langle A_{II(Y,Z)}X, W \rangle - \langle A_{II(X,Z)}Y, W \rangle.$$

### 2.3 Codazzi方程（法分量）

取法向分量，得：

**定理 2.2（Codazzi-Mainardi方程）**。对 $X,Y,Z \in \mathfrak{X}(M)$，
$$\left(\widetilde{R}(X,Y)Z\right)^\perp = (\nabla_X^\perp II)(Y,Z) - (\nabla_Y^\perp II)(X,Z). \tag{Codazzi}$$

其中 $(\nabla_X^\perp II)(Y,Z) = \nabla_X^\perp(II(Y,Z)) - II(\nabla_X Y, Z) - II(Y, \nabla_X Z)$ 为第二基本形式的协变导数。

### 2.4 Ricci方程

对法向量场，有 **Ricci方程**：
$$\langle R^\perp(X,Y)\xi, \eta \rangle = \langle \widetilde{R}(X,Y)\xi, \eta \rangle + \langle [A_\xi, A_\eta]X, Y \rangle,$$
其中 $R^\perp$ 为法丛的曲率，$[A_\xi, A_\eta] = A_\xi A_\eta - A_\eta A_\xi$。

---

## 3. Gauss绝妙定理

### 3.1 超曲面情形

设 $M^n \subseteq \widetilde{M}^{n+1}$ 为超曲面，法丛1维。取单位法向量 $N$，第二基本形式 $II(X,Y) = h(X,Y)N$，$h$ 为标量值对称张量。

**定理 3.1（Gauss方程的超曲面形式）**。对 $X,Y,Z,W \in TM$，
$$\langle \widetilde{R}(X,Y)Z, W \rangle = \langle R(X,Y)Z, W \rangle + h(X,Z)h(Y,W) - h(X,W)h(Y,Z).$$

### 3.2 Theorema Egregium

**定理 3.2（Theorema Egregium, Gauss 1827）**。设 $M^2 \subseteq \mathbb{R}^3$ 为正则曲面。则Gauss曲率 $K$ 仅依赖于诱导度量 $g$（第一基本形式）。

**证明**：在 $\mathbb{R}^3$ 中，$\widetilde{R} = 0$。Gauss方程给出
$$0 = \langle R(X,Y)Y, X \rangle + h(X,Y)^2 - h(X,X)h(Y,Y).$$
故
$$\langle R(X,Y)Y, X \rangle = h(X,X)h(Y,Y) - h(X,Y)^2 = \det(h_{ij}) \cdot (|X|^2|Y|^2 - \langle X,Y \rangle^2).$$
 sectional曲率 $K = \frac{\langle R(X,Y)Y,X \rangle}{|X|^2|Y|^2 - \langle X,Y \rangle^2} = \det(h_{ij})/\det(g_{ij})$。

但左边 $R$ 完全由 $g$ 的Christoffel符号决定，而后者仅依赖于 $g$ 的一阶和二阶导数。故 $K$ 仅依赖于 $g$。∎

**几何意义**：曲面的"弯曲"（Gauss曲率）可由生活在曲面上的生物通过测量内蕴距离完全确定，无需知道曲面如何嵌入三维空间。这一发现标志着微分几何从内蕴与外蕴并重的阶段进入以内蕴为主导的现代阶段。

---

## 4. Bonnet可积性定理

**定理 4.1（Bonnet定理）**。设 $M$ 为单连通Riemann流形，$g$ 为其度量。设 $II$ 为 $NM$-值对称 $(0,2)$-张量（$NM$ 为某秩 $k$ 的Riemann向量丛，配度量联络 $\nabla^\perp$）。若 $(g, II)$ 满足Gauss、Codazzi和Ricci方程（对某环境曲率 $\widetilde{R}$），则存在等距浸入 $F: M \to \widetilde{M}$ 以 $g$ 为第一基本形式、$II$ 为第二基本形式，且在 $\widetilde{M}$ 的刚体运动下唯一。

**证明概要**：考虑丛 $TM \oplus NM$ 上的联络 $D$，定义为
$$D_X(Y + \xi) = \nabla_X Y + II(X,Y) + \nabla_X^\perp \xi - A_\xi X.$$
Gauss-Codazzi-Ricci方程恰是 $D$ 的平坦性条件 $R^D = 0$。因 $M$ 单连通，$D$ 给出丛的平行标架，从而构造浸入 $F$。唯一性由初始标架的刚性决定。∎

---

## 5. 具体例子

### 例子 5.1：$S^2(r) \subseteq \mathbb{R}^3$

单位法向量 $N$ 指向外侧。对切向量 $X$，$\widetilde{\nabla}_X N = X/r$（因位置向量 $rN$ 的导数为 $X$）。故形状算子 $A_N = -I/r$（符号依约定），第二基本形式 $h = -g/r$。

Gauss方程：$0 = \langle R(X,Y)Z,W \rangle + \frac{1}{r^2}(\langle X,Z \rangle \langle Y,W \rangle - \langle X,W \rangle \langle Y,Z \rangle)$。

故 $R(X,Y)Z = \frac{1}{r^2}(\langle Y,Z \rangle X - \langle X,Z \rangle Y)$，sectional曲率 $K = 1/r^2$。

### 例子 5.2：平坦环面 $T^2 \subseteq \mathbb{R}^4$

$T^2 = S^1(1) \times S^1(1) \subseteq \mathbb{R}^2 \times \mathbb{R}^2 = \mathbb{R}^4$。参数化：$(\theta, \varphi) \mapsto (\cos\theta, \sin\theta, \cos\varphi, \sin\varphi)$。

切向量：$X = (-\sin\theta, \cos\theta, 0, 0)$，$Y = (0, 0, -\sin\varphi, \cos\varphi)$。$g_{11}=g_{22}=1$，$g_{12}=0$，度量平坦。

在 $\mathbb{R}^4$ 中，$\widetilde{\nabla}_X X = (-\cos\theta, -\sin\theta, 0, 0)$ 法向。同理 $\widetilde{\nabla}_Y Y$ 法向。$\widetilde{\nabla}_X Y = 0$。

法向量：$N_1 = (\cos\theta, \sin\theta, 0, 0)$，$N_2 = (0, 0, \cos\varphi, \sin\varphi)$。

$II(X,X) = N_1$，$II(Y,Y) = N_2$，$II(X,Y) = 0$。

Gauss方程：$0 = \langle R(X,Y)Y,X \rangle + 0 - 0$，故 $R = 0$，与平坦度量一致。Codazzi方程显然满足。

---

## 6. 与已有文档的关联

- [16-子流形几何](16-子流形几何.md)：第一、第二基本形式的定义与性质。
- [18-超曲面曲率](18-超曲面曲率.md)：超曲面中Gauss-Codazzi方程的特殊形式。
- [08-曲率张量](08-曲率张量.md)：Riemann曲率张量的基本理论。
- [07-Levi-Civita联络](07-Levi-Civita联络.md)：诱导联络与Levi-Civita联络。
- [20-Lie群与Lie代数](20-Lie群与Lie代数.md)：对称空间中的Gauss-Codazzi方程。

---

## 参考文献

1. C. F. Gauss, *Disquisitiones generales circa superficies curvas*, 1827.
2. M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992. (Ch. 6)
3. J. M. Lee, *Riemannian Manifolds*, Springer, 1997. (Ch. 8)
4. S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry*, Vol. II, Wiley, 1969. (Ch. 7)

---

**适用**：docs/14-微分几何/
