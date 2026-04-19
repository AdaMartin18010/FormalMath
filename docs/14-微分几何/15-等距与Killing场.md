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

等距（isometry）是Riemann几何中的"对称"——保持度量的微分同胚。一个Riemann流形的等距群（isometry group）是其最大的保度量变换群，反映了流形的内在对称性。等距群不仅是Lie群（Myers-Steenrod定理），其维数还受到流形维数的严格限制。

Killing向量场是等距群的无穷小生成元，其流产生单参数等距群。Killing方程 $\mathcal{L}_X g = 0$——度量关于 $X$ 的Lie导数为零——将等距的无限小刻画转化为一个线性偏微分方程组。在物理中，Killing场对应于守恒量：时间平移Killing场给出能量守恒，空间平移Killing场给出动量守恒。

本教程从等距的定义出发，建立Killing方程，分析等距群的Lie群结构，引入对称空间的概念，并通过具体例子展示理论的应用。

---

## 1. 等距映射

### 1.1 定义与基本性质

**定义 1.1**。设 $(M, g)$，$(N, h)$ 为Riemann流形。微分同胚 $\phi: M \to N$ 称为 **等距**（isometry），若 $\phi^* h = g$，即
$$g_p(X, Y) = h_{\phi(p)}(d\phi_p(X), d\phi_p(Y)) \quad \forall p \in M, \, X, Y \in T_p M.$$

**命题 1.1**。等距保持距离函数：$d_M(p, q) = d_N(\phi(p), \phi(q))$。

**证明**：距离定义为下确界曲线长度，等距保持曲线长度（因保持度量），故保持距离。∎

**命题 1.2**。等距保持Levi-Civita联络：$\phi_* (\nabla_X Y) = \nabla_{\phi_* X} (\phi_* Y)$。从而保持Riemann曲率、Ricci曲率、标量曲率。

### 1.2 局部等距

**定义 1.2**。局部微分同胚 $\phi: M \to N$ 称为 **局部等距**，若 $\phi^* h = g$。

**例 1.1**。覆叠映射 $\pi: \mathbb{R}^n \to T^n = \mathbb{R}^n / \mathbb{Z}^n$ 为局部等距，但不是整体等距（因非单射）。

---

## 2. Killing向量场

### 2.1 无穷小等距

**定义 2.1**。向量场 $X \in \mathfrak{X}(M)$ 称为 **Killing向量场**（Killing field），若其流 $\theta_t$（$t$ 充分小）由等距组成。即 $\theta_t^* g = g$ 对所有 $t$。

**定理 2.1（Killing方程）**。$X$ 为Killing场当且仅当
$$\mathcal{L}_X g = 0,$$
等价地，对任意 $Y, Z \in \mathfrak{X}(M)$，
$$\langle \nabla_Y X, Z \rangle + \langle Y, \nabla_Z X \rangle = 0. \tag{Killing}$$

**证明**：$\theta_t^* g = g$ 对 $t$ 在0处求导：$\left.\frac{d}{dt}\right|_{t=0} \theta_t^* g = \mathcal{L}_X g = 0$。反之，若 $\mathcal{L}_X g = 0$，则 $\frac{d}{dt} \theta_t^* g = \theta_t^* (\mathcal{L}_X g) = 0$，故 $\theta_t^* g$ 为常数，等于 $g$。

在局部坐标下，$\mathcal{L}_X g = X^k \partial_k g_{ij} + g_{kj} \partial_i X^k + g_{ik} \partial_j X^k = 0$。

用联络表示：$(\mathcal{L}_X g)_{ij} = \nabla_i X_j + \nabla_j X_i = 0$。∎

### 2.2 Killing场的性质

**命题 2.1**。Killing场 $X$ 满足 $\operatorname{div} X = 0$（因 $\operatorname{div} X = g^{ij}\nabla_i X_j = 0$）。

**命题 2.2**。若 $X, Y$ 为Killing场，则 $[X, Y]$ 为Killing场。

**证明**：$\mathcal{L}_{[X,Y]} g = \mathcal{L}_X \mathcal{L}_Y g - \mathcal{L}_Y \mathcal{L}_X g = 0$。∎

**定理 2.2**。完备Riemann流形上的Killing场是完备的（其流对所有 $t \in \mathbb{R}$ 有定义）。

### 2.3 Killing场的Jacobi场解释

**定理 2.3**。设 $\gamma$ 为测地线，$X$ 为Killing场。则 $X|_\gamma$ 是沿 $\gamma$ 的Jacobi场。

**证明**：Killing场生成等距，等距将测地线映为测地线。故 $X$ 的变分是测地线变分，其变分向量场为Jacobi场。∎

---

## 3. 等距群

### 3.1 Myers-Steenrod定理

**定理 3.1（Myers-Steenrod, 1939）**。设 $M$ 为Riemann流形。则等距群 $\operatorname{Isom}(M)$ 在紧开拓扑下是Lie群，其Lie代数为Killing场的Lie代数 $\mathfrak{isom}(M)$。且 $\dim \operatorname{Isom}(M) \leq \frac{n(n+1)}{2}$（$n = \dim M$）。

**证明概要**：等距将测地线映为测地线，由测地线的解析性和初始条件唯一性，等距由一点处的值和微分完全决定。故等距群可嵌入到正交标架丛的某个子流形中，赋予流形结构。维数上界由Killing场的初值（$X_p$ 和 $\nabla X|_p$）决定：Killing方程和曲率关系限制了 $\nabla X|_p$ 的自由度至多为 $n(n-1)/2$，加上 $X_p$ 的 $n$ 维，总自由度 $\leq n + n(n-1)/2 = n(n+1)/2$。∎

### 3.2 最大对称空间

**定义 3.1**。若 $\dim \operatorname{Isom}(M) = n(n+1)/2$，称 $M$ 为 **最大对称的**（maximally symmetric）。

**定理 3.2**。常曲率空间是最大对称的。

**例 3.1**。$\mathbb{R}^n$ 的等距群为Euclid群 $E(n) = O(n) \ltimes \mathbb{R}^n$，$\dim = n(n-1)/2 + n = n(n+1)/2$。

**例 3.2**。$S^n$ 的等距群为 $O(n+1)$，$\dim = n(n+1)/2$。

**例 3.3**。双曲空间 $\mathbb{H}^n$ 的等距群为 $O^+(n,1)$，$\dim = n(n+1)/2$。

---

## 4. 对称空间

**定义 4.1**。Riemann流形 $M$ 称为（Riemann）**对称空间**，如果对每点 $p \in M$ 存在等距 $s_p: M \to M$（称为 **点反射** 或 **测地对称**），满足 $s_p(p) = p$ 且 $d(s_p)_p = -\operatorname{id}_{T_p M}$。

**定理 4.1**。对称空间满足：

1. 完备；
2. 等距群可递地作用在 $M$ 上；
3. 曲率张量平行：$\nabla R = 0$。

**证明概要**：由对称性，测地线可双向无限延伸（因 $s_p$ 翻转测地线方向），故完备。任意两点 $p, q$ 可用测地线连接，中点的点反射交换 $p, q$，故等距群可递。$\nabla R = 0$ 由对称性直接验证。∎

**分类**：不可约对称空间由E. Cartan完全分类，分为：

- **紧型**：如 $SU(n)/SO(n)$，$SO(p+q)/(SO(p)\times SO(q))$（Grassmann流形）；
- **非紧型**：如 $SL(n,\mathbb{R})/SO(n)$，双曲空间；
- **Euclid型**：如 $\mathbb{R}^n$。

---

## 5. 具体例子

### 例子 5.1：$\mathbb{R}^n$ 的Killing场

**定理 5.1**。$\mathbb{R}^n$（标准度量）的Killing场恰为
$$X(x) = Ax + b, \quad A^T = -A, \quad b \in \mathbb{R}^n.$$

**证明**：Killing方程 $\partial_i X_j + \partial_j X_i = 0$。令 $A_{ij} = \partial_i X_j$，则 $A_{ij} = -A_{ji}$。由Schwarz定理，$\partial_k A_{ij} = \partial_i \partial_k X_j = \partial_i A_{kj} = -\partial_i A_{jk} = -\partial_j A_{ik} = \partial_j A_{ki}$。轮换指标并求和得 $2\partial_k A_{ij} = 0$。故 $A_{ij}$ 为常数反对称矩阵，$X_j = A_{jk}x_k + b_j$。∎

### 例子 5.2：$S^n$ 的Killing场

**定理 5.2**。$S^n \subseteq \mathbb{R}^{n+1}$ 的Killing场由 $\mathbb{R}^{n+1}$ 的反对称线性映射诱导：对 $A^T = -A \in \mathfrak{so}(n+1)$，
$$X_A(p) = Ap \in T_p S^n \quad (p \in S^n \subseteq \mathbb{R}^{n+1}).$$

**验证**：流为 $\theta_t(p) = e^{tA}p$，$e^{tA} \in SO(n+1)$，故为等距。$\mathfrak{so}(n+1)$ 的维数 $n(n+1)/2$ 达到最大对称上界。

### 例子 5.3：$S^2$ 上的Killing场

$\mathfrak{so}(3)$ 的基可取为
$$A_1 = \begin{pmatrix} 0 & 0 & 0 \\ 0 & 0 & -1 \\ 0 & 1 & 0 \end{pmatrix}, \quad
A_2 = \begin{pmatrix} 0 & 0 & 1 \\ 0 & 0 & 0 \\ -1 & 0 & 0 \end{pmatrix}, \quad
A_3 = \begin{pmatrix} 0 & -1 & 0 \\ 1 & 0 & 0 \\ 0 & 0 & 0 \end{pmatrix}.$$

对应Killing场：$X_1 = (-x^3, x^2, 0)$ 等，即绕坐标轴的旋转生成元。这些场在球坐标 $(\theta, \varphi)$ 下：$X_3 = \partial_\varphi$（绕 $z$ 轴旋转），$X_1 = \sin\varphi \partial_\theta + \cot\theta \cos\varphi \partial_\varphi$。

---

## 6. 与已有文档的关联

- [02-切空间与切向量](02-切空间与切向量.md)：等距的切映射保持内积。
- [03-切丛与向量场](03-切丛与向量场.md)：Killing场作为特殊的向量场。
- [20-Lie群与Lie代数](20-Lie群与Lie代数.md)：等距群的Lie群与Lie代数结构。
- [11-测地线方程](11-测地线方程.md)：Killing场与测地线、Jacobi场的关系。
- [李群李代数基础](../../11-高级数学/李群李代数-基础.md)：对称空间的Lie代数分类。

---

## 参考文献

1. S. B. Myers, N. E. Steenrod, "The group of isometries of a Riemannian manifold", *Ann. of Math.*, 40:400–416, 1939.
2. S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry*, Vol. I-II, Wiley, 1963-1969.
3. J. M. Lee, *Riemannian Manifolds*, Springer, 1997. (Ch. 11)
4. B. O'Neill, *Semi-Riemannian Geometry*, Academic Press, 1983. (Ch. 9)

---

**适用**：docs/14-微分几何/
