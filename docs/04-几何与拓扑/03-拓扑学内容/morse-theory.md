---
title: 莫尔斯理论
msc_primary: 57

  - 57R70
  - 57A99
  - 58E05
processed_at: '2026-04-05'
references:
  textbooks:
    - id: munkres_top
      type: textbook
      title: Topology
      authors:
      - James R. Munkres
      publisher: Pearson
      edition: 2nd
      year: 2000
      isbn: 978-0131816299
      msc: 54-01
      chapters: 
      url: ~
    - id: lee_ism
      type: textbook
      title: Introduction to Smooth Manifolds
      authors:
      - John M. Lee
      publisher: Springer
      edition: 2nd
      year: 2012
      isbn: 978-1441999818
      msc: 58-01
      chapters: 
      url: ~
  databases:
    - id: nlab
      type: database
      name: nLab
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
      consulted_at: 2026-04-17
    - id: stacks_project
      type: database
      name: Stacks Project
      entry_url: "https://stacks.math.columbia.edu/tag/{tag}"
      consulted_at: 2026-04-17
    - id: zbmath
      type: database
      name: zbMATH Open
      entry_url: "https://zbmath.org/?q=an:{zb_id}"
      consulted_at: 2026-04-17
---
# 莫尔斯理论 / Morse Theory

**主题编号**: B.05.16
**创建日期**: 2026年4月4日
**最后更新**: 2026年4月4日
**国际对齐**: Milnor *Morse Theory* (1963), Matsumoto *An Introduction to Morse Theory* (2002)

---

## 目录 / Table of Contents

- [莫尔斯理论 / Morse Theory](#莫尔斯理论-morse-theory)
  - 目录 / Table of Contents
  - [1. 基础概念 / Basic Concepts](#1-基础概念-basic-concepts)
    - [1.1 莫尔斯函数 / Morse Functions](#11-莫尔斯函数-morse-functions)
    - [1.2 临界点的几何意义 / Geometric Meaning](#12-临界点的几何意义-geometric-meaning)
  - [2. 莫尔斯引理与局部结构 / Morse Lemma and Local Structure](#2-莫尔斯引理与局部结构-morse-lemma-and-local-structure)
    - [2.1 莫尔斯引理 / Morse Lemma](#21-莫尔斯引理-morse-lemma)
    - [2.2 梯度流 / Gradient Flow](#22-梯度流-gradient-flow)
  - [3. 胞腔分解与同调 / Cell Decomposition and Homology](#3-胞腔分解与同调-cell-decomposition-and-homology)
    - [3.1 胞腔分解 / Cell Decomposition](#31-胞腔分解-cell-decomposition)
    - [3.2 莫尔斯不等式 / Morse Inequalities](#32-莫尔斯不等式-morse-inequalities)
    - [3.3 莫尔斯同调 / Morse Homology](#33-莫尔斯同调-morse-homology)
  - [4. 核心定理 / Core Theorems](#4-核心定理-core-theorems)
    - [4.1 Reeb定理 / Reeb's Theorem](#41-reeb定理-reebs-theorem)
    - [4.2 Lusternik-Schnirelmann理论](#42-lusternik-schnirelmann理论)
    - [4.3 Morse-Bott理论 / Morse-Bott Theory](#43-morse-bott理论-morse-bott-theory)
  - [5. 实战问题 / Practical Problems](#5-实战问题-practical-problems)
    - [问题 1：环面的莫尔斯函数](#问题-1环面的莫尔斯函数)
    - [问题 2：射影空间的莫尔斯函数](#问题-2射影空间的莫尔斯函数)
    - [问题 3：计算球面的同调](#问题-3计算球面的同调)
    - [问题 4：证明紧流形的有限性](#问题-4证明紧流形的有限性)
    - [问题 5：莫尔斯不等式的应用](#问题-5莫尔斯不等式的应用)
  - [6. 参考文献 / References](#6-参考文献-references)
    - [经典教材 / Classic Textbooks](#经典教材-classic-textbooks)
    - [现代发展 / Modern Developments](#现代发展-modern-developments)
    - [应用专题 / Applications](#应用专题-applications)
    - [在线资源 / Online Resources](#在线资源-online-resources)

---

## 1. 基础概念 / Basic Concepts

### 1.1 莫尔斯函数 / Morse Functions

**定义 1.1.1**（Hessian 矩阵）
设 $M$ 是 $n$ 维光滑流形，$f: M \to \mathbb{R}$ 是光滑函数，$p \in M$ 是临界点（即 $df_p = 0$）。在局部坐标 $(x^1, \ldots, x^n)$ 下，**Hessian 矩阵**定义为：
$$H_f(p) = \left( \frac{\partial^2 f}{\partial x^i \partial x^j}(p) \right)_{1 \leq i,j \leq n}$$

**定义 1.1.2**（非退化临界点）
临界点 $p$ 称为**非退化**的（non-degenerate），若 Hessian 矩阵 $H_f(p)$ 非奇异。

**定义 1.1.3**（莫尔斯函数 / Morse Function）
光滑函数 $f: M \to \mathbb{R}$ 称为**莫尔斯函数**，若：

1. 所有临界点都是非退化的
2. 临界点都是孤立的

**定义 1.1.4**（指标 / Index）
非退化临界点 $p$ 的**指标**（index）是 Hessian 矩阵的负特征值个数，记作 $\text{ind}(p)$ 或 $\lambda(p)$。

**例 1.1.5**

- $f(x) = x^2$ 在 $x=0$ 有指标 0 的临界点（极小值）
- $f(x) = -x^2$ 在 $x=0$ 有指标 1 的临界点（极大值，1维）
- $f(x,y) = x^2 - y^2$ 在 $(0,0)$ 有指标 1 的临界点（鞍点）

### 1.2 临界点的几何意义 / Geometric Meaning

**定理 1.2.1**（临界点的拓扑意义）
设 $p$ 是莫尔斯函数 $f$ 的指标为 $\lambda$ 的临界点。当穿过临界点 $p$ 时，子水平集 $M^a = f^{-1}((-\infty, a])$ 的拓扑变化为：

- 附着（attaching）一个 $\lambda$-维手柄（handle）$D^\lambda \times D^{n-\lambda}$

---

## 2. 莫尔斯引理与局部结构 / Morse Lemma and Local Structure

### 2.1 莫尔斯引理 / Morse Lemma

**定理 2.1.1**（莫尔斯引理 / Morse Lemma）
设 $p$ 是 $f: M \to \mathbb{R}$ 的非退化临界点，指标为 $\lambda$。存在局部坐标 $(x^1, \ldots, x^n)$ 使得 $p = (0, \ldots, 0)$ 且：
$$f(x) = f(p) - (x^1)^2 - \cdots - (x^\lambda)^2 + (x^{\lambda+1})^2 + \cdots + (x^n)^2$$

**推论 2.1.2**

1. 非退化临界点是孤立的
2. 局部拓扑由指标完全决定

**定理 2.1.3**（莫尔斯函数的存在性）
任意紧致流形上都存在莫尔斯函数。

*证明概要*：利用 Sard 定理和嵌入手 $M \hookrightarrow \mathbb{R}^N$，对几乎所有 $v \in \mathbb{R}^N$，函数 $f_v(p) = \langle p, v \rangle$ 是莫尔斯函数。

### 2.2 梯度流 / Gradient Flow

**定义 2.2.1**（梯度流）
给定黎曼度量 $g$，函数 $f$ 的**梯度流**是向量场 $-\nabla f$ 的流，即微分方程：
$$\frac{d\gamma}{dt} = -\nabla f(\gamma(t))$$
的解。

**定义 2.2.2**（稳定流形与不稳定流形）
对临界点 $p$，定义：

- **稳定流形**：$W^s(p) = \{x \in M : \lim_{t \to +\infty} \phi_t(x) = p\}$
- **不稳定流形**：$W^u(p) = \{x \in M : \lim_{t \to -\infty} \phi_t(x) = p\}$

**定理 2.2.3**
$$\dim W^u(p) = \lambda(p), \quad \dim W^s(p) = n - \lambda(p)$$

---

## 3. 胞腔分解与同调 / Cell Decomposition and Homology

### 3.1 胞腔分解 / Cell Decomposition

**定理 3.1.1**（莫尔斯理论的基本定理）
设 $f: M \to \mathbb{R}$ 是莫尔斯函数，$a < b$ 不是临界值。设 $f^{-1}([a,b])$ 中恰有一个临界点 $p$，$f(p) = c$，$\lambda(p) = \lambda$。则：
$$M^b \simeq M^a \cup_{\partial D^\lambda} D^\lambda$$
即 $M^b$ 同伦等价于 $M^a$ 粘上一个 $\lambda$-维胞腔。

**推论 3.1.2**（CW 结构）
紧致流形 $M$ 同伦等价于一个 CW 复形，其 $k$-维胞腔对应指标为 $k$ 的临界点。

### 3.2 莫尔斯不等式 / Morse Inequalities

**定义 3.2.1**（莫尔斯数）
设 $c_k$ 为指标 $k$ 的临界点个数，$P_t(M) = \sum_{k=0}^n \dim H_k(M; \mathbb{R}) t^k$ 为 Poincaré 多项式。

**定理 3.2.2**（弱莫尔斯不等式）
对 $0 \leq k \leq n$：
$$c_k \geq b_k = \dim H_k(M; \mathbb{R})$$

**定理 3.2.3**（强莫尔斯不等式）
设 $M_t = \sum_{k=0}^n c_k t^k$ 为莫尔斯多项式，则：
$$M_t - P_t(M) = (1+t)R(t)$$
其中 $R(t)$ 是非负整系数多项式。

**推论 3.2.4**
$$\sum_{k=0}^n (-1)^k c_k = \chi(M)$$

### 3.3 莫尔斯同调 / Morse Homology

**定义 3.3.1**（莫尔斯复形）
设 $\text{Crit}_k(f)$ 为指标 $k$ 的临界点集合。定义链复形：
$$C_k^{\text{Morse}} = \mathbb{Z}\langle \text{Crit}_k(f) \rangle$$
边界算子 $\partial: C_k \to C_{k-1}$ 定义为：
$$\partial(p) = \sum_{q \in \text{Crit}_{k-1}} n(p,q) q$$
其中 $n(p,q)$ 是连接 $p$ 到 $q$ 的梯度流线模空间的计数。

**定理 3.3.2**（莫尔斯同调定理）
$$H_*^{\text{Morse}}(M, f) \cong H_*(M; \mathbb{Z})$$

---

## 4. 核心定理 / Core Theorems

### 4.1 Reeb定理 / Reeb's Theorem

**定理 4.1.1**（Reeb 定理）
设 $M$ 是紧致 $n$-流形，$f: M \to \mathbb{R}$ 是恰有两个临界点的莫尔斯函数，则 $M$ 同胚于 $S^n$。

**证明概要**：

1. 两临界点必为极小值（指标 0）和极大值（指标 $n$）
2. $M^a$ 对 $a$ 略大于极小值是一个 $n$-盘
3. 由莫尔斯理论，$M$ 是 $D^n$ 粘上一个 $n$-柄
4. 边界 $\partial D^n = S^{n-1}$ 的粘贴映射给出 $M \cong S^n$

### 4.2 Lusternik-Schnirelmann理论

**定义 4.2.1**（畴数 / Category）
空间 $X$ 的**Lusternik-Schnirelmann 畴数** $\text{cat}(X)$ 是覆盖 $X$ 所需可缩开集的最小个数。

**定理 4.2.2**（Lusternik-Schnirelmann 定理）
设 $M$ 是紧致流形，$f: M \to \mathbb{R}$ 光滑，则：
$$\#\{\text{临界点 of } f\} \geq \text{cat}(M) \geq \text{cuplength}(M) + 1$$

### 4.3 Morse-Bott理论 / Morse-Bott Theory

**定义 4.3.1**（Morse-Bott 函数）
光滑函数 $f: M \to \mathbb{R}$ 称为**Morse-Bott 函数**，若其临界集是子流形，且 Hessian 在法向非退化。

**定理 4.3.2**
Morse-Bott 理论将 Morse 理论推广到具有对称性的情况，如环路空间上的能量泛函。

---

## 5. 实战问题 / Practical Problems

### 问题 1：环面的莫尔斯函数

**问题**：构造环面 $T^2 = S^1 \times S^1$ 上的一个莫尔斯函数，计算其临界点并验证莫尔斯不等式。

**解答**：

1. **构造**：嵌入 $T^2 \subset \mathbb{R}^3$ 为标准环面，取高度函数 $f(x,y,z) = z$。

2. **临界点**：
   - 最底点：$p_1 = (0, 0, -1)$，指标 0（极小值）
   - 最顶点：$p_4 = (0, 0, 1)$，指标 2（极大值）
   - 两个鞍点：$p_2, p_3$ 在 "腰部"，指标 1

3. **验证**：
   - $c_0 = 1, c_1 = 2, c_2 = 1$
   - $H_0(T^2) = \mathbb{Z}, H_1(T^2) = \mathbb{Z}^2, H_2(T^2) = \mathbb{Z}$
   - $b_0 = 1, b_1 = 2, b_2 = 1$
   - 强莫尔斯不等式：$M_t = 1 + 2t + t^2 = P_t = (1+t)^2$（完美！）

### 问题 2：射影空间的莫尔斯函数

**问题**：证明 $\mathbb{R}P^n$ 上存在恰有 $n+1$ 个临界点的莫尔斯函数。

**解答**：

1. **构造**：考虑 $f([x_0 : \cdots : x_n]) = \sum_{i=0}^n i \cdot x_i^2 / \sum_{i=0}^n x_i^2$

2. **临界点**：
   - 在齐次坐标下，临界点满足 $\nabla f = 0$
   - 解为 $[1:0:\cdots:0], [0:1:0:\cdots:0], \ldots, [0:\cdots:0:1]$
   - 恰有 $n+1$ 个临界点

3. **指标**：
   - 在 $[0:\cdots:0:1:0:\cdots:0]$（1 在第 $k$ 位），指标为 $k$
   - 故 $c_k = 1$ 对所有 $k = 0, \ldots, n$

4. **验证**：
   - $H_k(\mathbb{R}P^n; \mathbb{Z}/2) = \mathbb{Z}/2$ 对 $0 \leq k \leq n$
   - 莫尔斯不等式取等

### 问题 3：计算球面的同调

**问题**：用莫尔斯理论计算 $S^n$ 的奇异同调群。

**解答**：

1. **莫尔斯函数**：高度函数 $f(x_0, \ldots, x_n) = x_n$ 有两个临界点
   - 南极：指标 0
   - 北极：指标 $n$

2. **胞腔分解**：
   - $M^a$（略大于极小值）$\simeq D^n$（一个点）
   - 穿过北极时粘上一个 $n$-胞腔
   - $S^n \simeq \text{pt} \cup D^n$

3. **同调计算**：
   - $C_0 = \mathbb{Z}, C_n = \mathbb{Z}$，其余 $C_k = 0$
   - 边界算子 $\partial = 0$（无中间维数）
   - $H_0(S^n) = \mathbb{Z}, H_n(S^n) = \mathbb{Z}$，其余为 0

### 问题 4：证明紧流形的有限性

**问题**：用莫尔斯理论证明：紧致流形上任意莫尔斯函数只有有限个临界点。

**解答**：

1. 由莫尔斯引理，非退化临界点是孤立的
2. 紧致集上离散点集必为有限集
3. 具体地，设 $M$ 紧致，$\{p_\alpha\}$ 为临界点集
4. 每点 $p_\alpha$ 有邻域 $U_\alpha$ 使得 $U_\alpha \cap \{p_\beta\} = \{p_\alpha\}$
5. $\{U_\alpha\}$ 是 $M$ 的开覆盖，存在有限子覆盖
6. 故临界点集有限 $\square$

### 问题 5：莫尔斯不等式的应用

**问题**：证明：若 $M$ 是紧致 $n$-维流形，且 $H_k(M) \neq 0$，则任意莫尔斯函数 $f: M \to \mathbb{R}$ 至少有 $b_k$ 个指标为 $k$ 的临界点。

**解答**：

1. 由弱莫尔斯不等式：$c_k \geq b_k = \dim H_k(M; \mathbb{R})$
2. 若 $H_k(M) \neq 0$，则 $b_k \geq 1$
3. 故 $c_k \geq 1$，即至少有一个指标为 $k$ 的临界点
4. 更强的结论：至少有 $b_k$ 个这样的临界点 $\square$

---

## 6. 参考文献 / References

### 经典教材 / Classic Textbooks

- Milnor, J. W. (1963). *Morse Theory*. Princeton University Press.
- Matsumoto, Y. (2002). *An Introduction to Morse Theory*. AMS.
- Nicolaescu, L. I. (2011). *An Invitation to Morse Theory*. 2nd Edition. Springer.

### 现代发展 / Modern Developments

- Witten, E. (1982). Supersymmetry and Morse Theory. *Journal of Differential Geometry*, 17(4), 661-692.
- Schwarz, M. (1993). *Morse Homology*. Birkhäuser.
- Audin, M., & Damian, M. (2014). *Morse Theory and Floer Homology*. Springer.

### 应用专题 / Applications

- Bott, R. (1982). Lectures on Morse Theory, Old and New. *Bulletin of the AMS*, 7(2), 331-358.
- Cohen, R. L. (1991). *Topics in Morse Theory*. Stanford University Notes.

### 在线资源 / Online Resources

- Milnor's Morse Theory (经典中的经典)
- nLab: Morse Theory
- Wikipedia: Morse Theory

---

**文档状态**: 莫尔斯理论文档创建完成
**内容范围**: 基础概念、核心定理、实战问题
**难度级别**: 研究生中级
