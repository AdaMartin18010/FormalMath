---
title: "示性类入门"
msc_primary: 57

  - 57R20
msc_secondary: ["55R25", "55R40"]
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
# 示性类入门 / Introduction to Characteristic Classes

**主题编号**: B.05.14
**创建日期**: 2026年4月4日
**最后更新**: 2026年4月4日
**国际对齐**: Milnor-Stasheff *Characteristic Classes* (1974), Bott-Tu *Differential Forms in Algebraic Topology* (1982)

---

## 目录 / Table of Contents

- [示性类入门 / Introduction to Characteristic Classes](#示性类入门-introduction-to-characteristic-classes)
  - 目录 / Table of Contents
  - [1. 基础概念 / Basic Concepts](#1-基础概念-basic-concepts)
    - [1.1 示性类的直观理解 / Intuition](#11-示性类的直观理解-intuition)
    - [1.2 分裂原理 / Splitting Principle](#12-分裂原理-splitting-principle)
  - [2. Stiefel-Whitney 类 / Stiefel-Whitney Classes](#2-stiefel-whitney-类-stiefel-whitney-classes)
    - [2.1 公理化定义 / Axiomatic Definition](#21-公理化定义-axiomatic-definition)
    - [2.2 几何解释 / Geometric Interpretation](#22-几何解释-geometric-interpretation)
    - [2.3 计算方法 / Computation Methods](#23-计算方法-computation-methods)
  - [3. Chern 类与 Pontryagin 类 / Chern and Pontryagin Classes](#3-chern-类与-pontryagin-类-chern-and-pontryagin-classes)
    - [3.1 Chern 类 / Chern Classes](#31-chern-类-chern-classes)
    - [3.2 Pontryagin 类 / Pontryagin Classes](#32-pontryagin-类-pontryagin-classes)
  - [4. Euler 类 / Euler Class](#4-euler-类-euler-class)
    - [4.1 定义与性质 / Definition and Properties](#41-定义与性质-definition-and-properties)
  - [5. 核心定理 / Core Theorems](#5-核心定理-core-theorems)
    - [5.1 示性数与配边 / Characteristic Numbers and Cobordism](#51-示性数与配边-characteristic-numbers-and-cobordism)
    - [5.2 Hirzebruch 符号差定理 / Hirzebruch Signature Theorem](#52-hirzebruch-符号差定理-hirzebruch-signature-theorem)
    - [5.3 分裂原理的形式化 / Splitting Principle Formalized](#53-分裂原理的形式化-splitting-principle-formalized)
  - [6. 实战问题 / Practical Problems](#6-实战问题-practical-problems)
    - [问题 1：计算 $TS^2$ 的 Euler 类](#问题-1计算-ts2-的-euler-类)
    - [问题 2：实射影空间的 Stiefel-Whitney 类](#问题-2实射影空间的-stiefel-whitney-类)
    - [问题 3：复线丛的分类](#问题-3复线丛的分类)
    - [问题 4：Pontryagin 类的计算](#问题-4pontryagin-类的计算)
    - [问题 5：示性类的乘积公式](#问题-5示性类的乘积公式)
  - [7. 参考文献 / References](#7-参考文献-references)
    - [经典教材 / Classic Textbooks](#经典教材-classic-textbooks)
    - [专题著作 / Monographs](#专题著作-monographs)
    - [在线资源 / Online Resources](#在线资源-online-resources)

---

## 1. 基础概念 / Basic Concepts

### 1.1 示性类的直观理解 / Intuition

**定义 1.1.1**（示性类 / Characteristic Class）
**示性类**是从向量丛（或主丛）的等价类到底空间上同调群的**自然变换**。具体地，对每类示性类 $c$，赋予每个向量丛 $E \to B$ 一个上同调类 $c(E) \in H^*(B; R)$（$R$ 为系数环），满足：

1. **自然性**（Naturality）：对映射 $f: B' \to B$，
   $$c(f^*E) = f^*c(E)$$

2. **Whitney 和公式**：对丛的直和，
   $$c(E \oplus F) = c(E) \smile c(F)$$

**定理 1.1.1**（示性类的存在唯一性）
满足上述公理的示性类（带规范性条件）存在且唯一。

### 1.2 分裂原理 / Splitting Principle

**定理 1.2.1**（分裂原理）
设 $E \to B$ 是秩 $n$ 复向量丛。存在映射 $f: F(E) \to B$ 使得：

1. $f^*E \cong L_1 \oplus L_2 \oplus \cdots \oplus L_n$（线丛的直和）
2. $f^*: H^*(B) \hookrightarrow H^*(F(E))$ 是单射

**推论 1.2.2**
要验证关于示性类的公式，只需验证其在线丛直和上成立。

---

## 2. Stiefel-Whitney 类 / Stiefel-Whitney Classes

### 2.1 公理化定义 / Axiomatic Definition

**定理/定义 2.1.1**（Stiefel-Whitney 类）
对每个实向量丛 $E \to B$，存在唯一的类 $w_i(E) \in H^i(B; \mathbb{Z}/2)$，满足：

**公理 (SW1)**（维度）：$w_0(E) = 1$，$w_i(E) = 0$ 对 $i > \text{rank}(E)$

**公理 (SW2)**（自然性）：$w_i(f^*E) = f^*w_i(E)$

**公理 (SW3)**（Whitney 和）：$w(E \oplus F) = w(E) \smile w(F)$，其中 $w(E) = \sum w_i(E)$ 为**全 Stiefel-Whitney 类**

**公理 (SW4)**（规范性）：对 tautological 线丛 $\gamma^1 \to \mathbb{R}P^1$，$w_1(\gamma^1) \neq 0$

### 2.2 几何解释 / Geometric Interpretation

**定理 2.2.1**（可定向性判据）
实向量丛 $E$ 可定向当且仅当 $w_1(E) = 0$。

**定理 2.2.2**（Spin 结构判据）
设 $M$ 是可定向流形，$M$ 有 spin 结构当且仅当 $w_2(TM) = 0$。

### 2.3 计算方法 / Computation Methods

**定理 2.3.1**（乘积公式）
设 $E$ 和 $F$ 是实向量丛，则：
$$w_k(E \oplus F) = \sum_{i+j=k} w_i(E) \smile w_j(F)$$

**定理 2.3.2**（实射影空间的切丛）
$$w(T\mathbb{R}P^n) = (1 + a)^{n+1}$$
其中 $a \in H^1(\mathbb{R}P^n; \mathbb{Z}/2)$ 是生成元。

**例 2.3.3**

- $w_1(T\mathbb{R}P^n) = (n+1)a$，故 $\mathbb{R}P^n$ 可定向当且仅当 $n$ 为奇数
- $w(TS^n) = 1$（球面的切丛是稳定平凡的）

---

## 3. Chern 类与 Pontryagin 类 / Chern and Pontryagin Classes

### 3.1 Chern 类 / Chern Classes

**定理/定义 3.1.1**（Chern 类）
对每个复向量丛 $E \to B$，存在唯一的类 $c_i(E) \in H^{2i}(B; \mathbb{Z})$，满足类似于 Stiefel-Whitney 类的公理，其中规范性条件为：

对 tautological 线丛 $\gamma^1 \to \mathbb{C}P^1$，$c_1(\gamma^1)$ 是 $H^2(\mathbb{C}P^1; \mathbb{Z}) \cong \mathbb{Z}$ 的生成元。

**定理 3.1.2**（复射影空间的切丛）
$$c(T\mathbb{C}P^n) = (1 + \alpha)^{n+1}$$
其中 $\alpha \in H^2(\mathbb{C}P^n; \mathbb{Z})$ 是生成元。

**推论 3.1.3**
$$c_k(T\mathbb{C}P^n) = \binom{n+1}{k} \alpha^k$$

### 3.2 Pontryagin 类 / Pontryagin Classes

**定义 3.2.1**（Pontryagin 类）
设 $E$ 为实向量丛，其**复化丛** $E \otimes_\mathbb{R} \mathbb{C}$ 是复向量丛。定义第 $k$ 个 Pontryagin 类：
$$p_k(E) = (-1)^k c_{2k}(E \otimes \mathbb{C}) \in H^{4k}(B; \mathbb{Z})$$

**定理 3.2.2**（Pontryagin 类的性质）

1. $p_k(E) = 0$ 对 $4k > 2 \cdot \text{rank}(E)$
2. 满足自然性和 Whitney 和公式（在适当系数下）
3. $p(E \oplus \varepsilon^k) = p(E)$（稳定性）

---

## 4. Euler 类 / Euler Class

### 4.1 定义与性质 / Definition and Properties

**定义 4.1.1**（Euler 类）
设 $E \to B$ 是秩 $n$ 可定向实向量丛。**Euler 类** $e(E) \in H^n(B; \mathbb{Z})$ 定义如下：

设 $E_0$ 为 $E$ 的零截面补，则 Thom 同构给出：
$$H^n(B) \xrightarrow{\cong} H^{2n}(E, E_0)$$
Euler 类是零截面的自交类。

**定理 4.1.2**（Euler 类的性质）

1. $e(E) = 0$ 当且仅当 $E$ 存在处处非零截面（适当条件下）
2. 对定向流形 $M$，$\langle e(TM), [M] \rangle = \chi(M)$（Euler 示性数）
3. $e(E \oplus F) = e(E) \smile e(F)$

**定理 4.1.3**（Poincaré-Hopf 定理）
设 $M$ 是紧致定向流形，$V$ 是其上具有孤立零点的向量场，则：
$$\sum_{p \in \text{Zero}(V)} \text{ind}_p(V) = \chi(M) = \langle e(TM), [M] \rangle$$

---

## 5. 核心定理 / Core Theorems

### 5.1 示性数与配边 / Characteristic Numbers and Cobordism

**定义 5.1.1**（示性数 / Characteristic Numbers）
设 $M$ 是 $4k$ 维闭定向流形，$P$ 是 Pontryagin 类的 $k$ 次齐次多项式。定义**Pontryagin 数**：
$$P[M] = \langle P(p_1(TM), \ldots, p_k(TM)), [M] \rangle \in \mathbb{Z}$$

**定理 5.1.2**（Thom-Pontryagin 配边定理）
两个闭定向流形 $M, N$ 是**定向配边**的（oriented cobordant）当且仅当它们的所有 Pontryagin 数和 Stiefel-Whitney 数都相等。

### 5.2 Hirzebruch 符号差定理 / Hirzebruch Signature Theorem

**定义 5.2.1**（符号差 / Signature）
对 $4k$ 维闭定向流形 $M$， cup 积在 $H^{2k}(M; \mathbb{R})$ 上定义对称双线性型。其**符号差** $\sigma(M)$ 是正特征值个数减负特征值个数。

**定理 5.2.2**（Hirzebruch 符号差定理）
$$\sigma(M) = \langle L_k(p_1, \ldots, p_k), [M] \rangle$$
其中 $L_k$ 是 Hirzebruch $L$-多项式。

**例 5.2.3**

- $\dim M = 4$：$\sigma(M) = \frac{1}{3} p_1[M]$
- $\dim M = 8$：$\sigma(M) = \frac{1}{45}(7p_2 - p_1^2)[M]$

### 5.3 分裂原理的形式化 / Splitting Principle Formalized

**定理 5.3.1**
设 $c$ 是满足自然性和 Whitney 和公理的示性类。若对任意线丛 $L$，$c(L) = 1 + f(c_1(L))$ 对某形式幂级数 $f$，则：
$$c(E) = \prod_{i=1}^n (1 + f(x_i))$$
其中 $x_i$ 是形式 Chern 根，即 $c(E) = \prod_{i=1}^n (1 + x_i)$。

---

## 6. 实战问题 / Practical Problems

### 问题 1：计算 $TS^2$ 的 Euler 类

**问题**：计算 $S^2$ 的切丛的 Euler 类，并验证 Poincaré-Hopf 定理。

**解答**：

1. 由 Gauss-Bonnet 定理，$\langle e(TS^2), [S^2] \rangle = \chi(S^2) = 2$

2. 具体计算：
   - $TS^2 \oplus \varepsilon^1 = \varepsilon^3$（球面的法丛是平凡的）
   - $e(TS^2 \oplus \varepsilon^1) = e(TS^2) \smile e(\varepsilon^1) = 0$（平凡丛的 Euler 类为零）
   - 这似乎矛盾，需注意 Euler 类仅对定向丛定义

3. **正确计算**：
   - $S^2$ 作为 $\mathbb{C}P^1$，$TS^2$ 有复结构
   - $c_1(TS^2) = c_1(T\mathbb{C}P^1) = 3\alpha$？不对
   - 实际上 $T\mathbb{C}P^1 \cong \gamma^* \otimes \gamma^* = \mathcal{O}(2)$
   - $c_1(TS^2) = 2\alpha$，$e(TS^2) = c_1(TS^2) = 2\alpha$
   - $\langle 2\alpha, [S^2] \rangle = 2$ $\square$

### 问题 2：实射影空间的 Stiefel-Whitney 类

**问题**：证明 $\mathbb{R}P^n$ 可嵌入 $\mathbb{R}^{2n-1}$ 当 $n$ 不是 2 的幂次时是不可能的。

**解答**：

1. 由 Whitney 嵌入定理，$n$ 维流形可嵌入 $\mathbb{R}^{2n}$
2. 若 $M^n \hookrightarrow \mathbb{R}^{n+k}$，则法丛 $\nu$ 满足 $TM \oplus \nu = \varepsilon^{n+k}$
3. 对 $\mathbb{R}P^n \hookrightarrow \mathbb{R}^{2n-1}$，法丛秩为 $n-1$
4. 计算 $w(T\mathbb{R}P^n) = (1+a)^{n+1}$
5. 由 $w(TM) \smile w(\nu) = 1$，得 $w(\nu) = (1+a)^{-(n+1)} = (1+a)^{2^m - (n+1)}$（当 $2^m > n+1$）
6. 若 $n+1$ 不是 2 的幂，则 $w(\nu)$ 在次数 $\leq n-1$ 处有非零项，矛盾

### 问题 3：复线丛的分类

**问题**：证明 $S^2$ 上的复线丛由整数 $k \in \mathbb{Z}$ 完全分类，对应 $c_1 = k\alpha$。

**解答**：

1. 复线丛由 $[B, BU(1)] = [B, \mathbb{C}P^\infty]$ 分类
2. $[S^2, \mathbb{C}P^\infty] = \pi_2(\mathbb{C}P^\infty) = \mathbb{Z}$
3. 分类映射 $f_k: S^2 \to \mathbb{C}P^\infty$ 对应 $f_k^*(\gamma^1) = L_k$
4. $c_1(L_k) = f_k^*(c_1(\gamma^1)) = k\alpha$（通过 Hurewicz 同态和第一陈类的万有性）
5. 故 $L_k \cong L_{k'}$ 当且仅当 $k = k'$ $\square$

### 问题 4：Pontryagin 类的计算

**问题**：计算 $\mathbb{C}P^2$ 的切丛的 Pontryagin 类。

**解答**：

1. 复向量丛的 Pontryagin 类：$p_k(E) = (-1)^k c_{2k}(E_\mathbb{C})$
2. 对复流形，$T_\mathbb{R}M \otimes \mathbb{C} = T^{1,0}M \oplus T^{0,1}M = T^{1,0}M \oplus \overline{T^{1,0}M}$
3. 对 $\mathbb{C}P^2$，$c(T\mathbb{C}P^2) = (1+\alpha)^3 = 1 + 3\alpha + 3\alpha^2$
4. $p_1(T\mathbb{C}P^2) = c_1^2 - 2c_2 = 9\alpha^2 - 6\alpha^2 = 3\alpha^2$
5. 故 $p_1[T\mathbb{C}P^2] = \langle 3\alpha^2, [\mathbb{C}P^2] \rangle = 3$ $\square$

### 问题 5：示性类的乘积公式

**问题**：设 $E$ 是秩 $m$ 复向量丛，$F$ 是秩 $n$ 复向量丛。证明 $c(E \otimes F)$ 可用 $c(E)$ 和 $c(F)$ 的分裂原理表达。

**解答**：

1. 由分裂原理，设 $E = L_1 \oplus \cdots \oplus L_m$，$F = M_1 \oplus \cdots \oplus M_n$
2. 则 $E \otimes F = \bigoplus_{i,j} L_i \otimes M_j$
3. $c(E \otimes F) = \prod_{i,j} (1 + x_i + y_j)$，其中 $c(L_i) = 1 + x_i$，$c(M_j) = 1 + y_j$
4. 展开得：$c_k(E \otimes F) = \sigma_k(x_i + y_j)$（$k$ 次初等对称函数）
5. 用 Newton 恒等式可表示为 $c_i(E)$ 和 $c_j(F)$ 的多项式 $\square$

---

## 7. 参考文献 / References

### 经典教材 / Classic Textbooks

- Milnor, J. W., & Stasheff, J. D. (1974). *Characteristic Classes*. Princeton University Press.
- Bott, R., & Tu, L. W. (1982). *Differential Forms in Algebraic Topology*. Springer.
- Hatcher, A. (2003). *Vector Bundles and K-Theory* (Notes). Available online.

### 专题著作 / Monographs

- Hirzebruch, F. (1966). *Topological Methods in Algebraic Geometry*. Springer.
- Shanahan, P. (1978). *The Atiyah-Singer Index Theorem*. Springer.

### 在线资源 / Online Resources

- Hatcher's Vector Bundles and K-Theory: <https://pi.math.cornell.edu/~hatcher/VBKT/VB.pdf[需更新[需更新]]>
- nLab: Characteristic Class
- Wikipedia: Characteristic Class

---

**文档状态**: 示性类入门文档创建完成
**内容范围**: 基础概念、核心定理、实战问题
**难度级别**: 研究生中级
