---
title: 纤维丛理论
msc_primary: 55R10
msc_secondary:
- 55A99
- 57R22
processed_at: '2026-04-05'
---
# 纤维丛理论 / Fiber Bundle Theory

**主题编号**: B.05.13
**创建日期**: 2026年4月4日
**最后更新**: 2026年4月4日
**国际对齐**: Steenrod *The Topology of Fiber Bundles* (1951), Husemoller *Fiber Bundles* (1994)

---

## 目录 / Table of Contents

- [纤维丛理论 / Fiber Bundle Theory](#纤维丛理论-fiber-bundle-theory)
  - 目录 / Table of Contents
  - [1. 基础概念 / Basic Concepts](#1-基础概念-basic-concepts)
    - [1.1 纤维丛的定义 / Definition of Fiber Bundles](#11-纤维丛的定义-definition-of-fiber-bundles)
    - [1.2 丛映射 / Bundle Maps](#12-丛映射-bundle-maps)
  - [2. 主丛与向量丛 / Principal and Vector Bundles](#2-主丛与向量丛-principal-and-vector-bundles)
    - [2.1 主丛 / Principal Bundles](#21-主丛-principal-bundles)
    - [2.2 向量丛 / Vector Bundles](#22-向量丛-vector-bundles)
    - [2.3 主丛与向量丛的关联 / Associated Bundles](#23-主丛与向量丛的关联-associated-bundles)
  - [3. 联络与曲率 / Connections and Curvature](#3-联络与曲率-connections-and-curvature)
    - [3.1 主丛上的联络 / Connections on Principal Bundles](#31-主丛上的联络-connections-on-principal-bundles)
    - [3.2 曲率 / Curvature](#32-曲率-curvature)
  - [4. 核心定理 / Core Theorems](#4-核心定理-core-theorems)
    - [4.1 同伦提升定理 / Homotopy Lifting Theorem](#41-同伦提升定理-homotopy-lifting-theorem)
    - [4.2 分类定理 / Classification Theorem](#42-分类定理-classification-theorem)
    - [4.3 存在性定理 / Existence Theorems](#43-存在性定理-existence-theorems)
  - [5. 实战问题 / Practical Problems](#5-实战问题-practical-problems)
    - [问题 1：霍普夫纤维化的验证](#问题-1霍普夫纤维化的验证)
    - [问题 2：切丛的平凡性判断](#问题-2切丛的平凡性判断)
    - [问题 3：Möbius 丛的转移函数](#问题-3möbius-丛的转移函数)
    - [问题 4：主丛的延拓](#问题-4主丛的延拓)
    - [问题 5：向量丛的 Whitney 和公式应用](#问题-5向量丛的-whitney-和公式应用)
  - [6. 参考文献 / References](#6-参考文献-references)
    - [经典教材 / Classic Textbooks](#经典教材-classic-textbooks)
    - [现代教材 / Modern Textbooks](#现代教材-modern-textbooks)
    - [物理应用 / Physics Applications](#物理应用-physics-applications)
    - [中文资源 / Chinese Resources](#中文资源-chinese-resources)

---

## 1. 基础概念 / Basic Concepts

### 1.1 纤维丛的定义 / Definition of Fiber Bundles

**定义 1.1.1**（纤维丛 / Fiber Bundle）
一个**纤维丛**（fiber bundle）是四元组 $(E, B, \pi, F)$，其中：

- $E$ 为**全空间**（total space）
- $B$ 为**底空间**（base space）
- $F$ 为**纤维**（fiber）
- $\pi: E \to B$ 为连续满射（**投影映射**），满足**局部平凡性**：

对每点 $b \in B$，存在邻域 $U \subseteq B$ 和同胚 $\phi: \pi^{-1}(U) \to U \times F$，使得下图交换：
$$\begin{array}{ccc}
\pi^{-1}(U) & \xrightarrow{\phi} & U \times F \\
\pi \downarrow & & \downarrow \text{pr}_1 \\
U & = & U
\end{array}$$

即 $\text{pr}_1 \circ \phi = \pi|_{\pi^{-1}(U)}$。

**定义 1.1.2**（平凡丛 / Trivial Bundle）
若 $E \cong B \times F$ 且 $\pi = \text{pr}_1$，则称 $(E, B, \pi, F)$ 为**平凡丛**。

**定义 1.1.3**（转移函数 / Transition Functions）
设 $\{U_\alpha\}$ 是 $B$ 的开覆盖，$\phi_\alpha: \pi^{-1}(U_\alpha) \to U_\alpha \times F$ 为局部平凡化。在 $U_\alpha \cap U_\beta$ 上定义：
$$g_{\alpha\beta}: U_\alpha \cap U_\beta \to \text{Homeo}(F)$$
$$g_{\alpha\beta}(b) = \phi_{\alpha,b} \circ \phi_{\beta,b}^{-1}: F \to F$$
其中 $\phi_{\alpha,b}: \pi^{-1}(b) \to F$ 是 $\phi_\alpha$ 在纤维上的限制。

**定理 1.1.1**（转移函数的性质）
转移函数满足**上循环条件**（cocycle condition）：
1. $g_{\alpha\alpha}(b) = \text{id}_F$
2. $g_{\alpha\beta}(b) = g_{\beta\alpha}(b)^{-1}$
3. $g_{\alpha\beta}(b) \circ g_{\beta\gamma}(b) \circ g_{\gamma\alpha}(b) = \text{id}_F$ 在 $U_\alpha \cap U_\beta \cap U_\gamma$ 上

### 1.2 丛映射 / Bundle Maps

**定义 1.2.1**（丛映射 / Bundle Map）
设 $(E, B, \pi, F)$ 和 $(E', B', \pi', F')$ 为纤维丛。一个**丛映射**是映射对 $(\tilde{f}, f)$，其中 $\tilde{f}: E \to E'$，$f: B \to B'$，使得下图交换：
$$\begin{array}{ccc}
E & \xrightarrow{\tilde{f}} & E' \\
\pi \downarrow & & \downarrow \pi' \\
B & \xrightarrow{f} & B'
\end{array}$$

**定义 1.2.2**（丛等价 / Bundle Equivalence）
若丛映射 $(\tilde{f}, f)$ 满足 $f = \text{id}_B$ 且 $\tilde{f}$ 是同胚，则称两丛**等价**。

---

## 2. 主丛与向量丛 / Principal and Vector Bundles

### 2.1 主丛 / Principal Bundles

**定义 2.1.1**（主 $G$-丛 / Principal $G$-Bundle）
设 $G$ 为拓扑群。纤维丛 $(P, B, \pi, G)$ 称为**主 $G$-丛**，若：
1. $G$ 在 $P$ 上有连续的**右作用** $P \times G \to P$
2. 该作用保持纤维：$\pi(p \cdot g) = \pi(p)$
3. 该作用在纤维上是**自由且可递的**
4. 局部平凡化 $\phi_\alpha: \pi^{-1}(U_\alpha) \to U_\alpha \times G$ 是**等变的**（equivariant）

**定理 2.1.1**（主丛的构造）
给定开覆盖 $\{U_\alpha\}$ 和转移函数 $g_{\alpha\beta}: U_\alpha \cap U_\beta \to G$ 满足上循环条件，可构造主 $G$-丛：
$$P = \left( \bigsqcup_\alpha U_\alpha \times G \right) / \sim$$
其中 $(b, g)_\alpha \sim (b, g_{\beta\alpha}(b) \cdot g)_\beta$ 对 $b \in U_\alpha \cap U_\beta$。

### 2.2 向量丛 / Vector Bundles

**定义 2.2.1**（实向量丛 / Real Vector Bundle）
纤维丛 $(E, B, \pi, \mathbb{R}^n)$ 称为**秩 $n$ 实向量丛**，若：
1. 每根纤维 $E_b = \pi^{-1}(b)$ 具有 $n$ 维实向量空间结构
2. 局部平凡化 $\phi_\alpha: \pi^{-1}(U_\alpha) \to U_\alpha \times \mathbb{R}^n$ 在纤维上是线性同构

**定义 2.2.2**（复向量丛 / Complex Vector Bundle）
将 $\mathbb{R}^n$ 替换为 $\mathbb{C}^n$，即得**秩 $n$ 复向量丛**的定义。

**例 2.2.3**
- **切丛** $TM$：$n$ 维流形 $M$ 的秩 $n$ 实向量丛
- **余切丛** $T^*M$：切丛的对偶丛
- **Möbius 丛**：$S^1$ 上非平凡的秩 1 实向量丛

### 2.3 主丛与向量丛的关联 / Associated Bundles

**定理 2.3.1**（相伴丛的构造）
设 $P$ 是主 $G$-丛，$F$ 是 $G$ 左作用的空间。定义：
$$E = P \times_G F = (P \times F) / G$$
其中 $(p \cdot g, f) \sim (p, g \cdot f)$。则 $(E, B, \pi_F, F)$ 是纤维丛，称为**相伴丛**。

**定理 2.3.2**
设 $\rho: G \to GL(V)$ 是群表示，则相伴丛 $P \times_\rho V$ 是向量丛。

**推论 2.3.3**
流形 $M$ 的切丛 $TM$ 可看作标架主丛 $FM$ 与表示 $\rho: GL(n, \mathbb{R}) \to GL(\mathbb{R}^n)$ 的相伴丛。

---

## 3. 联络与曲率 / Connections and Curvature

### 3.1 主丛上的联络 / Connections on Principal Bundles

**定义 3.1.1**（联络形式 / Connection Form）
设 $P$ 是主 $G$-丛，$\mathfrak{g}$ 为 $G$ 的 Lie 代数。$P$ 上的**联络**是 $\mathfrak{g}$-值 1-形式 $\omega \in \Omega^1(P; \mathfrak{g})$，满足：

1. **等变性**：$R_g^* \omega = \text{Ad}_{g^{-1}} \omega$（$R_g$ 为右作用）
2. **垂直条件**：对基本向量场 $A^*$（$A \in \mathfrak{g}$ 生成），$\omega(A^*) = A$

**定义 3.1.2**（水平分布 / Horizontal Distribution）
联络 $\omega$ 定义**水平分布** $H_p = \ker \omega_p \subseteq T_p P$。

### 3.2 曲率 / Curvature

**定义 3.2.1**（曲率形式 / Curvature Form）
联络 $\omega$ 的**曲率**定义为：
$$\Omega = d\omega + \frac{1}{2}[\omega \wedge \omega] \in \Omega^2(P; \mathfrak{g})$$

**定理 3.2.1**（Bianchi 恒等式）
$$d\Omega = [\Omega \wedge \omega]$$

**定理 3.2.2**（结构方程）
对水平向量场 $X, Y$：
$$\Omega(X, Y) = d\omega(X, Y) = -\omega([X, Y])$$

---

## 4. 核心定理 / Core Theorems

### 4.1 同伦提升定理 / Homotopy Lifting Theorem

**定理 4.1.1**（纤维化提升性质）
设 $p: E \to B$ 是纤维化，$f: X \to E$ 和 $H: X \times I \to B$ 满足 $H(-, 0) = p \circ f$。则存在提升 $\tilde{H}: X \times I \to E$ 使得 $p \circ \tilde{H} = H$ 且 $\tilde{H}(-, 0) = f$。

**推论 4.1.2**
纤维化的纤维在同伦意义下唯一确定。

### 4.2 分类定理 / Classification Theorem

**定理 4.2.1**（主丛的分类）
设 $G$ 为拓扑群，$EG \to BG$ 为万有主 $G$-丛（$EG$ 可缩）。则对 CW 复形 $B$：
$$\{\text{主 } G\text{-丛 over } B\} / \cong \xrightarrow{\cong} [B, BG]$$
映射由拉回给出：$f: B \to BG$ 对应 $f^* EG$。

**定理 4.2.2**（向量丛的分类）
实秩 $n$ 向量丛由 $[B, BO(n)]$ 分类，复秩 $n$ 向量丛由 $[B, BU(n)]$ 分类。

**例 4.2.3**
- $BU(1) = \mathbb{C}P^\infty$，线丛由第一陈类分类
- $BO(1) = \mathbb{R}P^\infty$，实线丛由第一 Stiefel-Whitney 类分类

### 4.3 存在性定理 / Existence Theorems

**定理 4.3.1**（联络的存在性）
主丛上的联络总是存在的。

*证明概要*：利用单位分解将局部定义的联络（如平凡丛上的平坦联络）拼接成全局联络。

**定理 4.3.2**（截面的存在性）
设 $E \to B$ 是向量丛，$\dim B = n$，$\text{rank } E = k$。若 $k > n$，则存在处处非零的截面。

---

## 5. 实战问题 / Practical Problems

### 问题 1：霍普夫纤维化的验证

**问题**：验证 Hopf 映射 $\eta: S^3 \to S^2$ 是纤维化，并确定其纤维。

**解答**：

1. **Hopf 映射的定义**：将 $S^3 \subset \mathbb{C}^2$ 通过 $(z_1, z_2) \mapsto [z_1 : z_2] \in \mathbb{C}P^1 \cong S^2$

2. **纤维的计算**：对 $[z_1 : z_2] \in \mathbb{C}P^1$，原像满足 $(z_1, z_2) = \lambda (w_1, w_2)$，$\lambda \in S^1 \subset \mathbb{C}$

3. **验证纤维化**：
   - 局部地，$S^2 = U_1 \cup U_2$，其中 $U_i = \{[z_1 : z_2] : z_i \neq 0\}$
   - 在 $U_1$ 上，$[z_1 : z_2] = [1 : z_2/z_1]$，映射 $\eta^{-1}(U_1) \to U_1 \times S^1$ 由 $(z_1, z_2) \mapsto ([1 : z_2/z_1], z_1/|z_1|)$ 给出
   - 同理构造 $U_2$ 上的平凡化

4. **结论**：Hopf 纤维化是纤维为 $S^1$ 的主 $U(1)$-丛。

### 问题 2：切丛的平凡性判断

**问题**：证明 $S^2$ 的切丛 $TS^2$ 是非平凡的。

**解答**：

**方法 1**（Euler 类）：
- 若 $TS^2$ 平凡，则 $e(TS^2) = 0 \in H^2(S^2; \mathbb{Z})$
- 但 $\langle e(TS^2), [S^2] \rangle = \chi(S^2) = 2 \neq 0$
- 矛盾，故 $TS^2$ 非平凡

**方法 2**（ hairy ball theorem）：
- 若 $TS^2$ 平凡，则存在处处非零的向量场
- 这与毛球定理矛盾

### 问题 3：Möbius 丛的转移函数

**问题**：计算 $S^1$ 上 Möbius 线丛的转移函数。

**解答**：

1. **开覆盖**：取 $U_1 = S^1 \setminus \{1\}$，$U_2 = S^1 \setminus \{-1\}$
2. **局部平凡化**：
   - 在 $U_1$ 上，丛平凡
   - 在 $U_2$ 上，丛平凡
3. **转移函数**：
   - $U_1 \cap U_2 = U_+ \cup U_-$（上半圆和下半圆）
   - 在 $U_+$ 上，$g_{12} = 1$
   - 在 $U_-$ 上，$g_{12} = -1$（Möbius 带的扭转）

### 问题 4：主丛的延拓

**问题**：设 $G$ 连通，$P \to B$ 是主 $G$-丛。证明若底空间 $B$ 单连通，则 $P$ 的任意截面可延拓到整个 $B$。

**解答**：

1. 主丛存在整体截面当且仅当它是平凡丛
2. 由分类理论，$[B, BG] = 0$ 当 $B$ 单连通（$BG$ 连通且 $\pi_1(BG) = \pi_0(G) = 0$）
3. 故任意主 $G$-丛在单连通底空间上是平凡的
4. 因此存在整体截面

### 问题 5：向量丛的 Whitney 和公式应用

**问题**：设 $E$ 是 $S^2$ 上的秩 2 实向量丛。若 $E$ 可分解为两个线丛的直和，证明 $E$ 是平凡丛。

**解答**：

1. $S^2$ 上的实线丛由 $w_1 \in H^1(S^2; \mathbb{Z}/2) = 0$ 分类
2. 故 $S^2$ 上任意实线丛平凡
3. 若 $E = L_1 \oplus L_2$，则 $L_1, L_2$ 都平凡
4. 因此 $E \cong \varepsilon^1 \oplus \varepsilon^1 = \varepsilon^2$ 是平凡丛 $\square$

---

## 6. 参考文献 / References

### 经典教材 / Classic Textbooks

- Steenrod, N. (1951). *The Topology of Fiber Bundles*. Princeton University Press.
- Husemoller, D. (1994). *Fiber Bundles*. 3rd Edition. Springer.
- Kobayashi, S., & Nomizu, K. (1963-1969). *Foundations of Differential Geometry*. 2 vols. Wiley.

### 现代教材 / Modern Textbooks

- Taubes, C. H. (2011). *Differential Geometry: Bundles, Connections, Metrics and Curvature*. Oxford University Press.
- Donaldson, S. K., & Kronheimer, P. B. (1990). *The Geometry of Four-Manifolds*. Oxford University Press.

### 物理应用 / Physics Applications

- Bleecker, D. (1981). *Gauge Theory and Variational Principles*. Addison-Wesley.
- Naber, G. L. (2011). *Topology, Geometry, and Gauge Fields: Foundations*. 2nd Edition. Springer.

### 中文资源 / Chinese Resources

- 陈省身, 陈维桓. (2001). *微分几何讲义*. 北京大学出版社.
- 徐森林, 薛春华. (2004). *微分流形*. 高等教育出版社.

---

**文档状态**: 纤维丛理论文档创建完成
**内容范围**: 基础概念、核心定理、实战问题
**难度级别**: 研究生中级
