---
msc_primary: 97A99
msc_secondary:
  - 00A99
---

# Oxford 表示论课程深度内容

Oxford 数学系 Part B 的表示论课程涵盖有限群表示、特征标理论、Lie 代数表示与代数群表示等核心主题。本节从课程框架出发，提供严格的数学内容，包括核心定义、定理证明与典型例子。

## 1. 有限群表示论

### 1.1 表示与模的对应

**定义 1.1（群表示）**. 群 $G$ 在域 $\mathbb{F}$ 上的表示是群同态 $\rho: G \to GL(V)$，$V$ 为 $\mathbb{F}$-向量空间。

**定理 1.2（表示 = 模）**. $G$ 的表示等价于群代数 $\mathbb{F}[G]$ 上的左模。

*证明*. 给定表示 $(\rho, V)$，定义 $\mathbb{F}[G]$-模结构：$g \cdot v = \rho(g)v$，线性延拓。反之，给定模 $V$，定义 $\rho(g)(v) = g \cdot v$。$\square$

### 1.2 完全可约性

**定理 1.3（Maschke）**. 设 $\operatorname{char}\mathbb{F} \nmid |G|$。则 $G$ 的每个有限维表示完全可约。

*证明*. 对不变子空间 $W \subset V$，取投影 $P: V \to W$，定义 $\tilde{P} = \frac{1}{|G|}\sum_g \rho(g)P\rho(g)^{-1}$。则 $\tilde{P}$ 为 $G$-等变投影，$\ker\tilde{P}$ 为不变补空间。$\square$

## 2. 特征标理论与正交关系

### 2.1 特征标表

**定理 2.1（Schur 正交关系）**. 设 $\chi_1, \dots, \chi_r$ 为 $G$ 的互不等价不可约复表示的特征标。则：

$$\frac{1}{|G|}\sum_{g \in G} \overline{\chi_i(g)}\chi_j(g) = \delta_{ij}.$$

**推论 2.2**. 不可约复表示个数 = 共轭类个数。

### 2.2 诱导表示

**定理 2.3（Frobenius 互反）**. 设 $H \leq G$，$\sigma$ 为 $H$ 的表示，$\rho$ 为 $G$ 的表示。则：

$$\operatorname{Hom}_G(\rho, \operatorname{Ind}_H^G \sigma) \cong \operatorname{Hom}_H(\operatorname{Res}_H^G \rho, \sigma).$$

## 3. Lie 代数表示

### 3.1 半单 Lie 代数的分类

**定义 3.1（半单 Lie 代数）**. Lie 代数 $\mathfrak{g}$ 称为半单的，若其无非零可解理想，等价于 Killing 型 $\kappa(X, Y) = \operatorname{tr}(\operatorname{ad}_X \circ \operatorname{ad}_Y)$ 非退化。

**定理 3.2（Cartan 分类）**. 复半单 Lie 代数由 Dynkin 图分类：$A_n, B_n, C_n, D_n$（经典型）和 $E_6, E_7, E_8, F_4, G_2$（例外型）。

### 3.2 最高权理论

**定义 3.3（最高权）**. 对表示 $V$ 和 Cartan 子代数 $\mathfrak{h}$，权 $\lambda \in \mathfrak{h}^*$ 满足 $V_\lambda = \{v \in V : Hv = \lambda(H)v, \forall H \in \mathfrak{h}\} \neq 0$。最高权在正根下极大。

**定理 3.4（最高权定理）**. 对半单 Lie 代数的支配整权 $\lambda$，存在唯一的有限维不可约表示 $V(\lambda)$ 以 $\lambda$ 为最高权。

## 4. 例子

### 4.1 例子：$\mathfrak{sl}(2, \mathbb{C})$ 的表示

$\mathfrak{sl}(2, \mathbb{C})$ 的基 $H = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$，$E = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$，$F = \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix}$，满足 $[H, E] = 2E$，$[H, F] = -2F$，$[E, F] = H$。

不可约表示 $V(m)$：维数 $m+1$，基 $v_0, \dots, v_m$，$Hv_k = (m-2k)v_k$，$Ev_k = (m-k+1)v_{k-1}$，$Fv_k = (k+1)v_{k+1}$。

### 4.2 例子：$S_4$ 的特征标表

$S_4$ 有 5 个共轭类：$1$，$(12)$，$(123)$，$(1234)$，$(12)(34)$。

| 类 | 1 | (12) | (123) | (1234) | (12)(34) |
|---|---|---|---|---|---|
| $\chi_1$ (trivial) | 1 | 1 | 1 | 1 | 1 |
| $\chi_2$ (sign) | 1 | -1 | 1 | -1 | 1 |
| $\chi_3$ (standard) | 3 | 1 | 0 | -1 | -1 |
| $\chi_4 = \chi_2 \otimes \chi_3$ | 3 | -1 | 0 | 1 | -1 |
| $\chi_5$ | 2 | 0 | -1 | 0 | 2 |

验证：$\chi_5$ 来自 $S_4 \to S_3$（作用在三个对换上），$S_3$ 的标准表示提升。维数公式：$1^2 + 1^2 + 3^2 + 3^2 + 2^2 = 24 = |S_4|$。

## 5. 交叉引用

- [表示论基础](docs/02-代数结构/02-核心理论/表示论-基础.md) — 有限群表示系统理论
- [李代数](docs/02-代数结构/02-核心理论/李代数/01-李代数基础.md) — Lie 代数结构与分类
- [代数群](docs/02-代数结构/02-核心理论/代数群/01-代数群基础.md) — 代数群与表示
- [特征标理论](docs/02-代数结构/02-核心理论/表示论深化/02-特征标理论-深度版.md) — 更深入的计算技巧

---

**适用**：docs/04-International-Alignment/
