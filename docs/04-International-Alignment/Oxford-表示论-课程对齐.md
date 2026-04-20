---
msc_primary: 20C99
msc_secondary:
  - 20G05
  - 17B10
  - 22E47
---

# Oxford 表示论课程深度内容

Oxford 数学系 Part B 的表示论课程涵盖有限群表示、特征标理论、Lie 代数表示与代数群表示等核心主题。本节从课程框架出发，提供严格的数学内容，包括核心定义、定理证明与典型例子。

## 1. 有限群表示论

### 1.1 表示与模的对应

**定义 1.1（群表示）**. 群 $G$ 在域 $\mathbb{F}$ 上的表示是群同态 $\rho: G \to GL(V)$，其中 $V$ 为 $\mathbb{F}$-向量空间。$V$ 的维数称为表示的维数或次数。

**定理 1.2（表示 = 模）**. $G$ 的表示等价于群代数 $\mathbb{F}[G]$ 上的左模。

*证明*. 给定表示 $(\rho, V)$，定义 $\mathbb{F}[G]$-模结构：$g \cdot v = \rho(g)v$，线性延拓至整个群代数。反之，给定模 $V$，定义 $\rho(g)(v) = g \cdot v$。验证这是群同态：$\rho(gh)(v) = (gh) \cdot v = g \cdot (h \cdot v) = \rho(g)\rho(h)(v)$。$\square$

### 1.2 完全可约性

**定理 1.3（Maschke）**. 设 $\operatorname{char}\mathbb{F} \nmid |G|$。则 $G$ 的每个有限维表示完全可约，即任何子表示都有补子表示。

*证明*. 对不变子空间 $W \subset V$，取任意投影 $P: V \to W$，定义平均投影
$$\tilde{P} = \frac{1}{|G|}\sum_{g \in G} \rho(g)P\rho(g)^{-1}.$$
则 $\tilde{P}$ 为 $G$-等变投影：对 $h \in G$，
$$\rho(h)\tilde{P}\rho(h)^{-1} = \frac{1}{|G|}\sum_g \rho(hg)P\rho(hg)^{-1} = \tilde{P}.$$
故 $\ker\tilde{P}$ 为不变补空间，$V = W \oplus \ker\tilde{P}$。$\square$

**推论 1.4**. 在 Maschke 条件下，$G$ 的每个有限维表示可分解为不可约表示的直和。

## 2. 特征标理论与正交关系

### 2.1 特征标表

**定义 2.1（特征标）**. 表示 $\rho$ 的特征标为 $\chi_\rho(g) = \operatorname{tr}\rho(g)$。特征标是类函数：在共轭类上为常值。

**定理 2.2（Schur 正交关系）**. 设 $\chi_1, \dots, \chi_r$ 为 $G$ 的互不等价不可约复表示的特征标。则：

$$\frac{1}{|G|}\sum_{g \in G} \overline{\chi_i(g)}\chi_j(g) = \delta_{ij}.$$

*证明概要*. 对不可约表示 $V_i, V_j$，由 Schur 引理，$\operatorname{Hom}_G(V_i, V_j)$ 的维数为 $\delta_{ij}$。将 $\operatorname{Hom}(V_i, V_j)$ 视为 $G$-表示，其不变子空间维数等于平均迹。$\square$

**推论 2.3**. 不可约复表示个数 = 共轭类个数。

*证明*. 类函数空间维数为共轭类数。由 Schur 正交关系，不可约特征标构成类函数空间的标准正交基。$\square$

### 2.2 诱导表示

**定义 2.4（诱导表示）**. 设 $H \leq G$，$\sigma$ 为 $H$ 的表示。诱导表示 $\operatorname{Ind}_H^G \sigma$ 为
$$\mathbb{F}[G] \otimes_{\mathbb{F}[H]} V_\sigma,$$
或等价地，为满足 $f(hg) = \sigma(h)f(g)$ 的函数 $f: G \to V_\sigma$ 组成的空间。

**定理 2.5（Frobenius 互反）**. 设 $H \leq G$，$\sigma$ 为 $H$ 的表示，$\rho$ 为 $G$ 的表示。则：

$$\operatorname{Hom}_G(\rho, \operatorname{Ind}_H^G \sigma) \cong \operatorname{Hom}_H(\operatorname{Res}_H^G \rho, \sigma).$$

## 3. Lie 代数表示

### 3.1 半单 Lie 代数的分类

**定义 3.1（半单 Lie 代数）**. Lie 代数 $\mathfrak{g}$ 称为半单的，若其无非零可解理想。等价地，Killing 型
$$\kappa(X, Y) = \operatorname{tr}(\operatorname{ad}_X \circ \operatorname{ad}_Y)$$
非退化（Cartan 判别准则）。

**定理 3.2（Cartan 分类）**. 复半单 Lie 代数由 Dynkin 图分类：

- 经典型：$A_n\ (n \geq 1), B_n\ (n \geq 2), C_n\ (n \geq 3), D_n\ (n \geq 4)$；
- 例外型：$E_6, E_7, E_8, F_4, G_2$。

### 3.2 最高权理论

**定义 3.3（权与最高权）**. 对表示 $V$ 和 Cartan 子代数 $\mathfrak{h}$，权 $\lambda \in \mathfrak{h}^*$ 满足权空间
$$V_\lambda = \{v \in V : Hv = \lambda(H)v, \forall H \in \mathfrak{h}\} \neq 0.$$
最高权在正根下极大：对正根 $\alpha$，$\lambda + \alpha$ 不是权。

**定理 3.4（最高权定理）**. 对半单 Lie 代数的支配整权 $\lambda$，存在唯一的有限维不可约表示 $V(\lambda)$ 以 $\lambda$ 为最高权。任何有限维不可约表示均如此得到。

*证明概要*. 先构造 Verma 模 $M(\lambda) = U(\mathfrak{g}) \otimes_{U(\mathfrak{b})} \mathbb{C}_\lambda$，再取其唯一极大真子模的商。$\square$

## 4. 典型例子

### 4.1 $\mathfrak{sl}(2, \mathbb{C})$ 的表示

$\mathfrak{sl}(2, \mathbb{C})$ 的基可取为
$$H = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}, \quad E = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}, \quad F = \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix},$$
满足 $[H, E] = 2E$，$[H, F] = -2F$，$[E, F] = H$。

不可约表示 $V(m)$（$m \geq 0$）：维数 $m+1$，基 $v_0, \dots, v_m$，作用为
$$Hv_k = (m-2k)v_k, \quad Ev_k = (m-k+1)v_{k-1}, \quad Fv_k = (k+1)v_{k+1}.$$
最高权为 $m$，对应最高权向量 $v_0$。

### 4.2 $S_4$ 的特征标表

$S_4$ 有 5 个共轭类：$1$，$(12)$，$(123)$，$(1234)$，$(12)(34)$。

| 类 | 1 | (12) | (123) | (1234) | (12)(34) |
|---|---|---|---|---|---|
| $\chi_1$ (trivial) | 1 | 1 | 1 | 1 | 1 |
| $\chi_2$ (sign) | 1 | -1 | 1 | -1 | 1 |
| $\chi_3$ (standard) | 3 | 1 | 0 | -1 | -1 |
| $\chi_4 = \chi_2 \otimes \chi_3$ | 3 | -1 | 0 | 1 | -1 |
| $\chi_5$ | 2 | 0 | -1 | 0 | 2 |

验证：$\chi_5$ 来自 $S_4 \to S_3$（作用在三个对换上），$S_3$ 的标准表示提升。维数公式验证：$1^2 + 1^2 + 3^2 + 3^2 + 2^2 = 24 = |S_4|$。

## 5. 交叉引用

- [表示论基础](docs/02-代数结构/02-核心理论/表示论-基础.md) — 有限群表示系统理论
- [李代数](docs/02-代数结构/02-核心理论/李代数/01-李代数基础.md) — Lie 代数结构与分类
- [代数群](docs/02-代数结构/02-核心理论/代数群/01-代数群基础.md) — 代数群与表示
- [特征标理论](docs/02-代数结构/02-核心理论/表示论深化/02-特征标理论-深度版.md) — 更深入的计算技巧
- [同调代数](docs/02-代数结构/02-核心理论/同调代数深化-扩展/01-同调代数基础.md) — 导出函子与 Ext/Tr

---

**适用**：docs/04-International-Alignment/
