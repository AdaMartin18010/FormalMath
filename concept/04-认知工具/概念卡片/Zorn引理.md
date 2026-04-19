---
msc_primary: "03E25"
msc_secondary:
  - 06A06
  - 03E35
---

# 概念卡片：Zorn引理

## 严格定义

设 $(P, \leq)$ 为偏序集（partially ordered set, poset）。子集 $C \subseteq P$ 称为**链（chain）**，若 $C$ 中任意两个元素可比，即 $C$ 在诱导序下为全序集。

**Zorn 引理**：若偏序集 $P$ 的每条链都有上界（即对任意链 $C \subseteq P$，存在 $u \in P$ 使得 $c \leq u$ 对所有 $c \in C$），则 $P$ 中存在极大元（即存在 $m \in P$ 使得不存在 $x \in P$ 满足 $m < x$）。

**等价形式**：

- **Hausdorff 极大原理**：偏序集中的任何链都包含于某个极大链中。
- **良序原理**：任何集合都可被良序化（存在一个全序，使得每个非空子集都有最小元）。
- **选择公理（Axiom of Choice, AC）**：对任意非空集合的族 $\{X_i\}_{i \in I}$，存在选择函数 $f: I \to \bigcup_i X_i$ 使得 $f(i) \in X_i$。

在 ZF 公理系统中，上述四个命题彼此等价。

## 历史背景

Zorn 引理的历史与集合论和数理逻辑的发展紧密交织。

**选择公理的萌芽（1904）**：Ernst Zermelo 为了证明"任何集合都可被良序化"，明确提出了选择公理。这一公理引发了数学界的激烈争论——Borel、Lebesgue 等法国分析学家反对使用不可构造的选择，而 Hilbert 学派则认为它是数学推理的合法工具。

**极大原理的形成（1909–1935）**：Hausdorff 在 1909 年证明了偏序集中极大链的存在性（Hausdorff 极大原理）。Kazimierz Kuratowski 在 1922 年给出了类似的表述。Max Zorn 于 1935 年将其改进为今天广泛使用的形式，用于证明向量空间的基的存在性。

**等价性的确立（1935–1960）**：通过 Zermelo、Hausdorff、Kuratowski、Zorn、Teichmüller 和 Tukey 等人的工作，选择公理、良序原理、Zorn 引理和 Hausdorff 极大原理的等价性得以确立。Jech（1973）的专著系统研究了选择公理及其等价形式。

## 直观理解

Zorn 引理的直观图像是一个"无限上升的梯子"。想象你在偏序集 $P$ 中行走，每一步都走向更大的元素。条件说：无论你沿着怎样的链（路径）走多远，前方总有一个平台（上界）可以供你继续攀登或休息。Zorn 引理保证：这样的攀登过程最终必能到达一个"山顶"——极大元。

关键注意：Zorn 引理的极大元不一定是**最大元**（即不一定大于所有其他元素）。它只是一个"局部峰值"——没有比它更大的元素，但可能存在不可比较的元素。

另一个直观是**树的生长**：将偏序集想象为一棵向下生长的树（根在上，叶在下）。Zorn 条件要求每个树枝（链）都有上界（可以向上追溯到某个节点）。Zorn 引理说：在这样的树中，至少存在一个"顶端节点"，它不是任何其他节点的真后代。

## 数学例子

### 向量空间的基

**定理**：任何向量空间 $V$ 都有 Hamel 基。

**证明**：令 $P$ 为 $V$ 中所有线性无关子集的集合，以包含为偏序。设 $C = \{S_i\}_{i \in I}$ 为 $P$ 中的一条链。令 $U = \bigcup_{i \in I} S_i$。

验证 $U$ 线性无关：设 $v_1, \ldots, v_n \in U$ 且 $\sum_{k=1}^n \alpha_k v_k = 0$。因 $C$ 为链，存在某个 $S_j$ 包含所有 $v_k$。因 $S_j$ 线性无关，故所有 $\alpha_k = 0$。

因此 $U \in P$ 且为 $C$ 的上界。由 Zorn 引理，$P$ 有极大元 $B$。$B$ 即为 $V$ 的基：若存在 $v \in V \setminus \mathrm{span}(B)$，则 $B \cup \{v\}$ 线性无关，与 $B$ 的极大性矛盾。

### 极大理想的存在性

**定理**：任何非零交换环 $R$ 都有极大理想。

**证明**：令 $P$ 为 $R$ 的所有真理想的集合，以包含为偏序。设 $C = \{I_\alpha\}$ 为链。令 $I = \bigcup_\alpha I_\alpha$。

验证 $I$ 为真理想：若 $1 \in I$，则 $1 \in I_\alpha$ 对某个 $\alpha$，与 $I_\alpha$ 真矛盾。故 $I$ 为真理想且为 $C$ 的上界。

由 Zorn 引理，$P$ 有极大元 $M$。$M$ 即为极大理想。

### Hahn-Banach 定理

**定理**：设 $X$ 为实向量空间，$p: X \to \mathbb{R}$ 为次线性泛函（$p(x+y) \leq p(x) + p(y)$，$p(tx) = tp(x)$ 对 $t \geq 0$）。设 $Y \subseteq X$ 为子空间，$f: Y \to \mathbb{R}$ 为线性泛函且 $f(y) \leq p(y)$ 对 $y \in Y$。则存在线性泛函 $F: X \to \mathbb{R}$ 使得 $F|_Y = f$ 且 $F(x) \leq p(x)$ 对 $x \in X$。

**证明概要**：令 $P$ 为所有 $(Z, g)$ 的集合，其中 $Y \subseteq Z \subseteq X$，$g: Z \to \mathbb{R}$ 为 $f$ 的线性延拓且 $g \leq p$ 在 $Z$ 上。以延拓为偏序。

关键一步：若 $(Z, g)$ 非极大，则存在 $x_0 \notin Z$。定义 $Z' = Z + \mathbb{R}x_0$，需要选择 $g(x_0) = c$ 使得对所有 $z_1, z_2 \in Z$：
$$g(z_1) - p(z_1 - x_0) \leq c \leq p(z_2 + x_0) - g(z_2)。$$
由次线性性可证左边 $\leq$ 右边，故 $c$ 存在。

Zorn 引理给出极大元 $(Z_{\max}, F)$。若 $Z_{\max} \neq X$，则可进一步延拓，矛盾。故 $Z_{\max} = X$。

### Tychonoff 定理

**定理**：任意族紧致空间的积空间（乘积拓扑）紧致。

**证明概要**：利用 Alexander 子基定理：只需验证任何由子基元素构成的开覆盖都有有限子覆盖。

令 $X = \prod_{i \in I} X_i$，$\mathcal{S}$ 为子基。设 $\mathcal{U} \subseteq \mathcal{S}$ 为覆盖。对每个 $i \in I$，令 $\mathcal{U}_i$ 为 $\mathcal{U}$ 中投影到第 $i$ 个坐标上的开集族。

若某个 $\mathcal{U}_i$ 覆盖 $X_i$，则由 $X_i$ 紧致，有有限子覆盖，从而得到 $X$ 的有限子覆盖。

若没有任何 $\mathcal{U}_i$ 覆盖 $X_i$，则对每个 $i$，存在 $x_i \in X_i$ 不被 $\mathcal{U}_i$ 覆盖。令 $x = (x_i)_{i \in I}$。因 $\mathcal{U}$ 覆盖 $X$，存在 $U \in \mathcal{U}$ 包含 $x$。由子基定义，$U$ 形如 $\pi_i^{-1}(V_i)$。则 $x_i \in V_i \in \mathcal{U}_i$，矛盾。

（注：此证明不需显式使用 Zorn 引理，但 Alexander 子基定理本身等价于选择公理。）

## 与其他概念的联系

### 与良序原理的联系

良序原理说任何集合都可被良序化。从良序原理推导 Zorn 引理：设 $P$ 满足 Zorn 条件，$(W, \leq)$ 为 $P$ 的良序子集（由良序原理）。通过超限递归定义链 $C_\alpha$：$C_0 = \varnothing$；$C_{\alpha+1} = C_\alpha \cup \{x_\alpha\}$（选择严格大于 $C_\alpha$ 中所有元的 $x_\alpha$，若存在）；极限步取并。此过程必在某步停止（因不能构造到所有序数），停止点给出极大元。

### 与超限归纳的联系

超限归纳是数学归纳法在良序集上的推广。Zorn 引理可视为"存在性版本的超限归纳"：超限归纳证明某性质对所有序数成立；Zorn 引理证明某偏序集中存在极大元。两者共享同样的数学直觉——在良序结构中不能无限严格递减。

### 与范畴论的联系

在范畴论中，Zorn 引理的类比是**伴随函子定理**（Adjoint Functor Theorem）。Freyd 的一般伴随函子定理在适当的"解集条件"（类似于 Zorn 的链有上界条件）下保证了左伴随的存在性。这一视角将 Zorn 引理从集合论提升到更一般的数学结构中。

## 参考

- Jech, T. (1973). *The Axiom of Choice*. North-Holland.
- Halmos, P. R. (1960). *Naive Set Theory*. Van Nostrand.
- Kunen, K. (1980). *Set Theory: An Introduction to Independence Proofs*. North-Holland.
- Moore, G. H. (1982). *Zermelo's Axiom of Choice: Its Origins, Development, and Influence*. Springer.
