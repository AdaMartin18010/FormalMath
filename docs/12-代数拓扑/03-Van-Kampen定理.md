---
msc_primary: 55Q05
msc_secondary:
  - 55Q20
  - 57M05
processed_at: '2026-04-20'
title: Van Kampen定理
---

# Van Kampen定理

## 1. 引言

在代数拓扑中，基本群的计算是一个核心问题。对于简单的空间如圆或球面，我们可以通过覆叠空间或直接几何论证来确定其基本群。然而，对于由多个简单空间拼接而成的复杂空间，需要一种系统的方法来计算其整体的基本群。Van Kampen定理（又称Seifert-van Kampen定理）正是解决这一问题的有力工具：它将空间分解为两个（或多个）开子集的并，这些子集及其交的基本群已知，然后通过自由积与合 amalgamation 构造出整个空间的基本群。这一定理由Seifert于1931年首先提出，后由van Kampen于1933年独立发现并推广，是组合拓扑向代数拓扑过渡时期的标志性成果。

## 2. 自由积与合积

### 2.1 群的自由积

**定义 2.1**。设 $\{G_\alpha\}_{\alpha \in I}$ 为一族群。它们的**自由积**（free product）$\ast_{\alpha \in I} G_\alpha$ 是由不交并 $\bigsqcup_\alpha G_\alpha$ 生成的自由群，模去每个 $G_\alpha$ 内部原有的群关系所得的商群。等价地，$\ast_\alpha G_\alpha$ 中的元素可唯一表示为**约化字**（reduced word）：$g_1 g_2 \cdots g_n$，其中 $g_i \neq e$，相邻的 $g_i, g_{i+1}$ 来自不同的 $G_\alpha$。

**例 2.2**。$\mathbb{Z} * \mathbb{Z} = F_2$（两个生成元的自由群）。$\mathbb{Z}/2\mathbb{Z} * \mathbb{Z}/2\mathbb{Z} = \langle a, b \mid a^2 = b^2 = e \rangle$ 为无限二面体群。

### 2.2 合积

**定义 2.3**。设 $G, H$ 为群，$K$ 为第三个群，且有同态 $i: K \to G$，$j: K \to H$。**合积**（amalgamated free product/pushout）$G *_K H$（或 $G * H / N$，其中 $N$ 为正规闭包）定义为
$$G *_K H = (G * H) / N,$$
其中 $N$ 为 $G * H$ 中包含 $\{i(k)j(k)^{-1} : k \in K\}$ 的最小正规子群。即在 $G * H$ 中追加关系 $i(k) = j(k)$（对所有 $k \in K$）。

## 3. Van Kampen定理的陈述

### 3.1 经典形式

**定理 3.1**（Seifert-van Kampen）。设 $X$ 为拓扑空间，$U, V \subseteq X$ 为道路连通开集，满足 $X = U \cup V$，且 $U \cap V$ 非空道路连通。取基点 $x_0 \in U \cap V$。则
$$\pi_1(X, x_0) \cong \pi_1(U, x_0) *_{\pi_1(U \cap V, x_0)} \pi_1(V, x_0).$$
更准确地说，下图是群范畴中的推出（pushout）：
$$\begin{array}{ccc}
\pi_1(U \cap V, x_0) & \xrightarrow{i_*} & \pi_1(U, x_0) \\
\downarrow{j_*} & & \downarrow{k_*} \\
\pi_1(V, x_0) & \xrightarrow{l_*} & \pi_1(X, x_0)
\end{array}$$
其中映射由包含诱导。

### 3.2 多重版本

若 $X = \bigcup_{\alpha} U_\alpha$，其中每个 $U_\alpha$ 道路连通，每个有限交 $U_{\alpha_1} \cap \cdots \cap U_{\alpha_n}$ 道路连通，则 $\pi_1(X)$ 为相应图表的极限（colimit）。

## 4. 证明大纲

### 4.1 满射性

**引理 4.1**。由包含诱导的同态 $\pi_1(U) * \pi_1(V) \to \pi_1(X)$ 是满射。

*证明*。设 $\gamma$ 为 $X$ 中基于 $x_0$ 的环路。因 $[0,1]$ 紧，存在分割 $0 = t_0 < t_1 < \cdots < t_n = 1$ 使每个 $\gamma([t_i, t_{i+1}])$ 完全含于 $U$ 或 $V$ 中。设 $\gamma_i$ 为 $\gamma|_{[t_i, t_{i+1}]}$ 适当重参数化。因 $U \cap V$ 道路连通，可取道路 $\alpha_i$ 在 $U \cap V$ 中连接 $x_0$ 与 $\gamma(t_i)$。则
$$[\gamma] = [\alpha_0 * \gamma_0 * \bar{\alpha}_1] \cdot [\alpha_1 * \gamma_1 * \bar{\alpha}_2] \cdots [\alpha_{n-1} * \gamma_{n-1} * \bar{\alpha}_n].$$
每项完全在 $U$ 或 $V$ 中，故属于 $\pi_1(U)$ 或 $\pi_1(V)$ 的像。$\square$

### 4.2 核的刻画

**引理 4.2**。$\pi_1(U) * \pi_1(V) \to \pi_1(X)$ 的核是由 $\{i_*([\omega]) j_*([\omega])^{-1} : [\omega] \in \pi_1(U \cap V)\}$ 生成的正规子群。

*证明概要*。若 $\omega$ 为 $U \cap V$ 中的环路，则作为 $U$ 中的环路和作为 $V$ 中的环路在 $X$ 中同伦（因它们是同一环路）。故 $i_*([\omega]) = j_*([\omega])$ 于 $\pi_1(X)$，即 $i_*([\omega]) j_*([\omega])^{-1}$ 在核中。

反向需证明：若 $\pi_1(U) * \pi_1(V)$ 中的字映射到 $\pi_1(X)$ 中的平凡元，则它可经允许的插入/删除 $i_*([\omega])j_*([\omega])^{-1}$ 型关系约化为空字。这通过同伦 $H: [0,1] \times [0,1] \to X$ 将环路缩为点，再用Lebesgue数引理细分正方形为小块，每块完全在 $U$ 或 $V$ 中，从而将同伦转化为字的等价关系。$\square$

## 5. 应用

### 5.1 轮胎面（环面）

**例 5.1**。$T^2 = S^1 \times S^1$。

将 $T^2$ 视为正方形 $[0,1] \times [0,1]$ 对边粘合。取 $U$ 为去掉中心小闭圆盘，$V$ 为稍大的开圆盘包含该闭圆盘。则 $U$ 形变收缩到边界（即8字形 $S^1 \vee S^1$），故 $\pi_1(U) = F_2 = \langle a, b \rangle$。$V$ 可缩，$\pi_1(V) = 0$。$U \cap V$ 为圆环，形变收缩到圆周，$\pi_1(U \cap V) = \mathbb{Z}$，生成元 $c$ 在 $U$ 中同伦于 $aba^{-1}b^{-1}$（绕边界一周）。

由Van Kampen，
$$\pi_1(T^2) = F_2 *_\mathbb{Z} 0 = \langle a, b \mid aba^{-1}b^{-1} = e \rangle = \mathbb{Z}^2.$$

### 5.2 8字形空间

**例 5.2**。$X = S^1 \vee S^1$。

将每圆去掉一点（不交于切点），得到 $U, V$ 各同伦于 $S^1$，$U \cap V$ 可缩。故
$$\pi_1(X) = \mathbb{Z} *_{0} \mathbb{Z} = \mathbb{Z} * \mathbb{Z} = F_2.$$

### 5.3 双环面

**例 5.3**。双环面 $\Sigma_2$（两个轮胎面沿圆粘合）。

由Van Kampen，$\pi_1(\Sigma_2) = \langle a_1, b_1, a_2, b_2 \mid [a_1, b_1][a_2, b_2] = e \rangle$，其中 $[a,b] = aba^{-1}b^{-1}$。

一般地，亏格 $g$ 的可定向闭曲面有
$$\pi_1(\Sigma_g) = \langle a_1, b_1, \ldots, a_g, b_g \mid [a_1, b_1] \cdots [a_g, b_g] = e \rangle.$$

### 5.4 实射影平面

**例 5.4**。$\mathbb{R}P^2$。

将 $\mathbb{R}P^2$ 视为圆盘 $D^2$ 对径点等同边界。取 $U$ 为稍小于 $D^2$ 的开圆盘（可缩），$V$ 为边界的管状邻域（Möbius带）。$U \cap V$ 为圆环。$V$ 形变收缩到中轴线圆周，$\pi_1(V) = \mathbb{Z}$（生成元 $a$）。$U \cap V$ 的生成元 $c$ 在 $V$ 中同伦于 $a^2$（绕Möbius带中轴线两周）。故
$$\pi_1(\mathbb{R}P^2) = 0 *_\mathbb{Z} \mathbb{Z} = \langle a \mid a^2 = e \rangle = \mathbb{Z}/2\mathbb{Z}.$$

## 6. 与项目其他部分的关联

Van Kampen定理是计算基本群的主要工具，与覆盖空间理论（见[02-覆盖空间理论](02-覆盖空间理论.md)）互为补充。在群论中，群的图（graphs of groups）与Bass-Serre理论将Van Kampen定理推广到更一般的群作用。在范畴论视角（见`docs/02-代数结构/范畴论/`）下，Van Kampen定理表明 $\pi_1$ 保持推出（pushout）——这是基本群作为函子的重要性质。在代数几何中，平展基本群也有类似的Van Kampen型定理。高维Van Kampen定理涉及同伦群的计算，远比基本群情形复杂。

## 7. 参考文献

1. E.R. van Kampen, "On the connection between the fundamental groups of some related spaces", *Amer. J. Math.* 55 (1933), 261–267.
2. H. Seifert, "Konstruktion dreidimensionaler geschlossener Räume", *Ber. Sächs. Akad. Wiss.* 83 (1931), 26–66.
3. A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002.
4. W.S. Massey, *Algebraic Topology: An Introduction*, 1967.
5. 尤承业，《基础拓扑学讲义》，北京大学出版社，1997。
