---
msc_primary: 13E05
msc_secondary:
  - 13E10
  - 13F20
processed_at: '2026-04-20'
title: Noetherian环与Artinian环
---

# Noetherian环与Artinian环

## 1. 引言

Noetherian环和Artinian环是交换代数中两类基本的环，分别以上升链条件（ACC）和下降链条件（DCC）为特征。Noetherian环以Emmy Noether命名，她的工作奠定了现代抽象代数的基石；Artinian环以Emil Artin命名。这两类条件虽然对称地表述，但其后果却截然不同：Noetherian环极其丰富，几乎涵盖了代数几何和数论中遇到的所有环；而Artinian环则结构极为刚性，可被完全分类。本文系统阐述这两类环的定义、基本性质、Hilbert基定理以及Artin-Wedderburn型结果在交换情形的特例。

## 2. 链条件

### 2.1 定义

**定义 2.1**。环 $R$ 称为**Noetherian的**，若其理想满足**升链条件**（ACC）：任何理想升链
$$I_1 \subseteq I_2 \subseteq I_3 \subseteq \cdots$$
稳定（即存在 $N$ 使 $I_N = I_{N+1} = \cdots$）。

**定义 2.2**。环 $R$ 称为**Artinian的**，若其理想满足**下降链条件**（DCC）：任何理想降链
$$I_1 \supseteq I_2 \supseteq I_3 \supseteq \cdots$$
稳定。

等价刻画：$R$ Noetherian当且仅当每个理想有限生成。$R$ Artinian当且仅当每个素理想极大（见后）。

### 2.2 模的链条件

上述定义可推广到 $R$-模：模 $M$ 为Noetherian（Artinian）若其子模满足ACC（DCC）。

**命题 2.3**。在短正合序列 $0 \to M' \to M \to M'' \to 0$ 中，$M$ Noetherian（Artinian）当且仅当 $M'$ 和 $M''$ 皆Noetherian（Artinian）。

## 3. Noetherian环的性质

### 3.1 基本例子

**例 3.1**。域、PID（主理想整环）、DVR（离散赋值环）皆为Noetherian。

**例 3.2**。多项式环 $k[x_1, x_2, \ldots]$（无穷多变量）非Noetherian：理想升链 $(x_1) \subsetneq (x_1, x_2) \subsetneq (x_1, x_2, x_3) \subsetneq \cdots$ 不终止。

### 3.2 Hilbert基定理

**定理 3.3**（Hilbert基定理）。若 $R$ 为Noetherian环，则 $R[x]$ 也是Noetherian环。

*证明*。设 $I \subseteq R[x]$ 为理想。对每个 $n \geq 0$，令 $J_n = \{a \in R : \exists f \in I, \deg f \leq n, \text{首项系数为 } a\}$。则 $J_0 \subseteq J_1 \subseteq J_2 \subseteq \cdots$ 为 $R$ 中的理想升链。由ACC，稳定于某 $J_N$。每个 $J_n$（$n \leq N$）有限生成，设生成元为 $a_{n1}, \ldots, a_{nk_n}$，对应多项式 $f_{ni} \in I$。则 $\{f_{ni} : 0 \leq n \leq N, 1 \leq i \leq k_n\}$ 生成 $I$。$\square$

**推论 3.4**。若 $R$ Noetherian，则 $R[x_1, \ldots, x_n]$ Noetherian。特别地，域上有限生成代数 $k[x_1, \ldots, x_n]/I$ 皆Noetherian。

**推论 3.5**。Noetherian环上的有限生成模是Noetherian模。

### 3.3 准素分解

**定理 3.6**（Lasker-Noether）。Noetherian环中每个理想可表为有限个准素理想的交。

*证明概要*。称理想 $I$ **不可约**，若 $I = J \cap K$ 蕴含 $I = J$ 或 $I = K$。在Noetherian环中，每个理想为有限个不可约理想的交。不可约理想必为准素的（若 $ab \in I$，$a \notin I$，考虑升链 $\operatorname{Ann}(b) \subseteq \operatorname{Ann}(b^2) \subseteq \cdots$）。$\square$

## 4. Artinian环的结构

### 4.1 基本性质

**定理 4.1**。Artinian整环为域。

*证明*。设 $R$ Artinian整环，$0 \neq a \in R$。降链 $(a) \supseteq (a^2) \supseteq (a^3) \supseteq \cdots$ 稳定，故 $(a^n) = (a^{n+1})$，$a^n = ba^{n+1}$。因无零因子，$1 = ba$。$\square$

**定理 4.2**。Artinian环恰有有限个素理想，且每个素理想都是极大的。

*证明*。设 $\{\mathfrak{p}_i\}$ 为两两不同的素理想族。考虑降链 $\prod_{i=1}^n \mathfrak{p}_i$。由DCC，有限个即可。若 $\mathfrak{p}$ 素非极大，则 $\mathfrak{p} \subsetneq \mathfrak{m}$，降链 $\mathfrak{m}^n + \mathfrak{p}$ 稳定导致矛盾。$\square$

### 4.2 结构定理

**定理 4.3**（Artin-Wedderburn，交换情形）。Artinian环 $R$ 可唯一分解为有限个Artinian局部环的直积：
$$R \cong R_1 \times R_2 \times \cdots \times R_n.$$

**定理 4.4**。Artinian局部环 $(R, \mathfrak{m})$ 中，$\mathfrak{m}$ 为幂零理想（$\mathfrak{m}^k = 0$ 对某 $k$），且 $R$ 的长度（作为 $R$-模的组成列长度）有限。

### 4.3 Akizuki定理

**定理 4.5**（Akizuki）。环为Artinian当且仅当为Noetherian且维数为零（Krull维数为0，即每个素理想极大）。

*证明概要*。Artinian $\Rightarrow$ DCC $\Rightarrow$ ACC（对零维环，由准素分解和幂零性）。反向：零维Noetherian环的理想有足够结构使其满足DCC。$\square$

## 5. 与项目其他部分的关联

Noetherian环是代数几何的基础——Hilbert基定理保证了域上有限生成代数（即仿射坐标环）皆为Noetherian，从而使概形的理论可行。准素分解是代数簇的不可约分解的代数对应。Artinian环在表示论和编码理论中有应用。在维数理论（见[05-维数理论](05-维数理论.md)）中，Noetherian性是维数有限性的前提。在范畴论视角（见`docs/02-代数结构/范畴论/`）下，Noetherian模的范畴是Abel范畴的重要例子。

## 6. 参考文献

1. E. Noether, "Idealtheorie in Ringbereichen", *Math. Ann.* 83 (1921), 24–66.
2. D. Hilbert, "Über die Theorie der algebraischen Formen", *Math. Ann.* 36 (1890), 473–534.
3. M. Atiyah & I.G. Macdonald, *Introduction to Commutative Algebra*, Addison-Wesley, 1969.
4. H. Matsumura, *Commutative Ring Theory*, Cambridge University Press, 1986.
5. 冯克勤，《交换代数基础》，高等教育出版社，1985。
