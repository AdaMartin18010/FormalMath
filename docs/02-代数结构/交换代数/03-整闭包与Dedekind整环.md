---
msc_primary: 13B22
msc_secondary:
  - 13F05
  - 13G05
processed_at: '2026-04-20'
title: 整闭包与Dedekind整环
---

# 整闭包与Dedekind整环

## 1. 引言

整扩张（integral extension）和整闭包（integral closure）是交换代数中连接环论与域论的核心概念。它们源于古典代数数论：代数整数环是 $\mathbb{Q}$ 的有限扩张中整闭包的典型例子。整扩张保持了诸多优良的性质（如Krull维数不变），而整闭包则将一般的整环"正规化"。在维数为一的情形，整闭Noetherian整环具有特别简洁的结构——Dedekind整环，其理想可唯一分解为素理想的乘积。本文系统阐述整扩张的基本理论、素理想的提升、整闭包的性质以及Dedekind整环的刻画与例子。

## 2. 整扩张

### 2.1 整元的定义

**定义 2.1**。设 $R \subseteq S$ 为环扩张。元素 $s \in S$ 称为在 $R$ 上**整的**（integral），若存在首一多项式（monic polynomial）$f(x) = x^n + a_{n-1}x^{n-1} + \cdots + a_0 \in R[x]$ 使 $f(s) = 0$。

**定义 2.2**。$S$ 中在 $R$ 上整的所有元素构成子环，称为 $R$ 在 $S$ 中的**整闭包**（integral closure）。若 $R$ 在 $S$ 中的整闭包等于 $R$，称 $R$ 在 $S$ 中**整闭**。若 $R$ 在其分式域中整闭，称 $R$ **整闭**（integrally closed/normal）。

**例 2.3**。$\mathbb{Z}$ 在 $\mathbb{Q}$ 中整闭。$\mathbb{Z}[\sqrt{5}]$ 非整闭：$\frac{1 + \sqrt{5}}{2}$ 满足 $x^2 - x - 1 = 0$，但不在 $\mathbb{Z}[\sqrt{5}]$ 中。

### 2.2 整性的等价刻画

**定理 2.4**。以下条件等价：
1. $s \in S$ 在 $R$ 上整；
2. $R[s]$ 为有限生成 $R$-模；
3. 存在含 $R[s]$ 的子环 $T \subseteq S$ 使 $T$ 为有限生成 $R$-模。

*证明*。(1) $\Rightarrow$ (2)：若 $s^n + a_{n-1}s^{n-1} + \cdots + a_0 = 0$，则 $R[s]$ 由 $\{1, s, \ldots, s^{n-1}\}$ 生成。

(2) $\Rightarrow$ (3)：取 $T = R[s]$。

(3) $\Rightarrow$ (1)：设 $T$ 由 $t_1, \ldots, t_m$ 生成。$s \cdot t_i = \sum_j a_{ij} t_j$。由Cayley-Hamilton型论证，$s$ 满足其"特征多项式" $\det(sI - (a_{ij})) = 0$。$\square$

### 2.3 整扩张的基本性质

**定理 2.5**。设 $R \subseteq S$ 为整扩张。则：
1. （维数不变）$\dim R = \dim S$；
2. （Lying Over）对 $R$ 的每个素理想 $\mathfrak{p}$，存在 $S$ 的素理想 $\mathfrak{q}$ 使 $\mathfrak{q} \cap R = \mathfrak{p}$；
3. （Incomparability）若 $\mathfrak{q}_1 \subsetneq \mathfrak{q}_2$ 为 $S$ 的素理想，则 $\mathfrak{q}_1 \cap R \subsetneq \mathfrak{q}_2 \cap R$。

*证明*。(1) 由(2)(3)，$\operatorname{Spec}(S) \to \operatorname{Spec}(R)$ 的纤维为有限集，且保持包含关系。$\square$

**定理 2.6**（Going Up）。设 $R \subseteq S$ 整，$\mathfrak{p}_1 \subseteq \mathfrak{p}_2$ 为 $R$ 的素理想，$\mathfrak{q}_1$ 为 $S$ 的素理想且 $\mathfrak{q}_1 \cap R = \mathfrak{p}_1$。则存在 $S$ 的素理想 $\mathfrak{q}_2 \supseteq \mathfrak{q}_1$ 使 $\mathfrak{q}_2 \cap R = \mathfrak{p}_2$。

**定理 2.7**（Going Down，需 $R$ 整闭）。在额外假设 $R$ 整闭且 $S$ 为整环时，反向的Going Down也成立。

## 3. Dedekind整环

### 3.1 定义与刻画

**定义 3.1**。整环 $R$ 称为**Dedekind整环**，若满足：
1. Noetherian；
2. 维数为1（非零素理想皆极大）；
3. 整闭。

**定理 3.2**（等价刻画）。整环 $R$ 为Dedekind当且仅当：
- 每个非零理想可唯一分解为素理想的乘积；
- 每个非零理想可逆（在分式理想群中）；
- 每个非零理想为极大理想的有限乘积；
- $R$ 为Noetherian、整闭、维数 $\leq 1$。

### 3.2 理想类群

**定义 3.3**。$R$ 的**分式理想**为 $K = \operatorname{Frac}(R)$ 的有限生成 $R$-子模。非零分式理想在乘法下构成群，单位理想群为主分式理想子群。商群
$$\operatorname{Cl}(R) = \text{分式理想群} / \text{主分式理想群}$$
称为**理想类群**（class group）。$\operatorname{Cl}(R) = 0$ 当且仅当 $R$ 为PID。

**定理 3.4**。Dedekind整环的理想类群有限当且仅当 $R$ 为数域的整数环（或函数域的特定整环）。

### 3.3 典型例子

**例 3.5**。PID皆为Dedekind整环（类群平凡）。

**例 3.6**。数域 $K/\mathbb{Q}$ 的**整数环** $\mathcal{O}_K$（$K$ 中在 $\mathbb{Z}$ 上整的元构成的环）是Dedekind整环。

**例 3.7**。$\mathbb{Z}[\sqrt{-5}]$ 为Dedekind整环但非PID：$6 = 2 \cdot 3 = (1 + \sqrt{-5})(1 - \sqrt{-5})$，理想有唯一分解 $\langle 6 \rangle = \mathfrak{p}_1 \mathfrak{p}_2 \mathfrak{p}_3 \mathfrak{p}_4$。

**例 3.8**。$k[x]$（$k$ 域）为Dedekind。其有限扩张中的整闭包（如椭圆曲线坐标环）也是Dedekind。

## 4. 离散赋值环

**定义 4.1**。一维Noetherian局部整环 $(R, \mathfrak{m})$ 若整闭，则称为**离散赋值环**（DVR, discrete valuation ring）。等价于：存在离散赋值 $v: K^\times \to \mathbb{Z}$ 使 $R = \{x \in K : v(x) \geq 0\}$。

**定理 4.2**。Dedekind整环在其非零素理想处的局部化是DVR。

## 5. 与项目其他部分的关联

整闭包和Dedekind整环是代数数论和代数曲线的理论基础。在代数几何（见`docs/02-代数结构/范畴论/08-范畴论在代数几何中的应用.md`）中，正规概形（在每点处整闭）具有良好的奇异性性质。Dedekind整环是代数曲线的坐标环的一维类比。在范畴论视角（见`docs/02-代数结构/范畴论/`）下，整扩张给出了环范畴中的特定子类。局部化（见[01-局部化](01-局部化.md)）与整闭包经常联合使用：$R$ 整闭当且仅当在所有素（或极大）理想处局部化整闭。

## 6. 参考文献

1. R. Dedekind, "Über die Theorie der ganzen algebraischen Zahlen", *Dirichlet's Vorlesungen über Zahlentheorie*, Supplement XI, 1894.
2. E. Noether, "Abstrakter Aufbau der Idealtheorie in algebraischen Zahl- und Funktionenkörpern", *Math. Ann.* 96 (1927), 26–61.
3. M. Atiyah & I.G. Macdonald, *Introduction to Commutative Algebra*, Addison-Wesley, 1969.
4. H. Matsumura, *Commutative Ring Theory*, Cambridge University Press, 1986.
5. 潘承洞、潘承彪，《代数数论》，山东大学出版社，2001。
