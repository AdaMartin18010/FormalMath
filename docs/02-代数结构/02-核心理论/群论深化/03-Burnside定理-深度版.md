---
title: "Burnside定理 - 深度版"
msc_primary: 20

  - 20D10
msc_secondary: ["20C15", "20E32", "20F16"]
processed_at: '2026-04-05'
references:
  textbooks:
    - id: artin_algebra
      type: textbook
      title: Algebra
      authors:
      - Michael Artin
      publisher: Pearson
      edition: 2nd
      year: 2011
      isbn: 978-0132413770
      msc: 16-01
      chapters: 
      url: ~
    - id: strang_la
      type: textbook
      title: Introduction to Linear Algebra
      authors:
      - Gilbert Strang
      publisher: Wellesley-Cambridge Press
      edition: 5th
      year: 2016
      isbn: 978-0980232776
      msc: 15-01
      chapters: 
      url: ~
    - id: dummit_foote_aa
      type: textbook
      title: Abstract Algebra
      authors:
      - David S. Dummit
      - Richard M. Foote
      publisher: Wiley
      edition: 3rd
      year: 2003
      isbn: 978-0471433347
      msc: 13-01
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

# Burnside定理 - 深度版

> **"特征标理论的威力在于它能够揭示群结构的深层算术性质。"** —— William Burnside

---

## 📚 概述

Burnside定理（1904年）是有限群论中最深刻的结果之一：任何阶为$p^aq^b$（$p, q$为素数）的有限群都是可解群。这一结果的重要性在于：

1. **纯代数证明的困难性**：Burnside之前，这一问题困扰数学家数十年
2. **特征标理论的首个重大胜利**：这是首个完全依赖特征标理论证明的非平凡群论定理
3. **有限单群分类的前奏**：该定理揭示了单群可能的阶的结构

---

## 🕰️ 历史背景与数学家理念

### Burnside的数学理念

**William Burnside（1852-1927）**是英国数学家，他在群论、表示论和概率论方面都有重要贡献。Burnside的数学理念体现为：

1. **计算与结构的平衡**：既重视具体计算，又追求抽象结构
2. **特征标理论的信仰**：相信特征标能够揭示群的深层性质
3. **算术与代数的统一**：通过群阶的算术性质研究代数结构

### 伽罗瓦可解性理论的现代发展

**伽罗瓦数学理念**关于代数方程可解性的研究，直接影响了Burnside的工作：

- **伽罗瓦的可解群概念**：Burnside定理证明了$p^aq^b$阶群必然是可解的
- **伽罗瓦对应**：群的可解性对应于域扩张的根式可解性

### 格洛腾迪克的结构主义视角

**格洛腾迪克数学理念**强调通过结构关系理解数学对象。从这一视角看：

- Burnside定理揭示了群阶的算术结构与群的代数结构之间的深刻联系
- 特征标理论可视为从表示范畴到函数范畴的函子

---

## 🏗️ 核心概念与完整证明

### 1. 预备知识

**定义 3.1**（可解群）
群$G$称为**可解群**，如果存在子群列：
$$G = G_0 \triangleright G_1 \triangleright \cdots \triangleright G_n = \{e\}$$
使得每个商群$G_i/G_{i+1}$都是阿贝尔群。

**等价条件**：$G$可解当且仅当它的导出列终止于平凡群。

**定义 3.2**（代数整数）
复数$\alpha$称为**代数整数**，如果它是某个首一整系数多项式的根。

**基本性质**：

1. 代数整数构成$\mathbb{C}$的子环
2. 有理代数整数必为普通整数
3. 特征标值都是代数整数

**引理 3.1**（特征标的算术性质）
设$\chi$是$G$的不可约特征标，$K$是共轭类，$g \in K$，则：
$$\frac{|K|\chi(g)}{\chi(e)}$$
是代数整数。

**证明**：
设$\rho$是相应表示，$n = \chi(e)$。定义**类代数元素**：
$$z_K = \sum_{h \in K} h \in \mathbb{Z}[G]$$

**步骤1**：$z_K$在群代数$\mathbb{Z}[G]$的中心中。

**步骤2**：$\rho(z_K)$是标量算子（由Schur引理）。

**步骤3**：计算迹：
$$\text{tr}(\rho(z_K)) = \sum_{h \in K} \chi(h) = |K|\chi(g)$$

**步骤4**：由Schur引理，$\rho(z_K) = \lambda I$，故：
$$\lambda = \frac{|K|\chi(g)}{n}$$

**步骤5**：$z_K$是中心整群代数元素，故$\lambda$是代数整数。

**证毕**。

### 2. Burnside定理的完整证明

**定理 3.1**（Burnside，1904）
设$G$是阶为$p^aq^b$的有限群（$p, q$为素数，$a, b \geq 0$），则$G$是可解群。

**证明**：对$|G|$进行归纳。

**步骤1**：简化情形。
若$G$有非平凡正规子群$N$，则由归纳假设$N$和$G/N$都可解，故$G$可解。

因此只需证明：不存在非交换单群的阶为$p^aq^b$。

**步骤2**：关键引理。
设$G$是有限群，$\chi$是$G$的非平凡不可约特征标，$\chi(e) = n$。设$K$是共轭类，$g \in K$，$g \neq e$。若$\gcd(|K|, n) = 1$，则$\chi(g) = 0$或$|K| = 1$。

**引理证明**：

由条件，存在整数$u, v$使得$u|K| + vn = 1$。

乘以$\frac{\chi(g)}{n}$：
$$\frac{\chi(g)}{n} = u\frac{|K|\chi(g)}{n} + v\chi(g)$$

由引理3.1，$\frac{|K|\chi(g)}{n}$是代数整数，$\chi(g)$也是代数整数，故$\frac{\chi(g)}{n}$是代数整数。

设$\chi$由表示$(\rho, V)$给出。$\rho(g)$是有限阶矩阵，故可对角化，特征根是单位根$\omega_1, \ldots, \omega_n$。

因此：
$$\chi(g) = \omega_1 + \cdots + \omega_n$$
$$|\chi(g)| \leq n$$

若$|\chi(g)| = n$，则所有$\omega_i$相等，$\rho(g)$是标量矩阵。这意味着$g$在中心$Z(G)$中，故$|K| = 1$。

若$|\chi(g)| < n$，则$\frac{\chi(g)}{n}$是代数整数且$\left|\frac{\chi(g)}{n}\right| < 1$。

考虑$\chi(g)$的Galois共轭：它们也是$n$个单位根之和，绝对值不超过$n$。

因此$\frac{\chi(g)}{n}$的所有Galois共轭的绝对值都小于1。

但$\frac{\chi(g)}{n}$的极小多项式的常数项是$\pm$所有Galois共轭的乘积，其绝对值小于1。

而常数项是整数（因$\frac{\chi(g)}{n}$是代数整数），故必须为0。

因此$\chi(g) = 0$。

**引理证毕**。

**步骤3**：存在满足引理条件的特征标和共轭类。

设$G$是非交换单群，$|G| = p^aq^b$。

考虑Sylow $p$-子群$P$，$|P| = p^a$。

$P$有非平凡中心（$p$-群性质），取$e \neq g \in Z(P)$。

$g$的共轭类大小$|K_g| = [G : C_G(g)]$。

由于$g \in Z(P)$，$P \leq C_G(g)$，故$|K_g| = \frac{|G|}{|C_G(g)|}$整除$\frac{|G|}{|P|} = q^b$。

因此$|K_g|$是$q$的幂。

**步骤4**：应用正交关系。

设$\chi_1, \ldots, \chi_r$是$G$的不可约特征标，$\chi_1$是平凡特征标。

对$g \neq e$应用第二正交关系：
$$\sum_{i=1}^{r} \chi_i(e)\chi_i(g) = 0$$

即：
$$1 + \sum_{i=2}^{r} n_i \chi_i(g) = 0$$

其中$n_i = \chi_i(e)$。

**步骤5**：导出矛盾。

对每个非平凡不可约特征标$\chi_i$：

- 若$p \nmid n_i$，由于$|K_g|$是$q$的幂，$\gcd(|K_g|, n_i) = 1$
- 由关键引理，$\chi_i(g) = 0$或$g \in Z(G)$（不可能，因$G$是非交换单群）

因此若$p \nmid n_i$，则$\chi_i(g) = 0$。

设$S = \{i \geq 2 : p \mid n_i\}$，则：
$$1 + \sum_{i \in S} n_i \chi_i(g) = 0$$

**步骤6**：算术论证。

注意$n_i \mid |G| = p^aq^b$（由表示论基本结果）。

对每个$i \in S$，$n_i = p^{a_i}q^{b_i}$且$a_i \geq 1$。

因此：
$$\frac{1}{p} = -\sum_{i \in S} \frac{n_i}{p} \chi_i(g)$$

右边是代数整数（因$\frac{n_i}{p}$是整数，$\chi_i(g)$是代数整数）。

但$\frac{1}{p}$不是代数整数（其极小多项式为$px - 1$）。

**矛盾**！

**证毕**。

---

## 🧠 数学思想分析

### 证明的结构美

Burnside定理的证明体现了以下数学思想：

1. **归约法**：通过归纳和正规子群分析简化问题
2. **特征标算术**：将群的算术性质转化为特征标的代数性质
3. **矛盾论证**：假设非交换单群存在，导出算术矛盾

### 伽罗瓦对应的应用

Burnside定理与伽罗瓦理论的联系：

- 若$|G| = p^aq^b$，则$G$可解
- 由伽罗瓦对应，这对应于某些域扩张的根式可解性
- 该结果在代数数论中有重要应用

---

## 📚 参考文献

1. **Burnside, W.** (1904). "On groups of order $p^aq^b$". *Proceedings of the London Mathematical Society*, (2) 1, 388-392.
2. **Isaacs, I. M.** (1994). *Character Theory of Finite Groups*. Dover.
3. **Alperin, J. L., & Bell, R. B.** (1995). *Groups and Representations*. Springer.
4. **Serre, J.-P.** (1977). *Linear Representations of Finite Groups*. Springer.

---

*文档版本: 1.0*
*创建日期: 2026年4月*
*最后更新: 2026年4月*
