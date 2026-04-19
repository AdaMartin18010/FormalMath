---
msc_primary: 13J10
msc_secondary:
  - 13B35
  - 13H99
processed_at: '2026-04-20'
title: 完备化与Hensel引理
---

# 完备化与Hensel引理

## 1. 引言

完备化（completion）是分析学和代数学中共同的基本操作：在分析中，有理数完备化为实数、函数空间完备化为Banach空间；在代数中，环关于理想的完备化将"形式"结构变为"实质"结构，使得许多在原始环中仅近似成立的性质在完备环中精确成立。Hensel引理是完备局部环的标志性定理，它将牛顿迭代法从分析学移植到代数学：在完备局部环中，多项式的单根可以唯一地提升。本文系统阐述adic拓扑、完备化的构造与性质、完备Noetherian环的结构，以及Hensel引理的各种形式。

## 2. Adic拓扑

### 2.1 定义

**定义 2.1**。设 $R$ 为环，$I \subseteq R$ 为理想。$I$-adic拓扑以 $\{I^n\}_{n \geq 0}$ 为0的邻域基。$R$ 在此拓扑下为拓扑环。

**定义 2.2**。$R$ 中的序列 $(x_n)$ 称为**Cauchy列**，若对任意 $n$，存在 $N$ 使当 $m, k \geq N$ 时，$x_m - x_k \in I^n$。

### 2.2 完备化

**定义 2.3**。$R$ 关于 $I$ 的**完备化**（completion）定义为
$$\hat{R} = \varprojlim_n R/I^n = \left\{(x_n) \in \prod_{n=1}^\infty R/I^n : x_{n+1} \equiv x_n \pmod{I^n}\right\}.$$

自然映射 $R \to \hat{R}$（$r \mapsto (r \bmod I, r \bmod I^2, \ldots)$）的核为 $\bigcap_{n} I^n$。

**命题 2.4**。$\hat{R}$ 为完备拓扑环（关于 $\hat{I} = \varprojlim I/I^n$ 的adic拓扑）。$R \to \hat{R}$ 连续，像稠密。

### 2.3 例子

**例 2.5**。$R = \mathbb{Z}$，$I = (p)$。$\hat{\mathbb{Z}}_{(p)} = \mathbb{Z}_p$（$p$-进整数环）。

$$\mathbb{Z}_p = \left\{\sum_{n=0}^\infty a_n p^n : a_n \in \{0, 1, \ldots, p-1\}\right\}.$$

**例 2.6**。$R = k[x]$，$I = (x)$。$\hat{R} = k[[x]]$（形式幂级数环）。

**例 2.7**。$R = k[x_1, \ldots, x_n]$，$I = (x_1, \ldots, x_n)$。$\hat{R} = k[[x_1, \ldots, x_n]]$。

## 3. 完备Noetherian环

### 3.1 基本性质

**定理 3.1**。设 $R$ Noetherian，$I \subseteq R$ 理想。则：
1. $\hat{R}$ Noetherian；
2. $I\hat{R} = \hat{I}$，且 $R/I^n \cong \hat{R}/\hat{I}^n$；
3. 若 $M$ 有限生成 $R$-模，则 $\hat{M} = \varprojlim M/I^n M \cong M \otimes_R \hat{R}$；
4. $M \to \hat{M}$ 为单射当且仅当 $\bigcap_n I^n M = 0$（Krull交定理：当 $R$ Noetherian 且 $I \subseteq J(R)$ 时成立）。

### 3.2 结构定理

**定理 3.2**（Cohen结构定理）。设 $(R, \mathfrak{m})$ 为完备Noetherian局部环。则：
- 若 $R$ 包含域，则 $R \cong k[[x_1, \ldots, x_n]]/I$（$k = R/\mathfrak{m}$）；
- 一般情形，$R$ 有子环同构于Cohen环（特征0时为 $\mathbb{Z}_p$ 的有限扩张），$R$ 为其上形式幂级数环的商。

## 4. Hensel引理

### 4.1 经典形式

**定理 4.1**（Hensel引理）。设 $(R, \mathfrak{m})$ 为完备局部环，$f(x) \in R[x]$ 为首一多项式。设 $\bar{f}(x) \in (R/\mathfrak{m})[x]$ 有单根 $\bar{a}$（即 $\bar{f}(\bar{a}) = 0$，$\bar{f}'(\bar{a}) \neq 0$）。则存在唯一的 $a \in R$ 使 $f(a) = 0$ 且 $a \equiv \bar{a} \pmod{\mathfrak{m}}$。

*证明*（Newton迭代）。设 $a_1 \in R$ 为 $\bar{a}$ 的提升。定义
$$a_{n+1} = a_n - \frac{f(a_n)}{f'(a_n)}.$$
由 $f(a_n) \in \mathfrak{m}^n$ 和 $f'(a_n)$ 可逆（因 $f'(\bar{a}) \neq 0$），归纳得 $a_{n+1} \equiv a_n \pmod{\mathfrak{m}^n}$。故 $(a_n)$ Cauchy，收敛于 $a \in R$，$f(a) = 0$。$\square$

### 4.2 多元形式

**定理 4.2**。设 $f_1, \ldots, f_n \in R[x_1, \ldots, x_n]$，$J = (\partial f_i / \partial x_j)$ 为Jacobi矩阵。若在 $R/\mathfrak{m}$ 中有解 $\bar{a}$ 且 $J(\bar{a})$ 可逆，则存在唯一提升 $a \in R^n$。

### 4.3 Hensel局部环

**定义 4.3**。局部环 $(R, \mathfrak{m})$ 称为**Hensel的**，若满足Hensel引理。

**命题 4.4**。完备局部环 $⟶$ Hensel局部环 $⟶$ 局部环。

**命题 4.5**。Hensel局部环的整闭包是局部环（即只有一个极大理想位于给定极大理想之上）。

## 5. 应用

### 5.1 隐函数定理的代数类比

Hensel引理是隐函数定理的代数版本：在完备局部环中，"横截相交"（Jacobi可逆）保证了方程解的存在性和唯一性。

### 5.2 提升幂等元

**定理 5.1**。设 $R$ 完备于 $I$，$\bar{e} \in R/I$ 为幂等元。则存在唯一幂等元 $e \in R$ 使 $e \equiv \bar{e} \pmod{I}$。

这导致：完备半局部环可分解为局部环的直积。

### 5.3 $p$-进分析

在 $\mathbb{Q}_p$ 中，Hensel引理用于证明平方剩余、单位根等的结构。例如，$x^2 = a$ 在 $\mathbb{Q}_p$ 中有解当且仅当 $a = p^{2n}u$，$u \in \mathbb{Z}_p^\times$ 且 $\bar{u}$ 为模 $p$ 的平方（$p$ 奇）。

## 6. 与项目其他部分的关联

完备化与Hensel引理是交换代数通向分析学和数论的桥梁。$p$-进数 $\mathbb{Q}_p$ 在数论和表示论中具有核心地位。形式幂级数环 $k[[x_1, \ldots, x_n]]$ 是奇点理论和形变理论的基础。在代数几何（见`docs/02-代数结构/范畴论/08-范畴论在代数几何中的应用.md`）中，完备局部环用于研究概形的局部性质和形式邻域。在泛函分析（见`docs/03-分析学/03-泛函分析/`）中，Banach空间的完备化与环的adic完备化共享相同的范畴论框架（滤过极限）。局部化（见[01-局部化](01-局部化.md)）和完备化是研究局部性质的两大工具。

## 7. 参考文献

1. K. Hensel, "Über eine neue Begründung der Theorie der algebraischen Zahlen", *Jahresber. DMV* 6 (1897), 83–88.
2. I.S. Cohen, "On the structure and ideal theory of complete local rings", *Trans. AMS* 59 (1946), 54–106.
3. H. Matsumura, *Commutative Ring Theory*, Cambridge University Press, 1986.
4. J.-P. Serre, *Local Fields*, Springer, 1979.
5. 冯克勤，《交换代数基础》，高等教育出版社，1985。
