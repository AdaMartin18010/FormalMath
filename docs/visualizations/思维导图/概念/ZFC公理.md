---
msc_primary: 03E30
msc_secondary:
  - 03E25
  - 03E35
  - 03E45
title: ZFC公理
processed_at: '2026-04-05'
---

# ZFC 公理系统

## 1. 集合论的动因

19 世纪末，Cantor 创立了集合论，为数学提供了统一的基础语言。然而，朴素集合论中的**悖论**（如 Russell 悖论）表明需要严格的公理化。Zermelo-Fraenkel 集合论 with Choice（ZFC）成为现代数学的标准基础。

**Russell 悖论**. 考虑"所有不包含自身的集合的集合"$R = \{x : x \notin x\}$。则 $R \in R \iff R \notin R$，矛盾。

## 2. ZFC 公理

### 2.1 外延公理（Extensionality）

$$\forall x \forall y (\forall z (z \in x \leftrightarrow z \in y) \to x = y).$$

**意义**：集合由其元素唯一确定。

### 2.2 空集公理（Empty Set）

$$\exists x \forall y (y \notin x).$$

记此唯一集合为 $\varnothing$。

### 2.3 配对公理（Pairing）

$$\forall x \forall y \exists z \forall w (w \in z \leftrightarrow (w = x \vee w = y)).$$

记 $z = \{x, y\}$。由此可定义单元素集 $\{x\} = \{x, x\}$ 和有序对 $(x, y) = \{\{x\}, \{x, y\}\}$。

### 2.4 并集公理（Union）

$$\forall x \exists y \forall z (z \in y \leftrightarrow \exists w (w \in x \wedge z \in w)).$$

记 $y = \bigcup x$。对集合 $A, B$，$A \cup B = \bigcup \{A, B\}$。

### 2.5 幂集公理（Power Set）

$$\forall x \exists y \forall z (z \in y \leftrightarrow z \subseteq x).$$

记 $y = \mathcal{P}(x)$。

### 2.6 分离公理模式（Separation/Specification）

对任意公式 $\varphi(z, w_1, \dots, w_n)$：
$$\forall x \forall \bar{w} \exists y \forall z (z \in y \leftrightarrow (z \in x \wedge \varphi(z, \bar{w}))).$$

记 $y = \{z \in x : \varphi(z, \bar{w})\}$。**注意**：这避免了 Russell 悖论——我们不能构造"所有集合的集合"，只能从一给定集合中分离子集。

### 2.7 替换公理模式（Replacement）

对任意公式 $\varphi(x, y, \bar{w})$ 表达函数关系：
$$\forall A \forall \bar{w} ((\forall x \in A \exists! y \varphi(x, y, \bar{w})) \to \exists B \forall x \in A \exists y \in B \varphi(x, y, \bar{w})).$$

**意义**：函数的像集存在。替换公理强于分离公理，允许构造大序数。

### 2.8 无穷公理（Infinity）

$$\exists x (\varnothing \in x \wedge \forall y (y \in x \to y \cup \{y\} \in x)).$$

保证存在归纳集，从而存在自然数集 $\mathbb{N} = \omega$。

### 2.9 正则公理（Foundation/Regularity）

$$\forall x (x \neq \varnothing \to \exists y (y \in x \wedge y \cap x = \varnothing)).$$

**意义**：每个非空集合都有 $\in$-极小元。排除了 $x \in x$ 和无穷降链 $\dots \in x_2 \in x_1 \in x_0$。

### 2.10 选择公理（AC）

$$\forall X \left(\forall x, y \in X (x \neq y \to x \cap y = \varnothing) \to \exists C \forall x \in X \exists! y (y \in x \cap C)\right).$$

等价形式：任何集合的非空子集族有选择函数；任何集可良序化（Zermelo 定理）；Cartesian 积非空。

## 3. ZFC 中的数学构造

由 ZFC 可构造：
- **自然数**：von Neumann 序数，$0 = \varnothing$，$n+1 = n \cup \{n\}$；
- **整数**：$\mathbb{Z} = \mathbb{N} \times \mathbb{N} / \sim$，$(a,b) \sim (c,d) \iff a+d = b+c$；
- **有理数**：$\mathbb{Q} = \mathbb{Z} \times \mathbb{Z}_{>0} / \sim$；
- **实数**：Dedekind 分割或 Cauchy 序列等价类；
- **函数**：特殊的关系（有序对的集合）。

## 4. 独立性结果

**定理 4.1（Gödel; Cohen）**.
- 若 ZFC 相容，则 ZFC+CH 相容（Gödel，1940，内模型法）；
- 若 ZFC 相容，则 ZFC+$\neg$CH 相容（Cohen，1963，力迫法）。

故连续统假设 CH 在 ZFC 中不可判定。

## 5. 参考

1. Kunen, K. (1980). *Set Theory: An Introduction to Independence Proofs*. North-Holland.
2. Jech, T. (2003). *Set Theory* (3rd ed.). Springer.
3. Halmos, P. R. (1960). *Naive Set Theory*. Van Nostrand.
