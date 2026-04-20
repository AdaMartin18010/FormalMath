---
msc_primary: 00A99
习题编号: ALG-145
学科: 代数
知识点: 交换代数-Cohen-Macaulay环
难度: ⭐⭐⭐⭐
预计时间: 45分钟
---

# Cohen-Macaulay环

## 题目

设 $(R, \mathfrak{m})$ 是Noether局部环，$M$ 是有限生成 $R$-模。

**(a)** 定义深度 $\text{depth}(M)$ 为 $M$-正则序列的最大长度。证明
$$\text{depth}(M) \leq \dim(M) = \dim(R/\text{Ann}(M))$$

**(b)** 定义Cohen-Macaulay：等号成立。证明正则局部环是CM。

**(c)** 证明：$R$ CM当且仅当对所有素理想 $\mathfrak{p}$，$R_{\mathfrak{p}}$ 是CM。

---

## 解答

### (a) 深度-维数不等式

**证明：**

对正则序列 $x_1, \ldots, x_n$，$\dim(M/(x)M) = \dim(M) - n$。

（因正则元在 $M$ 上不是零因子，维数降1）

故 $n \leq \dim(M)$。

**详细展开**：

**定义回顾**：
- **正则序列**：$x_1, ..., x_n \in \mathfrak{m}$ 是 $M$-正则序列，如果：
  1. $x_1$ 在 $M$ 上不是零因子（即 $x_1 m = 0 \Rightarrow m = 0$）
  2. $x_2$ 在 $M/x_1 M$ 上不是零因子
  3. ...
  4. $x_n$ 在 $M/(x_1, ..., x_{n-1})M$ 上不是零因子

- **深度**：$\text{depth}(M) = \sup\{n \mid \exists M\text{-正则序列 } x_1, ..., x_n\}$

- **维数**：$\dim(M) = \dim(R/\text{Ann}(M))$（Krull维数）

**证明步骤**：

设 $x_1, ..., x_n$ 是 $M$-正则序列。需证 $n \leq \dim(M)$。

**引理**：若 $x$ 是 $M$-正则元，则 $\dim(M/xM) = \dim(M) - 1$。

**引理证明**：
- 由 Krull 主理想定理，$\dim(M/xM) \geq \dim(M) - 1$
- 另一方面，若 $x$ 正则，则 $x$ 不属于任何属于 $\text{Ann}(M)$ 的极小素理想（否则 $x$ 在该素理想的局部化中为零因子）
- 因此 $x$ "切断"了一条最长的素理想链，$\dim(M/xM) \leq \dim(M) - 1$

由引理，对正则序列 $x_1, ..., x_n$：
$$\dim(M/(x_1, ..., x_n)M) = \dim(M) - n$$

由于维数非负，$\dim(M) - n \geq 0$，即 $n \leq \dim(M)$。

取上确界，$\text{depth}(M) \leq \dim(M)$。$\square$

---

### (b) 正则局部环是CM

**证明：**

$(R, \mathfrak{m})$ 正则，$\mathfrak{m}$ 由正则序列 $x_1, \ldots, x_d$ 生成。

$\text{depth}(R) \geq d = \dim(R)$。

由(a)，等号成立，故CM。

**详细展开**：

**正则局部环的定义**：

Noether局部环 $(R, \mathfrak{m})$ 是**正则的**，如果：
$$\dim_{R/\mathfrak{m}}(\mathfrak{m}/\mathfrak{m}^2) = \dim(R)$$

即极大理想的极小生成元个数等于Krull维数。

**正则序列的构造**：

设 $x_1, ..., x_d$ 是 $\mathfrak{m}$ 的极小生成集（$d = \dim(R)$）。

**断言**：$x_1, ..., x_d$ 是 $R$-正则序列。

**证明断言**：
1. $x_1$ 在 $R$ 上不是零因子：若 $x_1 a = 0$，则 $a$ 的支集在 $\text{Ass}(R)$ 中。但正则局部环是整环（正则 $\Rightarrow$ 正规 $\Rightarrow$ 整闭 $\Rightarrow$ 整环），故 $a = 0$。
2. 归纳地，$R/(x_1, ..., x_{k-1})$ 仍是正则局部环（维数 $d - k + 1$），因此 $x_k$ 在其上不是零因子。

因此 $x_1, ..., x_d$ 是正则序列，$\text{depth}(R) \geq d = \dim(R)$。

结合(a)的不等式，$\text{depth}(R) = \dim(R)$，即 $R$ 是CM。$\square$

**正则 $	o$ CM 的意义**：

正则局部环是最"光滑"的局部环。CM条件是比正则性弱得多的条件，但已经足以保证许多好的性质（如对偶性、无嵌入素理想等）。

---

### (c) CM的局部化

**证明：**

**($\Rightarrow$)**：设 $R$ CM，$\mathfrak{p}$ 素理想。

$R_{\mathfrak{p}}$ 的维数 = $\text{ht}(\mathfrak{p})$，深度 $\geq$ $R$ 中正则序列在 $\mathfrak{p}$ 的长度。

由CM性，相等。

**详细证明**：

设 $\text{depth}(R) = \dim(R) = d$。取极大正则序列 $x_1, ..., x_d \in \mathfrak{m}$。

对素理想 $\mathfrak{p}$，考虑局部化 $R_{\mathfrak{p}}$。

**维数**：$\dim(R_{\mathfrak{p}}) = \text{ht}(\mathfrak{p})$。

**深度分析**：
- 若 $x_i \in \mathfrak{p}$，则 $x_i$ 在 $R_{\mathfrak{p}}$ 中仍是正则元（局部化保持正则性）
- 设 $x_1, ..., x_k \in \mathfrak{p}$，$x_{k+1}, ..., x_d \notin \mathfrak{p}$

**关键观察**：$x_1, ..., x_k$ 可以扩展为 $R_{\mathfrak{p}}$ 的极大正则序列，且 $k = \text{ht}(\mathfrak{p})$。

这是因为 $R/(x_1, ..., x_d)$ 是零维的（Artin局部环），所以：
$$\dim(R_{\mathfrak{p}}/(x_1, ..., x_k)) = \text{ht}(\mathfrak{p}) - k$$

但 $x_{k+1}, ..., x_d$ 不在 $\mathfrak{p}$ 中，在局部化后成为可逆元，因此：
$$\dim(R_{\mathfrak{p}}/(x_1, ..., x_k)) = 0$$

故 $k = \text{ht}(\mathfrak{p}) = \dim(R_{\mathfrak{p}})$。

由于 $x_1, ..., x_k$ 是 $R_{\mathfrak{p}}$-正则序列，$\text{depth}(R_{\mathfrak{p}}) \geq k = \dim(R_{\mathfrak{p}})$。

由深度-维数不等式，$\text{depth}(R_{\mathfrak{p}}) = \dim(R_{\mathfrak{p}})$，即 $R_{\mathfrak{p}}$ 是CM。

**($\Leftarrow$)**：若所有局部化CM，则 $R$ 满足深度-维数等式。

取极大理想 $\mathfrak{m}$。由假设 $R_{\mathfrak{m}} = R$ 是CM。$\square$

---

## Cohen-Macaulay环的重要性

### 1. 无嵌入素理想

CM环没有嵌入素理想（embedded primes）。即所有 associated primes 都是极小素理想。

### 2. 一致维数

CM环的所有极小素理想具有相同的维数（= depth）。

### 3. 对偶性

CM环上有良好的对偶理论。对 $d$-维CM环 $R$，存在**典范模** $\omega_R$，使得：
$$\text{Ext}^i_R(M, \omega_R) = 0 \quad (i \neq d - \dim(M))$$

### 4. 应用

- **代数几何**：局部完全交是CM；模空间的许多构造要求CM条件
- **组合数学**：Stanley-Reisner环的CM性质与组合拓扑的Cohen-Macaulay复形对应
- **表示论**：不变量环的CM性质是经典问题（Hilbert第14问题的变体）
