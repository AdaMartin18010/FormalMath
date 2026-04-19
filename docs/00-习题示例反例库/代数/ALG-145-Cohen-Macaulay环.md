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

**(c)** 证明：$R$ CM当且仅当对所有素理想 $\mathfrak{p}$，$R_\mathfrak{p}$ 是CM。

## 解答

### (a) 深度-维数不等式

**证明：**

对正则序列 $x_1, \ldots, x_n$，$\dim(M/(x)M) = \dim(M) - n$。

（因正则元在 $M$ 上不是零因子，维数降1）

故 $n \leq \dim(M)$。

### (b) 正则局部环是CM

**证明：**

$(R, \mathfrak{m})$ 正则，$\mathfrak{m}$ 由正则序列 $x_1, \ldots, x_d$ 生成。

$\text{depth}(R) \geq d = \dim(R)$。

由(a)，等号成立，故CM。

### (c) CM的局部化

**证明：**

**($\Rightarrow$)**：设 $R$ CM，$\mathfrak{p}$ 素理想。

$R_\mathfrak{p}$ 的维数 = $\text{ht}(\mathfrak{p})$，深度 $\geq$ $R$ 中正则序列在 $\mathfrak{p}$ 的长度。

由CM性，相等。

**($\Leftarrow$)**：若所有局部化CM，则 $R$ 满足深度-维数等式。
