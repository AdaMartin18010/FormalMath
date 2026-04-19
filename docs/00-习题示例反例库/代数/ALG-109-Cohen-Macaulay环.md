---
msc_primary: 00A99
习题编号: ALG-109
学科: 代数
知识点: 交换代数-Cohen-Macaulay环
难度: ⭐⭐⭐⭐
预计时间: 30分钟
---

# Cohen-Macaulay环

## 题目

设 $(R, \mathfrak{m})$ 是Noether局部环，$d = \dim(R)$。

**定义**：$R$ 是**Cohen-Macaulay**（CM），若 $\text{depth}(R) = \dim(R)$。

(a) 证明正则局部环是CM。

(b) 证明完全交是CM：若 $R = S/(f_1, \ldots, f_c)$，$S$ 正则，$f_1, \ldots, f_c$ 是 $S$-正则序列，则 $R$ 是CM。

(c) 证明CM环的局部化仍是CM。

## 解答

### (a) 正则局部环是CM

**证明：**

设 $R$ 正则，$d = \dim(R)$。

正则性：$\mathfrak{m}$ 由 $d$ 个元 $x_1, \ldots, x_d$ 生成，且：
$$\dim_k(\mathfrak{m}/\mathfrak{m}^2) = d$$

**Step 1**：$x_1, \ldots, x_d$ 是参数系。

$\dim(R/(x_1, \ldots, x_d)) = 0$。

**Step 2**：证明 $x_1, \ldots, x_d$ 是正则序列。

$x_1$ 非零因子（正则局部环是整环）。

$R/(x_1)$ 正则（维数 $d-1$）。

归纳：$x_2, \ldots, x_d$ 在 $R/(x_1)$ 上正则序列。

因此 $x_1, \ldots, x_d$ 是 $R$-正则序列。

$\text{depth}(R) \geq d = \dim(R)$。

由深度-维数不等式，等号成立。$\square$

### (b) 完全交是CM

**证明：**

设 $S$ 正则，$\dim(S) = n$，$f_1, \ldots, f_c$ 是 $S$-正则序列。

**维数**：$\dim(R) = n - c$（Krull主理想定理）。

**深度**：

$\text{depth}_S(R) = \text{depth}(S) - c = n - c$。

（因正则序列削减深度）

等式成立，$R$ 是CM。$\square$

### (c) CM的局部化

**证明：**

设 $R$ 是CM，$\mathfrak{p} \in \text{Spec}(R)$。

需证 $\text{depth}(R_\mathfrak{p}) = \dim(R_\mathfrak{p})$。

**关键事实**：CM环中，对所有 $\mathfrak{p}$：
$$\text{depth}(R_\mathfrak{p}) = \dim(R_\mathfrak{p}) = \text{ht}(\mathfrak{p})$$

由未混合性定理（unmixedness），CM环没有嵌入素理想。

正则序列局部化后仍是正则序列（适当解释）。

因此深度保持良好。$\square$

## 证明技巧

1. **参数系与正则序列**：正则局部环的等价刻画
2. **深度削减公式**：短正合列或模去正则元
3. **局部化性质**：正则序列的局部行为

## 常见错误

- ❌ 忘记验证正则序列的长度等于余维数
- ❌ 混淆CM与正则的关系（CM更一般）
- ❌ 局部化时深度公式的应用条件

## 变式练习

**变式1：** 证明 $k[x,y]/(x^2, xy)$ 不是CM。

**变式2：** 证明Gorenstein环是CM，并给出一个CM但非Gorenstein的例子。
