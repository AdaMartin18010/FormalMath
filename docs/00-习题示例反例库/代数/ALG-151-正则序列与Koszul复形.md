---
msc_primary: 00A99
习题编号: ALG-151
学科: 代数
知识点: 交换代数-Koszul复形
难度: ⭐⭐⭐⭐
预计时间: 40分钟
---

# 正则序列与Koszul复形

## 题目

**(a)** 定义 $M$-正则序列 $x_1, \ldots, x_n$，并讨论其与深度的关系。

**(b)** 定义Koszul复形 $K(x; M)$，证明 $H_i(K(x; M)) = 0$ 对 $i > 0$ 当 $x$ 是 $M$-正则序列。

**(c)** 用Koszul复形计算 $\operatorname{Tor}_i^R(R/I, M)$。

## 解答

### (a) 正则序列与深度

**定义**：设 $R$ 是交换环，$M$ 是 $R$-模。序列 $x_1, \ldots, x_n \in R$ 是 **$M$-正则序列**（或 $M$-sequence），若：

1. $x_1$ 在 $M$ 上非零因子：$x_1 m = 0 \Rightarrow m = 0$
2. $x_2$ 在 $M/x_1 M$ 上非零因子
3. 依此类推：$x_i$ 在 $M/(x_1, \ldots, x_{i-1})M$ 上非零因子
4. $(x_1, \ldots, x_n)M \neq M$

**深度**：设 $I \subset R$ 是理想，$M$ 是有限生成 $R$-模。

$$
\operatorname{depth}_I(M) = \inf\{i : \operatorname{Ext}_R^i(R/I, M) \neq 0\}
$$

等价地，是 $I$ 中 $M$-正则序列的最大长度。

**关键定理**：

- **Auslander-Buchsbaum 公式**（正则局部环 $R$）：$\operatorname{pd}_R(M) + \operatorname{depth}(M) = \operatorname{depth}(R) = \dim R$
- **深度与维数不等式**：$\operatorname{depth}(M) \leq \dim(M) = \dim(R/\operatorname{Ann}(M))$
- **Cohen-Macaulay 模**：$\operatorname{depth}(M) = \dim(M)$

**正则序列的性质**：

- 正则序列的顺序在局部环上可交换（当模有限生成时）
- $x_1, \ldots, x_n$ 正则 $\Rightarrow$ 理想 $(x_1, \ldots, x_n)$ 的高为 $n$
- 正则序列生成完全交理想（若 $R$ 正则局部）

---

### (b) Koszul 复形

**构造**：设 $x = (x_1, \ldots, x_n) \in R^n$。Koszul 复形 $K(x; R)$ 是外代数 $\Lambda^* R^n$ 上的链复形。

$K_p = \Lambda^p R^n$（秩 $\binom{n}{p}$ 的自由模），微分：

$$
d_p(e_{i_1} \wedge \cdots \wedge e_{i_p}) = \sum_{j=1}^p (-1)^{j-1} x_{i_j} e_{i_1} \wedge \cdots \wedge \hat{e}_{i_j} \wedge \cdots \wedge e_{i_p}
$$

即由 $x$ 决定的内缩算子。$K(x; M) = K(x; R) \otimes_R M$。

**同调计算**：

$$H_0(K(x; M)) = M/(x)M$$
$$H_n(K(x; M)) = \{m \in M : x_i m = 0, \forall i\} = \operatorname{Ann}_M(x)$$

**定理**：若 $x_1, \ldots, x_n$ 是 $M$-正则序列，则 $H_i(K(x; M)) = 0$ 对所有 $i > 0$。

*证明*（归纳）：$n=1$ 时 $K(x_1; M): 0 \to M \xrightarrow{x_1} M \to 0$，$H_1 = \ker(x_1) = 0$（正则），$H_0 = M/x_1 M$。

$n > 1$：分解 $K(x_1, \ldots, x_n; M) = K(x_n; R) \otimes K(x_1, \ldots, x_{n-1}; M)$。利用映射锥和归纳假设，正则性保证同调消失。

---

### (c) Tor 计算

**定理**：若 $x_1, \ldots, x_n$ 是 $R$-正则序列，$I = (x_1, \ldots, x_n)$，则 Koszul 复形 $K(x; R)$ 给出 $R/I$ 的自由分解：

$$
\cdots \to K_2 \to K_1 \to K_0 = R \to R/I \to 0
$$

即 $R/I$ 的 **Koszul 分解**。

**Tor 计算**：

$$
\operatorname{Tor}_i^R(R/I, M) = H_i(K(x; R) \otimes_R M) = H_i(K(x; M))
$$

当 $x$ 是 $M$-正则序列时，$\operatorname{Tor}_i^R(R/I, M) = 0$ 对 $i > 0$，即 $R/I$ 是 $M$-正则序列的商。

**应用**：正则局部环中，正则序列生成的理想 $I$ 的余维数等于生成元个数，$R/I$ 也是 Cohen-Macaulay。

---

## 常见错误

- **正则序列不可随意重排**：一般环上正则序列的顺序不可交换，但 **Noether 局部环**上有限生成模的正则序列可重排。
- **忽略 $(x)M \neq M$ 条件**：否则空序列也满足条件，深度定义为无穷。
- **混淆 Koszul 复形与 de Rham 复形**：前者基于外代数内缩，后者基于微分形式外微分。

## 参考文献

- Matsumura, *Commutative Ring Theory*, Cambridge.
- Eisenbud, *Commutative Algebra*, GTM 150, 第 17 章.
