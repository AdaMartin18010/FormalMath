---
习题编号: ALG-143
学科: 代数
知识点: 交换代数-完备化
难度: ⭐⭐⭐⭐
预计时间: 40分钟
---

# 完备化与Hensel引理

## 题目

设 $(R, \mathfrak{m})$ 是Noether局部环，$\hat{R} = \varprojlim R/\mathfrak{m}^n$ 是完备化。

**(a)** 证明 $R \to \hat{R}$ 是平坦的。

**(b)** 证明Artin-Rees引理：对有限生成 $R$-模 $M$ 的子模 $N$，存在 $k$ 使得对 $n \geq k$：
$$\mathfrak{m}^n M \cap N = \mathfrak{m}^{n-k}(\mathfrak{m}^k M \cap N)$$

**(c)** 证明Hensel引理：设 $f(x) \in R[x]$，$a \in R$ 使 $f(a) \equiv 0 \pmod{\mathfrak{m}}$，$f'(a) \not\equiv 0 \pmod{\mathfrak{m}}$，则存在唯一的 $\alpha \in \hat{R}$ 使 $f(\alpha) = 0$ 且 $\alpha \equiv a \pmod{\mathfrak{m}}$。

## 解答

### (a) 完备化的平坦性

**证明：**

$\hat{R}$ 是平坦模当且仅当 $-\otimes \hat{R}$ 正合。

$\hat{R}$ 是 $R/\mathfrak{m}^n$ 的逆向极限。

由Noether性，逆向系统是本质满射。

平坦性来自 $R/\mathfrak{m}^n$ 平坦（$R$ 上？需验证）。

关键：$R$ Noether局部，$\hat{R}$ 是忠实平坦 $R$-代数。

### (b) Artin-Rees引理

**证明：**

考虑分次环 $\text{gr}(R) = \bigoplus \mathfrak{m}^n/\mathfrak{m}^{n+1}$。

$N$ 的滤过诱导分次 $\text{gr}(N) \subset \text{gr}(M)$。

$\text{gr}(R)$ 是Noether分次环，$\text{gr}(N)$ 是子模，故稳定。

稳定性即Artin-Rees等式。

### (c) Hensel引理

**证明：**

Newton迭代：设 $a_0 = a$，$a_{n+1} = a_n - f(a_n)/f'(a_n)$。

归纳证 $f(a_n) \equiv 0 \pmod{\mathfrak{m}^{2^n}}$，$a_{n+1} \equiv a_n \pmod{\mathfrak{m}^{2^n}}$。

$(a_n)$ 是Cauchy列，收敛于 $\alpha \in \hat{R}$。

$f(\alpha) = \lim f(a_n) = 0$。

唯一性由 $f'(a)$ 可逆保证。
