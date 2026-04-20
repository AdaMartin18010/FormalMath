---
msc_primary: 00A99
习题编号: ALG-215
学科: 代数
知识点: 表示论-Schur函子
难度: ⭐⭐⭐⭐⭐
预计时间: 50分钟
---

# Schur 函子

## 题目

**(a)** 定义 Schur 函子 $S^\lambda(V)$ 并证明其函子性。

**(b)** 证明 Cauchy 公式和 Littlewood-Richardson 规则。

**(c)** 讨论 Schur 多项式和对称函数理论。

## 解答

### (a) Schur 函子

**设置**：$V$ 是复向量空间，$\lambda = (\lambda_1 \geq \lambda_2 \geq \cdots \geq \lambda_k > 0)$ 是 $n$ 的分拆，$|\lambda| = n$。

**Young 表**：Young 图是左对齐的行，第 $i$ 行 $\lambda_i$ 个格子。

**对称群表示**：$S^\lambda$ 是对应 $\lambda$ 的 $S_n$ 不可约表示（Specht 模）。

**Schur 函子**：

$$S^\lambda(V) = V^{\otimes n} \otimes_{\mathbb{C}[S_n]} S^\lambda$$

**函子性**：$S^\lambda$ 是多项式函子。对线性映射 $T: V \to W$：

$$S^\lambda(T): S^\lambda(V) \to S^\lambda(W)$$

由 $T^{\otimes n}$ 在 $V^{\otimes n}$ 上诱导。

**$GL(V)$ 作用**：$S^\lambda(V)$ 是 $GL(V)$-表示，最高权 $(\lambda_1, \ldots, \lambda_k, 0, \ldots)$。

**特例**：

- $\lambda = (n)$：$S^{(n)}(V) = S^n V$（对称幂）
- $\lambda = (1^n)$：$S^{(1^n)}(V) = \Lambda^n V$（外幂）

---

### (b) Cauchy 公式与 LR 规则

**Cauchy 公式**：

$$\prod_{i,j} \frac{1}{1-x_i y_j} = \sum_\lambda s_\lambda(x) s_\lambda(y)$$

其中 $s_\lambda$ 是 Schur 多项式。

*证明*：$GL(V) \times GL(W)$ 作用在 $S(V \otimes W)$ 上，分解为 $S^\lambda(V) \otimes S^\lambda(W)$。

**Littlewood-Richardson 规则**：

$$s_\mu \cdot s_\nu = \sum_\lambda c^\lambda_{\mu\nu} s_\lambda$$

$c^\lambda_{\mu\nu}$ 是 LR 系数。

**组合描述**：$c^\lambda_{\mu\nu}$ 等于在 $\mu$ 上添加 $\nu$ 形状的 skew tableau，满足：

1. 是 semistandard（行弱增，列严格增）
2. 词（reading word）是 lattice permutation（任意前缀中 $i$ 的个数 $\geq i+1$ 的个数）

---

### (c) Schur 多项式

**定义**：$\lambda$ 分拆，$n$ 变量：

$$s_\lambda(x_1, \ldots, x_n) = \frac{\det(x_i^{\lambda_j + n - j})_{1 \leq i,j \leq n}}{\prod_{i<j}(x_i - x_j)}$$

（Vandermonde 分母）。

**等价公式**：

- **Jacobi-Trudi**：$s_\lambda = \det(h_{\lambda_i - i + j}) = \det(e_{\lambda'_i - i + j})$
  - $h_k$：完全齐次对称函数
  - $e_k$：初等对称函数
  - $\lambda'$：共轭分拆

**对称函数环**：$\Lambda = \lim_{\leftarrow} \mathbb{Z}[x_1, \ldots, x_n]^{S_n}$。

$\{s_\lambda\}$ 是 $\Lambda$ 的 $\mathbb{Z}$-基。

---

## 常见错误

- **Schur 函子的零**：若 $\lambda$ 的行数 $> \dim V$，则 $S^\lambda(V) = 0$。
- **LR 系数的非负性**：$c^\lambda_{\mu\nu} \geq 0$，但直接由定义不明显。
- **Schur 多项式的变量数**：$n < l(\lambda')$ 时 $s_\lambda(x_1, \ldots, x_n) = 0$。

## 参考文献

- Fulton & Harris, *Representation Theory*, GTM 129.
- Macdonald, *Symmetric Functions and Hall Polynomials*.
