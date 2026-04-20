---
msc_primary: 00A99
习题编号: ALG-207
学科: 代数
知识点: 表示论-Lie代数
难度: ⭐⭐⭐⭐
预计时间: 45分钟
---

# Lie 代数表示

## 题目

**(a)** 证明 Engel 定理和 Lie 定理。

**(b)** 定义 Cartan 子代数并证明其共轭性。

**(c)** 计算 $\mathfrak{sl}(2, \mathbb{C})$ 的有限维不可约表示。

## 解答

### (a) Engel 与 Lie 定理

**Engel 定理**：设 $L$ 是有限维 Lie 代数，则 $L$ 幂零当且仅当 $\operatorname{ad}_x$ 是幂零线性变换对所有 $x \in L$ 成立。

*证明*：对 $\dim L$ 归纳。当 $\dim L = 1$ 时显然。假设对维数小于 $n$ 的 Lie 代数成立。

取 $L$ 的极大真子代数 $K \subset L$。$K$ 通过 $\operatorname{ad}$ 作用在商空间 $L/K$ 上。由归纳假设，每个 $\operatorname{ad}_x|_{L/K}$ 幂零，故存在 $y \notin K$ 使得 $[K, y] \subset K$，即 $K$ 是理想。

若 $L/K$ 一维，$K$ 是余维一理想。由归纳 $K$ 幂零，$L = K + \mathbb{C}z$，$\operatorname{ad}_z|_K$ 幂零。由 Lie 代数扩张理论，$L$ 幂零。

**Lie 定理**：设 $L$ 是可解 Lie 代数，$\rho: L \to \mathfrak{gl}(V)$ 是有限维表示，$V$ 是代数闭域上向量空间。则存在 $V$ 的基使得所有 $\rho(x)$ 上三角化。

*证明*：对 $\dim V$ 归纳。需找 $v \neq 0$ 使得 $\rho(x)v = \lambda(x)v$。关键引理：若 $I \triangleleft L$ 理想，$W$ 是 $I$ 的公共特征空间，则 $W$ 是 $L$ 不变的。

取 $I = [L, L]$。由可解性 $[L, L] \neq L$。对 $I$ 用归纳，$W = \{v : \rho(y)v = \lambda(y)v, \forall y \in I\}$ 非零且 $L$ 不变。商 $L/I$ 是 Abel 的，故在 $W$ 上可对角化，得到一维特征空间。

---

### (b) Cartan 子代数

**定义**：$H \subset L$ 是 **Cartan 子代数**，若：

1. $H$ 是幂零子代数
2. $H = N_L(H)$（自正规化）

**存在性**：对任意 $x \in L$，考虑特征空间分解 $L = \bigoplus_\alpha L_\alpha(\operatorname{ad}_x)$。取 **正则元** $x$（使 $\dim L_0(\operatorname{ad}_x)$ 极小），则 $H = L_0(\operatorname{ad}_x)$ 是 Cartan 子代数。

**共轭性定理**：设 $L$ 是有限维 Lie 代数，$H_1, H_2$ 是 Cartan 子代数，则存在 $\sigma \in \operatorname{Aut}(L)$（内自同构群的闭包）使得 $\sigma(H_1) = H_2$。

*证明概要*（Chevalley）：分两步：

**半单情形**：此时 Cartan 子代数是极大环面子代数。设 $\mathfrak{h}_1, \mathfrak{h}_2$ 是极大环面子代数。对根系 $\Phi$，$L = \mathfrak{h} \oplus \bigoplus_{\alpha \in \Phi} L_\alpha$。Weyl 群 $W$ 通过内自同构作用，且任意两个正根系通过 $W$ 共轭，从而极大环面共轭。

**一般情形**：利用 Levi 分解 $L = R \rtimes S$，其中 $R$ 是根（极大可解理想），$S$ 是半单。Cartan 子代数在 $L/R$ 中对应半单的 Cartan，利用提升得到共轭性。

---

### (c) $\mathfrak{sl}(2, \mathbb{C})$ 的表示

**标准基**：

$$
h = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}, \quad
e = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}, \quad
f = \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix}
$$

满足 $[h, e] = 2e, \; [h, f] = -2f, \; [e, f] = h$。

**不可约表示 $V_m$**：对 $m \in \mathbb{N}$，$V_m$ 是 $m+1$ 维空间，基 $\{v_0, v_1, \ldots, v_m\}$，作用为：

$$
\begin{aligned}
h \cdot v_k &= (m - 2k) v_k, \\
e \cdot v_k &= (m - k + 1) v_{k-1}, \\
f \cdot v_k &= (k + 1) v_{k+1}.
\end{aligned}
$$

其中约定 $v_{-1} = v_{m+1} = 0$。

**证明不可约**：设 $W \subset V_m$ 是非零子表示。取 $w \in W$ 是 $h$ 的特征向量：$w = \sum c_k v_k$，$h \cdot w = \lambda w$。

由 $e, f$ 反复作用，生成的轨道包含所有基向量（因为系数 $(m-k+1), (k+1)$ 非零），故 $W = V_m$。

**分类定理**：$\mathfrak{sl}(2, \mathbb{C})$ 的有限维不可约表示同构类一一对应于 $\{V_m : m = 0, 1, 2, \ldots\}$。

*证明*：对任意有限维表示 $V$，$h$ 可对角化（因 $h$ 半单）。设 $\lambda$ 是最大特征值（**最高权**），$v$ 是最高权向量：$h \cdot v = \lambda v$，$e \cdot v = 0$。

由 $f$ 作用得 $f^k \cdot v$，$h$ 特征值递减 $\lambda - 2k$。因 $V$ 有限维，存在 $m$ 使 $f^{m+1} \cdot v = 0$，$f^m \cdot v \neq 0$。

由 $[e, f] = h$ 归纳得 $e \cdot (f^k v) = k(\lambda - k + 1) f^{k-1} v$。对 $k = m+1$：

$$
0 = e \cdot (f^{m+1} v) = (m+1)(\lambda - m) f^m v
$$

因 $f^m v \neq 0$，得 $\lambda = m \in \mathbb{N}$。子空间 $\operatorname{span}\{f^k v : k = 0, \ldots, m\}$ 是 $m+1$ 维不可约子表示，恰为 $V_m$。由 Weyl 完全可约性定理，半单 Lie 代数的有限维表示完全可约，故分类得证。

**Casimir 元**：

$$
C = \frac{1}{2}h^2 + ef + fe = \frac{1}{2}h^2 + h + 2fe \in U(\mathfrak{sl}_2)
$$

在 $V_m$ 上作用为标量 $\frac{m(m+2)}{2}$，是表示不变量。

---

## 常见错误

- **混淆幂零与可解**：幂零 Lie 代数必可解，反之不成立（如二维非 Abel Lie 代数）。
- **忽略代数闭域条件**：Lie 定理需代数闭域，否则需域扩张。
- **误认为所有表示完全可约**：仅对 **半单** Lie 代数成立（Weyl 定理），可解代数不一定。
- **特征值计算错误**：$\mathfrak{sl}(2)$ 表示中 $h$ 特征值必须同为奇偶性，跨度为 $m, m-2, \ldots, -m$。

## 参考文献

- Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9.
- Fulton & Harris, *Representation Theory: A First Course*, GTM 129.
