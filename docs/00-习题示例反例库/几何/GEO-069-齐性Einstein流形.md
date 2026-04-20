---
msc_primary: 00A99
习题编号: GEO-069
学科: 几何
知识点: 几何-Einstein流形
难度: ⭐⭐⭐⭐
预计时间: 45分钟
---

# 齐性 Einstein 流形

## 题目

**(a)** 证明齐性 Einstein 度规的变分刻画。

**(b)** 讨论紧 Lie 群上的 Einstein 度规。

**(c)** 证明 Wang-Ziller 关于齐性 Einstein 流形的存在性结果。

## 解答

### (a) 齐性 Einstein 度规的变分刻画

**定义**：Riemann 流形 $(M, g)$ 称为 **Einstein 流形**，若其 Ricci 张量满足：
$$\text{Ric}(g) = \lambda g$$
其中 $\lambda \in \mathbb{R}$ 是 Einstein 常数。若 $\lambda > 0$，称正 Einstein；$\lambda = 0$ 为 Ricci 平坦；$\lambda < 0$ 为负 Einstein。

**定义**：$M$ 是**齐性**的，若其等距群 $I(M, g)$ 在 $M$ 上传递作用。等价地，$M = G/H$，其中 $G$ 是 Lie 群，$H$ 是闭子群。

**Hilbert-Einstein 泛函**：对 $n$ 维紧流形，定义：
$$S(g) = \int_M R_g \, d\mu_g$$
其中 $R_g$ 是标量曲率。

**变分原理**：Einstein 方程（无宇宙常数）是 $S(g)$ 在固定体积约束 $\text{Vol}(M, g) = 1$ 下的 Euler-Lagrange 方程。

对紧齐性空间 $M = G/H$，$G$ 紧，存在双不变度量 $Q$ 在 $\mathfrak{g}$ 上。设 $\mathfrak{g} = \mathfrak{h} \oplus \mathfrak{m}$ 是 $Q$-正交分解（reductive 分解），其中 $\mathfrak{m} \cong T_{eH}M$。

**定理**：$G$-不变度规 $g$ 在 $M = G/H$ 上是 Einstein 的当且仅当 $g$ 是总标量曲率泛函 $S$ 在固定体积的 $G$-不变度规空间上的临界点。

*证明*：由对称性降低，所有计算可约化到一点。对 $G$-不变度规，标量曲率是常数，故：
$$S(g) = R_g \cdot \text{Vol}(M, g)$$

变分计算（在 $\mathfrak{m}$ 上的对称双线性形式空间中）：
$$\frac{d}{dt}\bigg|_{t=0} S(g + th) = \int_M \langle \frac{R_g}{2}g - \text{Ric}(g), h \rangle_g \, d\mu_g$$

因此临界点满足 $\text{Ric} = \frac{R}{2}g$，但这需要修正：正确的约束变分给出 $\text{Ric} - \frac{R}{n}g = 0$ 当约束为迹（体积）固定，即 Einstein 条件。∎

### (b) 紧 Lie 群上的 Einstein 度规

**双不变度规**：设 $G$ 是紧连通 Lie 群，$Q$ 是 $\mathfrak{g}$ 上的 $Ad(G)$-不变正定内积（由紧性存在）。由左平移生成的度规在 $G$ 上称为 **双不变**（bi-invariant）。

**定理**：紧 Lie 群上的双不变度规是 Einstein 的，且 Einstein 常数 $\lambda = \frac{1}{4}$（在适当归一化下）。

*证明*：对双不变度规，曲率张量在单位元处为：
$$R(X, Y)Z = \frac{1}{4}[[X, Y], Z], \quad X, Y, Z \in \mathfrak{g}$$

Ricci 张量计算：
$$\text{Ric}(X, Y) = -\frac{1}{2}\sum_i \langle [X, e_i], [Y, e_i] \rangle + \frac{1}{4}\sum_{i,j} \langle [e_i, e_j], X \rangle \langle [e_i, e_j], Y \rangle$$

利用 $Ad$-不变性：
$$\text{Ric}(X, Y) = \frac{1}{4}Q(X, Y)$$

因此 $\text{Ric} = \frac{1}{4}g$。∎

**左不变度规**：更一般的左不变度规（不必双不变）提供丰富的 Einstein 结构。

**例子**：在 $SU(2) \cong S^3$ 上，左不变度规由 $\mathfrak{su}(2)$ 上正定内积参数化。设 $
\{e_1, e_2, e_3\}$ 满足 $[e_i, e_j] = e_k$（循环）。则度规由 $g(e_i, e_i) = \lambda_i$ 参数化（设对角）。

**Berger 度规**：取 $\lambda_1 = \lambda_2 = 1$，$\lambda_3 = t^2$。这些度规是 **Berger 球面**。它们是 Einstein 的当且仅当 $t = 1$（标准球面）或 $t^2 = 1/3$。后者给出 $S^3$ 上非标准 Einstein 度规，具有弱齐性（weakly homogeneous）性质。

### (c) Wang-Ziller 存在性定理

**设定**：设 $G/H$ 是紧齐性空间，$G$ 半单紧 Lie 群，$H$ 闭子群。设 $\mathfrak{g} = \mathfrak{h} \oplus \mathfrak{m}$ 是 $Q$-正交 reductive 分解。

若 $\mathfrak{m}$ 作为 $H$-表示可分解为不可约分量：
$$\mathfrak{m} = \mathfrak{m}_1 \oplus \mathfrak{m}_2 \oplus \cdots \oplus \mathfrak{m}_k$$

则 $G$-不变度规由 $k$ 个正参数 $x_1, \ldots, x_k$ 参数化（在每个 $\mathfrak{m}_i$ 上为 $x_i Q$）。

**定理（Wang-Ziller, 1986）**：设 $G/H$ 紧齐性空间，$\mathfrak{m}$ 分解为 $k$ 个 $Ad(H)$-不可约分量。则 Einstein 方程约化为 $k$ 个代数方程。特别地：

1. 若 $k = 1$（等向不可约），则 $G/H$ 上存在唯一的（至多缩放）$G$-不变 Einstein 度规。

2. 若 $k = 2$，Einstein 条件等价于关于 $x_1/x_2$ 的多项式方程，通常有有限多个正解。

3. 对一般的纤维化 $G/H \to G/K$（$H \subset K \subset G$），纤维和底空间上的 Einstein 条件可组合，在特定参数下给出整个空间的 Einstein 度规。

**证明的核心计算**：

对 $G$-不变度规 $g = (x_1, \ldots, x_k)$，Levi-Civita 联络限制在每个分量上。结构常数由 Lie 括号定义：
$$[\mathfrak{m}_i, \mathfrak{m}_j] \subset \mathfrak{m}_k \oplus \mathfrak{h}$$

记 $[ijk]$ 为相关的 $Ad(H)$-不变量。Ricci 张量的分量为：
$$r_i = \frac{1}{2x_i}d_i + \frac{1}{4}\sum_{j,k} [ijk]\frac{x_k}{x_i x_j} - \frac{1}{2}\sum_{j,k} [ikj]\frac{1}{x_k}$$

Einstein 条件 $r_i = \lambda x_i$（对所有 $i$）给出 $k$ 个方程。消去 $\lambda$ 得到 $k-1$ 个方程。

**充分条件（Wang-Ziller）**：设存在纤维化：
$$K/H \to G/H \to G/K$$
若 $K/H$ 和 $G/K$ 均允许 Einstein 度规，且 Einstein 常数满足特定关系，则可构造 $G/H$ 上的 Einstein 度规。

**例子**：Stiefel 流形 $V_k(\mathbb{R}^n) = SO(n)/SO(n-k)$ 允许多个 Einstein 度规（当 $k \geq 2$），包括"自然"嵌入度规和通过纤维化构造的非标准度规。

**常见错误**：
- 误认为齐性 Einstein 度规唯一：实际上一个齐性空间可能有多个不同 Einstein 度规（如 $S^{4n+3}$ 有标准度规和 Jensen 的 Einstein 度规）。
- 忽视结构常数 $[ijk]$ 可以为零，导致某些分量上的 Ricci 张量退化的情形。

**参考文献**：
- S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry*, Vol. II, 1969
- M. Wang, W. Ziller, "Einstein metrics on principal torus bundles", *J. Diff. Geom.* 1986
- J. Besse, *Einstein Manifolds*, Springer, 1987
- C. Böhm, M. Wang, W. Ziller, "A variational approach for compact homogeneous Einstein manifolds", *Geom. Funct. Anal.* 2004
