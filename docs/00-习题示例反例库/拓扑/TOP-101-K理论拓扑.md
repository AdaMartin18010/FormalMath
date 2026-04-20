---
msc_primary: 00A99
习题编号: TOP-101
学科: 拓扑
知识点: 拓扑-K理论
难度: ⭐⭐⭐⭐
预计时间: 45分钟
---

# 拓扑 K-理论

## 题目

**(a)** 证明 Bott 周期性：$\tilde{K}^0(S^2) \cong \mathbb{Z}$，$\tilde{K}^{-1}(S^2) = 0$。

**(b)** 证明 Thom 同构在 K-理论中的形式。

**(c)** 讨论 K-理论的 Chern 特征。

## 解答

### (a) Bott 周期性

**拓扑 K-理论的构造**：设 $X$ 是紧 Hausdorff 空间。$\text{Vect}_\mathbb{C}(X)$ 是复向量丛的同构类构成的交换幺半群（直和为加法）。

**Grothendieck 群**：$K^0(X)$ 是 $\text{Vect}_\mathbb{C}(X)$ 的 Grothendieck 完备化。等价地，形式差 $[E] - [F]$ 模关系 $[E] - [F] = [E'] - [F']$ 当 $E \oplus F' \cong E' \oplus F$。

约化 K-理论：$\tilde{K}^0(X) = \ker(K^0(X) \to K^0(pt) = \mathbb{Z})$（由秩映射）。

**定理（Bott 周期性）**：对紧空间 $X$：
$$\tilde{K}^0(S^2 \wedge X) \cong \tilde{K}^0(X)$$
$$\tilde{K}^{-1}(S^2 \wedge X) \cong \tilde{K}^{-1}(X)$$

即 $S^2$ 在 K-理论中给出周期 2。特别地：
$$\tilde{K}^0(S^2) \cong \mathbb{Z}, \quad \tilde{K}^{-1}(S^2) = 0$$

**证明**：

**$K^0(S^2)$ 的计算**：

$K^0(S^2)$ 由向量丛的秩和第一陈类分类。对 $S^2 = \mathbb{C}P^1$，线丛由 $c_1 \in H^2(S^2, \mathbb{Z}) \cong \mathbb{Z}$ 分类。

**万有丛**：$H = \mathcal{O}(-1)$ 是 tautological 线丛（Hopf 丛）。$c_1(H) = -1$（在标准定向下）。令 $L = H^{-1} = \mathcal{O}(1)$，$c_1(L) = 1$。

**定理**：$K^0(S^2) = \mathbb{Z}[1] \oplus \mathbb{Z}[L]$，作为环有 $(L - 1)^2 = 0$。

*证明*：由分裂原理，任何 $S^2$ 上的向量丛可写成线丛的直和（因 $S^2$ 的维数低）。线丛由 $c_1$ 分类，故 $K^0(S^2)$ 由 $[1]$ 和 $[L]$ 生成。

计算 $L \otimes L$：$c_1(L \otimes L) = c_1(L) + c_1(L) = 2$，故 $L \otimes L = L^{\otimes 2}$ 对应 $c_1 = 2$ 的线丛。由群结构，$[L]^2$ 应满足某种关系。利用 Atiyah-Bott-Shapiro 的 Clifford 模构造或直接的分类，得 $(L-1)^2 = 0$。

更直接地，考虑外代数丛：$\Lambda^*(L \oplus \bar{L})$ 给出 $K^0(S^2)$ 中的关系。或者利用 $S^2$ 是 $\mathbb{C}P^1$，$K^0(\mathbb{C}P^1) = \mathbb{Z}[x]/(x^2)$，其中 $x = [L] - 1$。

因此：
$$\tilde{K}^0(S^2) = \mathbb{Z} \cdot (L - 1) \cong \mathbb{Z}$$

**$\tilde{K}^{-1}(S^2)$**：

$$\tilde{K}^{-1}(X) = \tilde{K}^0(\Sigma X) = \tilde{K}^0(S^1 \wedge X)$$

由 Bott 周期（待证或作为已知），$\tilde{K}^{-1}(S^2) = \tilde{K}^0(S^3)$。而 $K^0(S^3) = \mathbb{Z}$（秩映射，因 $H^2(S^3) = 0$ 无线丛不变量），故 $\tilde{K}^0(S^3) = 0$。

**Bott 映射**：Bott 周期性的核心是同构：
$$\beta: \tilde{K}^0(X) \to \tilde{K}^0(S^2 \wedge X)$$

由外部积给出：$\beta(x) = x \boxtimes (L - 1)$，其中 $L - 1 \in \tilde{K}^0(S^2)$ 是 Bott 元。

Bott 的原始证明利用环路空间：$\Omega^2 BU \simeq BU \times \mathbb{Z}$（作为 H-空间），即 $BU$ 是无限环路空间，周期为 2。

### (b) K-理论的 Thom 同构

**设定**：设 $E \to X$ 是秩 $k$ 复向量丛，$\pi: E \to X$ 是投影。

**Thom 空间**：$\text{Th}(E) = D(E)/S(E)$，其中 $D(E)$ 是单位圆盘丛，$S(E)$ 是球丛。等价地，$\text{Th}(E) = E^+$（E 的一点紧化，当 $X$ 紧时）。

**定理（K-理论 Thom 同构）**：存在 **Thom 类** $\lambda_E \in \tilde{K}^0(\text{Th}(E))$，使得 cup 积给出同构：
$$\cup \lambda_E: K^0(X) \xrightarrow{\cong} \tilde{K}^0(\text{Th}(E))$$

等价地：$K^0(E, E \setminus 0) \cong K^0(X)$。

**Thom 类的构造**：

对复向量丛 $E$，考虑外代数丛 $\Lambda^*(E) = \Lambda^0(E) \oplus \Lambda^1(E) \oplus \cdots \oplus \Lambda^k(E)$。在每点 $x \in X$，$\Lambda^*(E_x)$ 是 $\mathbb{Z}/2$-分次向量空间（偶/奇次）。

Clifford 乘法 $v \wedge - + i_v(-)$（$v \in E_x$）给出 $E$ 在 $\Lambda^*(E)$ 上的作用。这在 $E$ 的每点定义了类：
$$\lambda_E = [\Lambda^{even}(E)] - [\Lambda^{odd}(E)] \in K^0(X)$$

但需要提升到相对 K-理论。利用 $E$ 的复结构，定义：
$$\lambda_E = \sum_{i=0}^k (-1)^i [\Lambda^i(E)] \in \tilde{K}^0(\text{Th}(E))$$

这是 $K$-理论的 **Euler 类**的类比。实际上 $\lambda_E$ 限制到每纤维是 $K^0(\mathbb{C}^k, \mathbb{C}^k \setminus 0) \cong \tilde{K}^0(S^{2k}) \cong \mathbb{Z}$ 的生成元（Bott 周期性的迭代）。

**证明 Thom 同构**：

对平凡丛 $E = X \times \mathbb{C}^k$，$\text{Th}(E) = X_+ \wedge S^{2k}$。由 Bott 周期性：
$$\tilde{K}^0(\text{Th}(E)) = \tilde{K}^0(S^{2k} \wedge X_+) \cong \tilde{K}^0(X)$$

Thom 类对应 $1 \in K^0(X)$ 在此同构下的像。

对一般丛，利用 Mayer-Vietoris 和平凡化覆盖。设 $\{U_i\}$ 是 $X$ 的覆盖使 $E|_{U_i}$ 平凡。在交集上 Thom 类由转移函数粘合，利用 $K$-理论的可缩性保证一致性。

**与上同调 Thom 同构的比较**：

在通常上同调中，Thom 同构为 $H^i(X) \cong H^{i+2k}(\text{Th}(E))$。在 K-理论中，由于 Bott 周期性，维数偏移被"吸收"：$K^0$ 到 $K^0$（不偏移）。这反映 K-理论是"周期性"上同调理论。

### (c) Chern 特征

**定义**：Chern 特征是从 K-理论到有理上同调的环同态：
$$\text{ch}: K^0(X) \to H^{even}(X; \mathbb{Q}) = \bigoplus_{i=0}^\infty H^{2i}(X; \mathbb{Q})$$

**分裂原理**：对复向量丛 $E \to X$，存在 $f: Y \to X$ 使 $f^*E$ 分裂为线丛的直和 $L_1 \oplus \cdots \oplus L_k$，且 $f^*: H^*(X) \to H^*(Y)$ 是单射。

由分裂原理，只需在线丛上定义 ch，然后延拓。

**在线丛上的定义**：设 $L$ 是线丛，$x = c_1(L) \in H^2(X; \mathbb{Z})$。定义：
$$\text{ch}(L) = e^x = 1 + x + \frac{x^2}{2!} + \frac{x^3}{3!} + \cdots$$

（因 $x$ 幂零到某阶，这是有限和。）

对一般丛 $E = L_1 \oplus \cdots \oplus L_k$，形式上写 $c(E) = \prod(1 + x_i)$，$x_i = c_1(L_i)$。则：
$$\text{ch}(E) = \sum_{i=1}^k e^{x_i}$$

**定理**：$\text{ch}$ 是环同态：$\text{ch}(E \oplus F) = \text{ch}(E) + \text{ch}(F)$，$\text{ch}(E \otimes F) = \text{ch}(E) \smile \text{ch}(F)$。

*证明*：由分裂原理，设 $E = \bigoplus L_i$，$F = \bigoplus M_j$。则：
$$E \otimes F = \bigoplus_{i,j} L_i \otimes M_j$$
$$\text{ch}(E \otimes F) = \sum_{i,j} e^{x_i + y_j} = \sum_i e^{x_i} \sum_j e^{y_j} = \text{ch}(E) \text{ch}(F)$$

**Chern 特征的核与像**：

**定理（Atiyah-Hirzebruch）**：对有限 CW 复形 $X$，$\text{ch}: K^0(X) \otimes \mathbb{Q} \to H^{even}(X; \mathbb{Q})$ 是同构。

*证明*：对 $X = pt$，$K^0(pt) = \mathbb{Z}$，$\text{ch}(1) = 1$。对 $S^{2n}$，$\tilde{K}^0(S^{2n}) \cong \mathbb{Z}$，$\tilde{H}^{even}(S^{2n}; \mathbb{Q}) = \mathbb{Q}$，ch 是同构（Bott 元的 ch 是生成元的适当倍数）。由五引理和 CW 结构归纳。∎

**应用**：

- **指标定理**：Atiyah-Singer 指标定理用 ch 和 Todd 类表示椭圆算子的解析指标：
  $$\text{ind}(D) = \int_X \text{ch}(E) \cdot \text{Td}(TX)$$

- **Riemann-Roch 定理**：对光滑射影簇间的态射 $f: X \to Y$，Grothendieck-Riemann-Roch 公式：
  $$\text{ch}(f_!E) \cdot \text{Td}(Y) = f_*(\text{ch}(E) \cdot \text{Td}(X))$$

**常见错误**：
- 将 ch 的定义域误认为 $K^0(X)$ 本身而非 $K^0(X) \otimes \mathbb{Q}$：ch 的像在 $H^{even}(X; \mathbb{Q})$，可能有分母。例如 $ch(\mathbb{C}P^n$ 上的 tautological 丛) 含 $1/n!$ 系数。
- 混淆 K-理论的 Thom 类与上同调的 Thom 类：K-理论的 $\lambda_E$ 在 ch 下映到上同调 Thom 类，但自身不是 Euler 类的直接类比。
- 忽视 Bott 周期性的方向：$\tilde{K}^0(S^{2n}) \cong \mathbb{Z}$，$\tilde{K}^1(S^{2n}) = 0$；$\tilde{K}^0(S^{2n+1}) = 0$，$\tilde{K}^1(S^{2n+1}) \cong \mathbb{Z}$。

**参考文献**：
- M. Atiyah, *K-Theory*, Benjamin, 1967
- M. Atiyah, F. Hirzebruch, "Vector bundles and homogeneous spaces", *Proc. Symp. Pure Math.* 1961
- R. Bott, "The stable homotopy of the classical groups", *Ann. Math.* 1959
- M. Karoubi, *K-Theory: An Introduction*, Springer, 1978
