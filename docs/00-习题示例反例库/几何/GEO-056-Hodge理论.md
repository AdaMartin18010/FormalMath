---
msc_primary: 00A99
习题编号: GEO-056
学科: 几何
知识点: 几何-Hodge理论
难度: ⭐⭐⭐⭐
预计时间: 45分钟
---

# Hodge 理论深入

## 题目

**(a)** 证明 Lefschetz 分解定理。

**(b)** 讨论 Hodge-Riemann 双线性关系。

**(c)** 证明 hard Lefschetz 定理。

---

## 解答

### (a) Lefschetz分解

#### Hard Lefschetz

设 $X$ 是 $n$ 维紧Kähler流形，$\omega$ 是Kähler形式。

**算子**：
- $L = \omega \wedge \cdot$: $H^k(X, \mathbb{C}) \to H^{k+2}(X, \mathbb{C})$
- $\Lambda = L^*$: adjoint
- $H = [L, \Lambda]$: 计数算子

**Hard Lefschetz定理**：
$$L^{n-k}: H^k(X, \mathbb{C}) \xrightarrow{\cong} H^{2n-k}(X, \mathbb{C})$$

#### Lefschetz分解

**本原上同调**：
$$P^k = \ker(\Lambda: H^k \to H^{k-2}) = \ker(L^{n-k+1}: H^k \to H^{2n-k+2})$$

**定理**：
$$H^k(X, \mathbb{C}) = \bigoplus_{j \geq 0} L^j P^{k-2j}$$

**证明**：由 $\mathfrak{sl}_2(\mathbb{C})$ 表示论。

$(L, \Lambda, H)$ 满足：
$$[H, L] = 2L, \quad [H, \Lambda] = -2\Lambda, \quad [L, \Lambda] = H$$

这是 $\mathfrak{sl}_2$ 的标准生成关系。

$\mathfrak{sl}_2$ 的有限维表示完全可约，最高权向量即本原上同调。

$\square$

---

### (b) Hodge-Riemann双线性关系

#### Hodge分解

$$H^k(X, \mathbb{C}) = \bigoplus_{p+q=k} H^{p,q}(X)$$

其中 $H^{p,q}$ 是调和 $(p,q)$-形式。

#### 本原形式的内积

对 $\alpha, \beta \in P^{p,q}$（$p+q = k$），定义：
$$Q(\alpha, \beta) = i^{p-q}(-1)^{k(k-1)/2} \int_X \alpha \wedge \bar{\beta} \wedge \omega^{n-k}$$

**Hodge-Riemann双线性关系**：
1. $Q(H^{p,q}, H^{p',q'}) = 0$（$(p,q) \neq (q',p')$）
2. $Q$ 在 $P^{p,q}$ 上正定（$(-1)^{k(k-1)/2} i^{p-q} Q(\alpha, \bar{\alpha}) > 0$）

#### 推论

- **Hodge指标的符号**：$H^{n,n}(X)$ 上的相交形式符号可由Hodge-Riemann确定
- **Kähler package**：Lefschetz分解 + Hodge-Riemann + Hard Lefschetz 构成Kähler几何的代数核心

---

### (c) Hard Lefschetz的证明

#### Kähler恒等式

**定理**：$[L, d^*] = 0$，$[\Lambda, d] = 0$（在适当意义下）。

更精确地：
- $[L, \bar{\partial}^*] = -i\partial$
- $[\Lambda, \partial] = i\bar{\partial}^*$

#### Laplacian的交换性

**定理**：$\Delta_d = 2\Delta_\partial = 2\Delta_{\bar{\partial}}$。

故调和形式同时是 $\partial$-调和和 $\bar{\partial}$-调和的。

#### Hard Lefschetz的证明

**步骤1**：$L$ 与Laplacian交换

$[L, \Delta] = 0$，故 $L$ 将调和形式映到调和形式。

**步骤2**：$\mathfrak{sl}_2$ 作用**

$(L, \Lambda, H)$ 在调和形式上作用，满足 $\mathfrak{sl}_2$ 关系。

**步骤3**：表示论**

$\mathfrak{sl}_2$ 的有限维表示由最高权分类。

$L^{n-k}: H^k \to H^{2n-k}$ 是同构，因为它对应于表示论中的"最低权到最高权"映射。

$\square$

#### 推广

- **mixed Hodge结构**：Deligne将Hodge理论推广到代数簇（不必光滑或紧）
- **$p$-adic Hodge理论**：Fontaine, Faltings, Scholze等的 $p$-adic 类比
- **非交换Hodge理论**：Kontsevich-Soibelman的推广