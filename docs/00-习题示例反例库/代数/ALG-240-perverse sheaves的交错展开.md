---
msc_primary: 32

  - 32S60
exercise_id: ALG-240
title: perverse sheaves的交错展开
difficulty: 4
type: PRF
topic: 代数
subtopic: 几何表示论
source:
  course: 研究级课程
  chapter: "1.0"
  original: true
processed_at: '2026-04-10'
---

# ALG-240: Perverse Sheaves 的交错展开

**题号**: ALG-240
**难度**: ⭐⭐⭐⭐ (Level 4)
**类型**: 证明型 (PRF)
**来源**: 研究级课程
**主题**: 几何表示论

---

## 题目

**(a)** 定义 perverse sheaf 的交错展开（alternating expansion）。

**(b)** 证明交错展开系数与 Kazhdan-Lusztig 多项式的关系。

**(c)** 讨论 Springer 理论中 perverse sheaf 的具体展开。

---

## 解答

### (a) 交错展开的定义

**设定**：设 $X$ 是代数簇，$\{X_\alpha\}$ 是有限 stratification（$X = \bigsqcup X_\alpha$，每个 $X_\alpha$ 光滑局部闭）。

设 $j_\alpha: X_\alpha \hookrightarrow X$ 是包含。对局部系 $L_\alpha$ on $X_\alpha$，定义中间扩张（intermediate extension）：
$$IC(\overline{X}_\alpha, L_\alpha) = j_{!*}(L_\alpha[\dim X_\alpha])$$

这是 $\overline{X}_\alpha$ 上的 perverse sheaf，满足：
- 在 $X_\alpha$ 上限制为 $L_\alpha[\dim X_\alpha]$
- 在更小的 strata 上满足 stalk 和上 stalk 的 vanishing 条件

**定理（BBD）**：$Perv(X)$（perverse sheaves）是 Artinian 和 Noetherian Abel 范畴。简单对象恰为 $IC_\alpha = IC(\overline{X}_\alpha, L_\alpha)$。

**交错展开（Alternating Expansion）**：

设 $K \in D^b_c(X)$（有界 constructible 复形）。由 perverse t-结构，$K$ 有 perverse filtration，其关联分次给出 perverse cohomology ${}^p\!H^i(K)$。

对每个 perverse sheaf $P$，有 Jordan-Hölder 分解：
$$P \sim \sum_\alpha m_\alpha IC_\alpha$$

**交错展开**：在 Grothendieck 群 $K_0(Perv(X))$ 中，利用局部上同调，任何 constructible 复形可展开为：
$$[K] = \sum_{\alpha, i} (-1)^i [{}^p\!H^i(K_\alpha)]$$

其中 $K_\alpha = j_\alpha^* K$ 是 strata 上的限制。

### (b) 交错展开与 Kazhdan-Lusztig 多项式

**设定**：$G$ 是复约化群，$B \subset G$ 是 Borel。旗簇 $X = G/B$ 有 Bruhat decomposition：
$$X = \bigsqcup_{w \in W} X_w$$
其中 $X_w = BwB/B \cong \mathbb{C}^{l(w)}$ 是 Schubert 胞腔。

**Kazhdan-Lusztig 多项式**：对 $x, w \in W$，$P_{x,w}(q) \in \mathbb{Z}[q]$ 满足：
- $P_{w,w} = 1$
- $\deg P_{x,w} \leq (l(w) - l(x) - 1)/2$ 对 $x < w$
- 递推关系（involution $ar{}$）

**定理（Kazhdan-Lusztig, 1980）**：在 Schubert 簇 $\overline{X}_w$ 上的 $IC$ sheaf 的 stalk Poincaré 多项式由 KL 多项式给出：
$$\sum_i \dim \mathcal{H}^i(IC_{\overline{X}_w})_{x} \cdot q^i = P_{x,w}(q^2)$$

**交错展开系数**：

设 $\Delta_x = j_{x!}\mathbb{C}_{X_x}[l(x)]$（标准模），$\nabla_x = j_{x*}\mathbb{C}_{X_x}[l(x)]$（余标准模）。它们在 $K_0$ 中有展开：
$$[\Delta_x] = \sum_{y \leq x} (-1)^{l(x)-l(y)} P_{y,x}(1) [IC_y]$$

或在 $q$-变形下：
$$[\Delta_x] = \sum_{y \leq x} (-1)^{l(x)-l(y)} P_{y,x}(q) [IC_y] \bigg|_{q \text{-Grothendieck group}}$$

**证明**：利用分解定理和 perverse sheaf 的 Grothendieck 群。$\Delta_x$ 是 perverse sheaf（因 $j_!$ 保持 perversity 对仿射态射，$X_x$ 是仿射空间）。其 Jordan-Hölder 因子是 $IC_y$（$y \leq x$）。

重数由 stalk 计算：在 $y$ 点，$\Delta_x$ 的 stalk 是 $\mathbb{C}$（若 $y = x$）或 0（若 $y \not\leq x$），而 $IC_y$ 的 stalk 由 $P_{z,y}$ 控制。比较 Euler 特征（带 sign）得交错展开公式。

### (c) Springer 理论中的展开

**Springer 消解**：设 $\mathfrak{g}$ 是 Lie 代数，$\mathcal{N} \subset \mathfrak{g}$ 是幂零锥。Springer 消解：
$$\mu: T^*(G/B) \cong \tilde{\mathcal{N}} \to \mathcal{N}$$

$\tilde{\mathcal{N}}$ 是伴随丛 $\{(x, b) : x \in \mathfrak{n}_b\}$。

**Springer 对应**：对 $W$ 的不可约表示 $\phi$，存在 $G$-等变 perverse sheaf $A_\phi$ on $\mathcal{N}$，使得：
$$\mu_* \mathbb{C}_{\tilde{\mathcal{N}}}[\dim \tilde{\mathcal{N}}] \cong \bigoplus_\phi V_\phi \otimes A_\phi$$

其中 $V_\phi$ 是 $W$-表示空间。

**交错展开在 Springer 理论中**：

幂零锥有 Jordan 分类：$\mathcal{N} = \bigsqcup_\lambda \mathcal{O}_\lambda$，$\lambda$ 是划分（对应 Jordan 标准型）。

$IC$ sheaf $IC(\overline{\mathcal{O}}_\lambda)$ 在 $\mathcal{O}_\mu$（$\mu < \lambda$）上的 stalk 由 Springer fiber 的上同调给出。

**具体展开**：对 $GL_n$，Springer fiber $\mathcal{B}_N$（固定幂零元 $N$ 的旗集）的上同调携带 $S_n$ 作用。

**定理（Springer, 1978）**：$H^{2i}(\mathcal{B}_N)$ 作为 $S_n$-表示，与 Kostka 多项式 $K_{\lambda,\mu}(q)$ 相关：
$$\sum_i q^i \text{ch}(H^{2i}(\mathcal{B}_N)) = \sum_\lambda K_{\lambda,\mu}(q) s_\lambda$$

其中 $N$ 对应划分 $\mu$，$s_\lambda$ 是 Schur 函数。

Kostka 多项式是 KL 多项式在 $GL_n$ 幂零锥上的特化。交错展开给出：
$$[\mathbb{C}_{\mathcal{O}_\lambda}] = \sum_\mu (-1)^{\dim \mathcal{O}_\lambda - \dim \mathcal{O}_\mu} K_{\mu,\lambda}(1) [IC_{\overline{\mathcal{O}}_\mu}]$$

**常见错误**：
- 将 perverse sheaf 的交错展开与通常 sheaf 的上同调展开混淆：perverse 展开中的 sign 来自 perverse degree 和平移。
- 忽视 $IC$ sheaf 的 normalization：$IC = j_{!*}(L[\dim X])$ 中的 $[\dim X]$ 平移确保 $IC$ 是 perverse。
- 将 Kazhdan-Lusztig 多项式在 $q = 1$ 的值与交错展开的系数直接等同：需要适当的 sign 调整。

**参考文献**：
- A. Beilinson, J. Bernstein, P. Deligne, *Faisceaux pervers*, Astérisque 100, 1982
- D. Kazhdan, G. Lusztig, "Schubert varieties and Poincaré duality", *Proc. Symp. Pure Math.* 1980
- T. A. Springer, "Trigonometric sums, Green functions of finite groups and representations of Weyl groups", *Invent. Math.* 1976
- N. Chriss, V. Ginzburg, *Representation Theory and Complex Geometry*, Birkhäuser, 1997
