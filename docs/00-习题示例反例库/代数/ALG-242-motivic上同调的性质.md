---
msc_primary: 14

  - 14F42
exercise_id: ALG-242
title: motivic上同调的性质
difficulty: 5
type: PRF
topic: 代数
subtopic: 动机理论
source:
  course: 研究级课程
  chapter: "1.0"
  original: true
processed_at: '2026-04-10'
---

# ALG-242: Motivic 上同调的性质

**题号**: ALG-242
**难度**: ⭐⭐⭐⭐⭐ (Level 5)
**类型**: 证明型 (PRF)
**来源**: 研究级课程
**主题**: 动机理论

---

## 题目

**(a)** 定义 motivic 上同调并证明其基本性质。

**(b)** 证明 motivic 上同调与 Chow 群、Milnor K-理论的关系。

**(c)** 讨论 Beilinson-Lichtenbaum 猜想及其证明。

---

## 解答

### (a) Motivic 上同调的定义与基本性质

**Suslin-Voevodsky 的 motivic 上同调**：对光滑簇 $X$ over $k$，定义：
$$H^{p,q}_{\mathcal{M}}(X, \mathbb{Z}) = \text{Hom}_{DM(k)}(M(X), \mathbb{Z}(q)[p])$$

其中 $DM(k)$ 是 Voevodsky 的混合 motive 导出范畴，$M(X)$ 是 $X$ 的 motive，$\mathbb{Z}(q) = C_*(\mathbb{G}_m^{\wedge q})[-q]$ 是 Tate motive。

**Bloch 的高次 Chow 群（等价定义）**：
$$CH^q(X, p) = \text{高次 Chow 群}$$

Bloch 定义 $z^q(X, \bullet)$ 为恰当相交的代数闭链复形。则：
$$H^{2q-p,q}_{\mathcal{M}}(X, \mathbb{Z}) = CH^q(X, p)$$

**基本性质**：

1. **$\mathbb{A}^1$-同伦不变性**：
   $$H^{p,q}_{\mathcal{M}}(X \times \mathbb{A}^1, \mathbb{Z}) \cong H^{p,q}_{\mathcal{M}}(X, \mathbb{Z})$$

2. **射影丛公式**：对 $\mathbb{P}(E) \to X$（秩 $r$ 向量丛）：
   $$H^{*,*}_{\mathcal{M}}(\mathbb{P}(E)) \cong \bigoplus_{i=0}^{r-1} H^{*-2i,*-i}_{\mathcal{M}}(X)$$

3. **Gysin 序列**：对光滑闭浸入 $Z \hookrightarrow X$（余维 $c$）：
   $$\cdots \to H^{p-2c,q-c}_{\mathcal{M}}(Z) \to H^{p,q}_{\mathcal{M}}(X) \to H^{p,q}_{\mathcal{M}}(X \setminus Z) \to H^{p-2c+1,q-c}_{\mathcal{M}}(Z) \to \cdots$$

4. **对域 $k$ 本身**：
   $$H^{n,n}_{\mathcal{M}}(k, \mathbb{Z}) = K_n^M(k)$$
   $$H^{2n,n}_{\mathcal{M}}(k, \mathbb{Z}) = CH^n(k) = 0 \text{ (对 } n > 0\text{)}$$

### (b) 与 Chow 群和 Milnor K-理论的关系

**与 Chow 群**：

**定理**：对光滑 $X$，$H^{2q,q}_{\mathcal{M}}(X, \mathbb{Z}) \cong CH^q(X)$。

*证明*：由高次 Chow 群的定义，$CH^q(X, 0) = CH^q(X)$（通常 Chow 群）。而 $H^{2q,q}_{\mathcal{M}}(X, \mathbb{Z}) = CH^q(X, 0)$。

更直接地，$CH^q(X)$ 是余维 $q$ 代数闭链模有理等价。Motivic 上同调中的 $\mathbb{Z}(q)[2q]$ 对应于 codimension $q$ 的几何对象。

**与 Milnor K-理论**：

**定理**：对域 $k$：
$$H^{n,n}_{\mathcal{M}}(k, \mathbb{Z}) \cong K_n^M(k)$$

*证明*：Milnor K-群 $K_n^M(k)$ 由符号 $\{a_1, \ldots, a_n\}$ 生成，满足交错性和 $\{a, 1-a\} = 0$。

Suslin 证明高次 Chow 群 $CH^n(k, n) \cong K_n^M(k)$。几何上，$CH^n(k, n)$ 是 $k^n$ 中恰当相交的余维 $n$ 闭链，恰对应 Milnor 符号。

 motivic 上同调中，$H^{n,n}(k, \mathbb{Z}) = \text{Hom}(\text{Spec}(k), \mathbb{Z}(n)[n])$。Tate motive $\mathbb{Z}(n)$ 对应 $(\mathbb{G}_m)^{\wedge n}$，其同伦群与 Milnor K-理论一致。

**与 Quillen K-理论的关系**：

**Bloch-Lichtenbaum 谱序列**：
$$E_2^{p,q} = H^{p-q,-q}_{\mathcal{M}}(X, \mathbb{Z}) \Rightarrow K_{-p-q}(X)$$

这给出 motivic 上同调到代数 K-理论的桥梁。Voevodsky 的 slice filtration 给出 motivic 谱序列的现代解释。

### (c) Beilinson-Lichtenbaum 猜想

**猜想（Beilinson-Lichtenbaum）**：对光滑簇 $X$ over $k$（$\text{char}(k) \nmid m$），存在自然映射：
$$H^{p,q}_{\mathcal{M}}(X, \mathbb{Z}/m) \to H^p_{\text{ét}}(X, \mu_m^{\otimes q})$$

这是同构对 $p \leq q$，且对 $p = q+1$ 是单射。

**定理（Voevodsky, Rost, Suslin 等，1996-2011）**：Beilinson-Lichtenbaum 猜想成立。

**证明的核心步骤**：

**步骤 1：与 Bloch-Kato 等价**。BL 猜想等价于 Bloch-Kato 猜想：
$$K_n^M(k)/m \cong H^n(k, \mu_m^{\otimes n})$$

**步骤 2： motivic Steenrod 代数**。Voevodsky 定义 motivic Steenrod 运算并计算 motivic cohomology of a point。

**步骤 3：Rost motive**。对素数 $p$，Rost 构造与范形式相关的 motive，其 motivic 上同调控制分裂性。

**步骤 4：归纳证明**。利用 motivic Adams 谱序列和 Steenrod 运算的代数性质，证明符号映射的单满性。

**推论**：

1. **Quillen-Lichtenbaum 猜想**：对适当的 $X$ 和 $m$，$K$-理论的 $m$-完备化与 étale $K$-理论一致。

2. **Milnor 关于 Witt 环的猜想**：Witt 环 $W(k)$ 的 filtration 与 Milnor K-理论关联。

3. **Galois 上同调的计算**：对许多域，Galois 上同调可通过 motivic 方法计算。

**常见错误**：
- 将 motivic 上同调与 usual 上同调混淆：motivic 有双次 $(p,q)$，usual 只有单次。
- 忽视 $q > p$ 时 motivic 上同调可能非零：与 usual 上同调不同，$H^{p,q}$ 对 $q > p$ 可以非零（如 $K_n^M$ 对应 $p = q = n$）。
- 将 BL 猜想的条件遗忘：需要 $\text{char}(k) \nmid m$，且在 $p > q$ 时不一定是同构。

**参考文献**：
- S. Bloch, *Lectures on Algebraic Cycles*, Duke Univ. Press, 1980
- V. Voevodsky, "Motivic cohomology with $\mathbb{Z}/\ell$-coefficients", *Ann. Math.* 2011
- A. Suslin, V. Voevodsky, "Bloch-Kato conjecture and motivic cohomology with finite coefficients", 2000
- M. Levine, *Mixed Motives*, AMS, 1998
