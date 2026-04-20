---
msc_primary: 14

  - 14C30
exercise_id: ALG-241
title: Mumford-Tate群与Hodge结构
difficulty: 4
type: PRF
topic: 代数
subtopic: Hodge理论
source:
  course: 研究级课程
  chapter: "1.0"
  original: true
processed_at: '2026-04-10'
---

# ALG-241: Mumford-Tate 群与 Hodge 结构

**题号**: ALG-241
**难度**: ⭐⭐⭐⭐ (Level 4)
**类型**: 证明型 (PRF)
**来源**: 研究级课程
**主题**: Hodge理论

---

## 题目

**(a)** 定义纯 Hodge 结构和 Mumford-Tate 群。

**(b)** 证明 Mumford-Tate 群是 Hodge 结构的完整对称群。

**(c)** 讨论 Hodge 结构的特殊化与变形。

---

## 解答

### (a) 纯 Hodge 结构与 Mumford-Tate 群

**定义（纯 Hodge 结构）**：纯 Hodge 结构（权 $n$）是有限维 $\mathbb{Q}$-向量空间 $V$ 的分解：
$$V_\mathbb{C} = V \otimes_\mathbb{Q} \mathbb{C} = \bigoplus_{p+q=n} V^{p,q}$$
满足 $\overline{V^{p,q}} = V^{q,p}$（Hodge 对称性）。

**等价描述**：Hodge filtration $F^\bullet$：
$$F^p = \bigoplus_{r \geq p} V^{r, n-r}$$
满足 $V_\mathbb{C} = F^p \oplus \overline{F^{n-p+1}}$。

**例子**：紧 Kähler 流形 $X$ 的上同调 $H^n(X, \mathbb{Q})$ 有权 $n$ 的纯 Hodge 结构。

**Tate Hodge 结构**：$\mathbb{Q}(1) = 2\pi i \mathbb{Q} \subset \mathbb{C}$，权 $-2$，$V^{-1,-1} = V_\mathbb{C}$。

**Deligne Torus**：定义 $\mathbb{S} = \text{Res}_{\mathbb{C}/\mathbb{R}}(\mathbb{G}_m)$，即 Weil 限制。作为实代数群：
$$\mathbb{S}(\mathbb{R}) = \mathbb{C}^\times$$

$
\mathbb{S}(\mathbb{C}) = \mathbb{C}^\times \times \mathbb{C}^\times$。

**Hodge 结构作为表示**：权 $n$ 的 Hodge 结构等价于同态：
$$h: \mathbb{S} \to GL(V)_\mathbb{R}$$
满足 $h(t) = t^n \cdot \text{id}$ 对 $t \in \mathbb{R}^\times \subset \mathbb{C}^\times$。

具体地，$z \in \mathbb{C}^\times = \mathbb{S}(\mathbb{R})$ 作用在 $V^{p,q}$ 上为 $z^p \bar{z}^q$。

**Mumford-Tate 群的定义**：
$$MT(V) = \overline{\langle h(\mathbb{S}(\mathbb{R})) \rangle}^{Zar} \subset GL(V)$$

即 $h(\mathbb{S})$ 在 $GL(V)$ 中的 Zariski 闭包。这是 $\mathbb{Q}$-定义的代数子群。

### (b) Mumford-Tate 群的完全对称性

**定理**：$MT(V)$ 是保持 $V$ 上所有由 Hodge 张量生成的张量中的 Hodge 类的最大代数子群。

**Hodge 类**：在 $V^{\otimes r} \otimes (V^\vee)^{\otimes s}$ 中，Hodge 类是 $(0,0)$-型（即权 0，$p = q = 0$）的有理类。

**定理（Mumford-Tate 的主定理）**：$G \subset GL(V)$ 是 $\mathbb{Q}$-代数子群。则 $G \supset MT(V)$ 当且仅当 $G$ 固定所有 Hodge 类。

等价地，$MT(V)$ 是固定 $V$ 及其对偶的所有张量积中的 Hodge 类的最小代数群。

**证明**：

**$(\Rightarrow)$**：$MT(V)$ 由定义固定所有 Hodge 张量（因 Hodge 类正是 $h(\mathbb{S})$ 的不变量）。

**$(\Leftarrow)$**：设 $G$ 固定所有 Hodge 类。需证 $G \supset h(\mathbb{S})$。由 Chevalley 定理，$G$ 是某 $W = V^{\otimes r} \otimes (V^\vee)^{\otimes s}$ 中某向量 $w$ 的稳定子。$w$ 是 $G$-不变，由假设是 Hodge 类。故 $h(\mathbb{S})$ 固定 $w$，即 $h(\mathbb{S}) \subset G$。取 Zariski 闭包，$MT(V) \subset G$。∎

**推论**：若 $V$ 的 Hodge 结构由 $V$ 单独生成（无额外的 Hodge 类），则 $MT(V) = GL(V)$（或 $Sp(V)$ 或 $O(V)$，取决于 polarized 情形）。

**Hodge locus**：考虑 Hodge 结构的族 $\{V_s\}_{s \in S}$。点 $s$ 的 Mumford-Tate 群 $MT(V_s)$ 在一般点取最小值（generic Mumford-Tate 群）。Hodge locus 是 $MT(V_s) \subsetneq MT_{gen}$ 的点集。

**定理（Cattani-Deligne-Kaplan, 1995）**：Hodge locus 是 $S$ 的可数代数子集的并。

### (c) Hodge 结构的特殊化与变形

**变分 of Hodge 结构（VHS）**：设 $f: X \to S$ 是光滑真态射。$R^n f_* \mathbb{Q}$ 是 $S$ 上的局部系，每纤维 $H^n(X_s, \mathbb{Q})$ 有 Hodge 结构。

**Griffiths 横截性**：Hodge  filtration $F^p$ 在 $S$ 上变化，满足：
$$\nabla(F^p) \subset F^{p-1} \otimes \Omega^1_S$$
其中 $\nabla$ 是 Gauss-Manin 联络。

**Hodge 结构的极限（Schmid, 1973）**：设 degeneration $X \to \Delta$（单参数，在 $0$ 有奇点）。$H^n(X_t)$ 的 Hodge 结构当 $t \to 0$ 时有极限。极限不是纯 Hodge 结构，而是**混合 Hodge 结构**。

**混合 Hodge 结构（MHS）**：$V$ 有递增权滤过 $W_\bullet$ 和递减 Hodge 滤过 $F^\bullet$，使得 $Gr_m^W V$ 有权 $m$ 的纯 Hodge 结构。

**极限混合 Hodge 结构**：Schmid 证明单值算子 $T$ 定义 nilpotent 算子 $N = \log T_u$（unipotent 部分）。则 $(V, W(N)_\bullet, F^\bullet_\infty)$ 构成 MHS，其中 $W(N)$ 是 $N$ 的 Jacobson-Morozov 滤过。

**应用**：

- **Hodge 猜想的几何**：Mumford-Tate 群的计算可帮助判断哪些 Hodge 类是代数的。
- **André-Oort 猜想**：Shimura 变种的特殊子变种由 Mumford-Tate 群刻画。André-Oort 猜想断言，包含大量 CM 点的不可约子变种必为特殊子变种。

**常见错误**：
- 将 Mumford-Tate 群与 Hodge 群混淆：Hodge 群 $Hg(V) = MT(V) \cap SL(V)$（或 $Sp$），是导子群。
- 忽视 Mumford-Tate 群是 $\mathbb{Q}$-群：$MT(V)$ 的定义在 $\mathbb{Q}$ 上，不是 $\mathbb{R}$ 上的任意闭子群。
- 将 VHS 的 Griffiths 横截性与 flatness 混淆：$F^p$ 不是 flat 的，其导数在 $F^{p-1}$ 中。

**参考文献**：
- D. Mumford, "Families of abelian varieties", *Proc. Symp. Pure Math.* 1969
- P. Deligne, "Travaux de Griffiths", *Sém. Bourbaki* 1970
- W. Schmid, "Variation of Hodge structure: the singularities of the period mapping", *Invent. Math.* 1973
- E. Cattani, P. Deligne, A. Kaplan, "On the locus of Hodge classes", *J. AMS* 1995
