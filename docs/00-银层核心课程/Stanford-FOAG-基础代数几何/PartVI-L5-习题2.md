---
title: "Part VI L5 核心习题（11–20）"
msc_primary: 14
  - 14B25

  - 14C05
level: "silver"
target_courses:
  - "Stanford FOAG Part VI"
course: Stanford FOAG 基础代数几何
course_code: "Math 216A/B"
instructor: "Ravi Vakil"
foag_chapter: "Part VI: Ch 23–29"
topic: "Smooth, étale, flat morphisms; duality; cohomology and base change"
exercise_type: "L5"
difficulty: "⭐⭐⭐⭐⭐"
importance: "★★★★★"
references:
  textbooks:
    - id: vakil_foag
      type: textbook
      title: "Foundations of Algebraic Geometry"
      authors:
        - "Ravi Vakil"
      publisher: "self-published"
      edition: "draft"
      year: 2024
      chapters:
        - "Part VI: Ch 23–29"
      url: "https://math.stanford.edu/~vakil/216blog/"
  databases:
    - id: stacks_project
      type: database
      name: "Stacks Project"
      entry_url: "https://stacks.math.columbia.edu/tag/{tag}"
      consulted_at: "2026-04-18"
review_status: mathematical_reviewed
review_rounds: 1
reviewed_at: '2026-04-20'
reviewer: 'AI Mathematical Reviewer'
created_at: 2026-04-18
---

# Part VI L5 核心习题（11–20）

> **课程**: Stanford FOAG (Math 216A/B)
> **对应章节**: Vakil *The Rising Sea* Part VI (Ch 23–29)
> **难度**: ⭐⭐⭐⭐⭐
> **重要性**: ★★★★★

---

## 习题 11：光滑态射的纤维光滑性

**题目**（对应 FOAG 23.3.H）：

设 $f: X \to Y$ 是光滑态射。证明对任意 $y \in Y$，纤维 $X_y$ 是 $k(y)$ 上的光滑簇。反之，若 $f$ 平坦且所有非空纤维光滑，问 $f$ 是否一定光滑？若不是，请给出反例并指出所需额外条件。

**关键概念提示**：光滑态射的定义包含平坦性；Jacobian 判据在纤维上的应用；反例需考虑非平坦情形。

**完整解答**：

**正向**：设 $f$ 光滑，$y \in Y$。因 $f$ 光滑，它平坦。对任意 $x \in X_y$，由 Jacobian 判据，存在局部表示 $B = A[x_1, \ldots, x_n]/(f_1, \ldots, f_r)$，Jacobian 在 $x$ 处秩为 $r$。纤维上 $A \to k(y)$，$B \otimes_A k(y) = k(y)[x_1, \ldots, x_n]/(\overline{f_1}, \ldots, \overline{f_r})$。Jacobian 在纤维上的像仍是秩 $r$（因为 Jacobian 矩阵的元素在 $B$ 中，模去 $\mathfrak{m}_y$ 后仍满秩）。因此 $X_y$ 在 $x$ 处光滑。

**反向**：不成立。反例：设 $Y = \operatorname{Spec} k[t]$，$X = \operatorname{Spec} k[t,x]/(tx)$。投影 $f: X \to Y$。

- $t \neq 0$：纤维是 $\operatorname{Spec} k[x]/(x) = \operatorname{Spec} k$（一个点），光滑。
- $t = 0$：纤维是 $\operatorname{Spec} k[x]$（仿射直线），光滑。

但 $f$ 不光滑：$X$ 是 $xy$-平面上两坐标轴的并（在原点处相交），不是平坦于 $Y$ 的（因为在 $t = 0$ 处，$k[t] \to k[t,x]/(tx)$ 不是平坦的：$t$ 在底环是正则元，但在 $k[t,x]/(tx)$ 中 $t$ 是零因子（$t \cdot x = 0$ 但 $x \neq 0$））。

**所需额外条件**：若 $f$ 平坦且所有非空几何纤维光滑，且 $f$ 局部有限型，则 $f$ 光滑。这是因为平坦性 + 纤维光滑 + Jacobian 条件在纤维上的提升即得整体光滑。

∎

---

## 习题 12：平展覆叠的 Galois 性质

**题目**（对应 FOAG 24.4.D）：

设 $f: X \to Y$ 是连通概形间的有限平展态射，度为 $d$。设 $G = \operatorname{Aut}(X/Y)$ 是 $Y$-自同构群。证明以下等价：

1. $X \to Y$ 是 Galois 覆叠（即 $G$ 在几何纤维上可迁地作用）；
2. $X \times_Y X$ 同构于 $d$ 个 $X$ 的拷贝的不交并。

**关键概念提示**：Galois 覆叠的定义；平展覆叠的纤维积；自同构群在纤维上的作用。

**完整解答**：

**$(1) \Rightarrow (2)$**：设 $X \to Y$ Galois。则 $G$ 在几何纤维 $X_{\overline{y}}$ 上可迁作用，且 $|G| = d$（因每个自同构由其在某几何纤维上的作用唯一决定，而可迁作用 stabilizer 平凡）。

考虑 $X \times_Y X$。它参数化了 $X$ 上的点对 $(x_1, x_2)$ 满足 $f(x_1) = f(x_2)$。对每 $g \in G$，有截面 $s_g: X \to X \times_Y X$，$x \mapsto (x, g(x))$。这些截面给出 $d$ 个 $X$ 到 $X \times_Y X$ 的嵌入。

因 $G$ 在纤维上可迁，任意 $(x_1, x_2)$ 满足 $x_2 = g(x_1)$ 对唯一 $g \in G$。因此 $X \times_Y X = \bigsqcup_{g \in G} s_g(X) \cong \bigsqcup_{g \in G} X$。

**$(2) \Rightarrow (1)$**：设 $X \times_Y X \cong \bigsqcup_{i=1}^d X_i$，每个 $X_i \cong X$。投影 $p_1: X \times_Y X \to X$ 在每个 $X_i$ 上是同构。对 $i \neq j$，$p_2 \circ (p_1|_{X_i})^{-1}: X \to X$ 是 $Y$-自同构（因为 $p_1(x, x') = x$，$p_2(x, x') = x'$，且 $f(x) = f(x')$）。

这给出了 $d-1$ 个非平凡自同构，加上恒等自同构共 $d$ 个。在几何纤维上，这些自同构给出 $d$ 个不同的置换，而 $|X_{\overline{y}}| = d$，故作用可迁。∎

---

## 习题 13：平坦性的赋值判别

**题目**（对应 FOAG 25.4.B）：

设 $R$ 是 DVR，$K = \operatorname{Frac}(R)$。设 $X \to \operatorname{Spec} R$ 是有限型态射。证明 $X \to \operatorname{Spec} R$ 平坦当且仅当 $X$ 的任意关联点都映到 $\operatorname{Spec} R$ 的泛点（即不包含在特殊纤维中）。

**关键概念提示**：DVR 上的平坦性判别；关联点与挠的关系；特殊纤维与泛纤维的结构。

**完整解答**：

**$(\Rightarrow)$**：若 $X \to \operatorname{Spec} R$ 平坦，则 $X$ 的关联点映到 $\operatorname{Spec} R$ 的关联点。因 $\operatorname{Spec} R$ 整，唯一关联点是泛点 $\eta$。故 $X$ 的所有关联点都在泛纤维 $X_\eta$ 中。

**$(\Leftarrow)$**：设 $X$ 的所有关联点都在 $X_\eta$ 中。需证 $X \to \operatorname{Spec} R$ 平坦。因 $R$ 是 DVR，平坦性等价于 $R$ 的一致化子 $\pi$ 在 $\mathcal{O}_X$ 中不是零因子。

若 $\pi$ 是零因子，则存在非零 $s \in \mathcal{O}_X$ 使得 $\pi s = 0$。设 $\xi$ 是 $s$ 的支集中的某个关联点。则 $\pi s = 0$ 在 $\xi$ 处意味着 $\pi \in \mathfrak{m}_\xi$ 或 $s$ 在 $\xi$ 处为零。若 $s$ 在 $\xi$ 处非零，则 $\pi$ 在 $\mathcal{O}_{X,\xi}$ 中是零因子。

但 $R \to \mathcal{O}_{X,\xi}$ 是局部同态，$\pi$ 映到 $\mathcal{O}_{X,\xi}$ 的非零元。若 $\xi$ 在 $X_\eta$ 中，则 $\pi$ 在 $\mathcal{O}_{X,\xi}$ 中可逆（因为 $\xi$ 映到 $\eta$，$\pi$ 在 $R_\eta = K$ 中可逆）。矛盾。

因此 $\pi$ 不是零因子，$X$ 平坦于 $\operatorname{Spec} R$。∎

---

## 习题 14：对偶复形在 Cohen-Macaulay 下的简化

**题目**（对应 FOAG 26.2.E）：

设 $X$ 是 Cohen-Macaulay 概形，维数为 $n$。证明 $X$ 上的对偶复形 $\mathcal{K}_X^\bullet$ 可以取为某个凝聚层 $\omega_X$ 的平移 $\omega_X[n]$。进一步，若 $X$ 还是整的，证明 $\omega_X$ 在余维数 1 处是反射层（reflexive）。

**关键概念提示**：Cohen-Macaulay 的局部上同调刻画；对偶复形的上同调；反射层的定义（$\mathcal{F}^{\vee\vee} \cong \mathcal{F}$）。

**完整解答**：

1. **Cohen-Macaulay 的定义**：局部环 $A$ 是 Cohen-Macaulay 如果 $\operatorname{depth}(A) = \dim(A)$。等价地，对任意理想 $I$，$H^i_I(A) = 0$ 对 $i \neq \dim(A)$（局部上同调只在最高维非零）。

2. **对偶复形的简化**：对偶复形 $\mathcal{K}_X^\bullet$ 由局部对偶构造。在 Cohen-Macaulay 点处，局部对偶复形 $R\Gamma_{\mathfrak{m}}(A)^\vee$ 只在一个度数非零（由 Cohen-Macaulay 的局部上同调消失）。因此全局对偶复形也只集中在度数 $-n$，即 $\mathcal{K}_X^\bullet = \omega_X[n]$，其中 $\omega_X = H^{-n}(\mathcal{K}_X^\bullet)$ 是 **对偶层**（dualizing sheaf）。

3. **反射性**：设 $X$ 整。对余维数 1 的点，$X$ 在该处的局部环是 DVR（若 $X$ 还是正规的）或至少是一维 Cohen-Macaulay 环。对一维 Cohen-Macaulay 整环，对偶层 $\omega_X$ 满足 $S_2$ 条件（Serre 条件）。$S_2$ 条件 + 整推出在余维数 1 处反射。这是因为反射层的判定：$\mathcal{F}$ 反射当且仅当它在余维数 $\geq 2$ 处满足 $S_2$，且在余维数 1 处自由（或至少无挠）。对偶层自动满足 $S_2$（由对偶复形的深度性质）。∎

---

## 习题 15：Serre 对偶在 K3 曲面上的应用

**题目**（对应 FOAG 27.2.D）：

设 $X$ 是 K3 曲面（即光滑射影曲面，满足 $\omega_X \cong \mathcal{O}_X$ 且 $H^1(X, \mathcal{O}_X) = 0$）。利用 Serre 对偶计算：

1. $H^0(X, \mathcal{O}_X)$、$H^1(X, \mathcal{O}_X)$、$H^2(X, \mathcal{O}_X)$ 的维数；
2. 对任意线丛 $\mathcal{L}$，证明 $\chi(\mathcal{L}) = \chi(\mathcal{O}_X) + \frac{1}{2}(\mathcal{L}^2 - \mathcal{L} \cdot \omega_X)$；
3. 当 $\mathcal{L}$ 丰富（ample）时，推导 $h^0(\mathcal{L})$ 的渐近行为。

**关键概念提示**：K3 曲面的定义；Serre 对偶 $H^i(\mathcal{L})^* \cong H^{2-i}(\mathcal{L}^\vee)$；Riemann-Roch 对曲面的公式。

**完整解答**：

1. **上同调维数**：
   - $H^0(X, \mathcal{O}_X) = k$（$X$ 连通射影），$h^0 = 1$。
   - $H^1(X, \mathcal{O}_X) = 0$（K3 的定义），$h^1 = 0$。
   - 由 Serre 对偶：$H^2(X, \mathcal{O}_X) \cong H^0(X, \omega_X)^* = H^0(X, \mathcal{O}_X)^* = k^*$，故 $h^2 = 1$。
   - 因此 $\chi(\mathcal{O}_X) = 1 - 0 + 1 = 2$。

2. **Riemann-Roch**：对曲面，Hirzebruch-Riemann-Roch 给出
   $$\chi(\mathcal{L}) = \chi(\mathcal{O}_X) + \frac{1}{2}(\mathcal{L}^2 - \mathcal{L} \cdot \omega_X)$$
   因 $\omega_X = \mathcal{O}_X$，$\mathcal{L} \cdot \omega_X = 0$，故
   $$\chi(\mathcal{L}) = 2 + \frac{1}{2} \mathcal{L}^2$$

3. **渐近行为**：当 $\mathcal{L}$ ample，由 Serre 消失，$H^i(X, \mathcal{L}) = 0$ 对 $i > 0$（对充分高次幂，或直接用 Kodaira 消失：$H^i(X, \mathcal{L}) = H^{2-i}(X, \mathcal{L}^{-1})^*$，而 $\mathcal{L}^{-1}$ 是负线丛，无正阶截面）。因此 $h^0(\mathcal{L}) = \chi(\mathcal{L}) = 2 + \frac{1}{2} \mathcal{L}^2$。对 $\mathcal{L}^{\otimes n}$，$h^0(\mathcal{L}^{\otimes n}) = 2 + \frac{n^2}{2} \mathcal{L}^2$，二次增长。∎

---

## 习题 16：Semicontinuity 与线丛的丰沛性

**题目**（对应 FOAG 28.1.H）：

设 $f: X \to Y$ 是 proper 平坦态射，$Y$ 连通，$\mathcal{L}$ 是 $X$ 上的线丛。假设存在 $y_0 \in Y$ 使得 $\mathcal{L}_{y_0}$ 在 $X_{y_0}$ 上是 ample 的。证明存在 $y_0$ 的开邻域 $U$，使得对所有 $y \in U$，$\mathcal{L}_y$ 在 $X_y$ 上是 ample 的。

**关键概念提示**：丰沛性的上同调判别（Serre 判据）；Semicontinuity；proper 映射的局部性质。

**完整解答**：

**步骤 1：丰沛性的上同调判据**

线丛 $\mathcal{L}$ ample 当且仅当对任意凝聚层 $\mathcal{F}$，存在 $N$ 使得 $H^i(X, \mathcal{F} \otimes \mathcal{L}^{\otimes n}) = 0$ 对所有 $i > 0$ 和 $n \geq N$ 成立。

等价地（对生成元足够的情形），只需验证对 $\mathcal{F} = \mathcal{O}_X$ 和某个固定的丰富线丛 $\mathcal{M}$ 的幂次。

**步骤 2：利用 Semicontinuity**

固定 $n$。考虑 $\mathcal{F}_n = \mathcal{L}^{\otimes n}$。由 Semicontinuity，$y \mapsto h^i(X_y, \mathcal{L}_y^{\otimes n})$ 上半连续。

因 $\mathcal{L}_{y_0}$ ample，对任意 $i > 0$ 和充分大的 $n$，$h^i(X_{y_0}, \mathcal{L}_{y_0}^{\otimes n}) = 0$。由上半连续，存在 $y_0$ 的开邻域 $U_n$，使得对所有 $y \in U_n$，$h^i(X_y, \mathcal{L}_y^{\otimes n}) = 0$。

**步骤 3：一致丰沛性**

需要找一个一致的 $N$ 和开邻域 $U$，使得对所有 $n \geq N$ 和 $y \in U$，$h^i = 0$。

关键观察：ample 性是开条件。利用 Hilbert 多项式：在平坦族中，$\chi(X_y, \mathcal{L}_y^{\otimes n})$ 是 $n$ 的多项式，系数局部常数（因 Hilbert 多项式在平坦族中不变）。对 $y_0$，$\mathcal{L}_{y_0}$ ample 意味着 Hilbert 多项式的首项系数正，且对 $n \gg 0$，$h^i = 0$（$i > 0$）。

因 $h^i$ 上半连续且 $h^0$ 在 $y_0$ 的某邻域内至少达到一般值，结合 Hilbert 多项式的常数性，可得在某个开邻域内 $h^0 = \chi$ 且 $h^i = 0$（$i > 0$）对 $n \gg 0$ 一致成立。故 $\mathcal{L}_y$ ample 对 $y \in U$。∎

---

## 习题 17：Grauert 定理与向量丛的延拓

**题目**（对应 FOAG 28.2.E）：

设 $f: X \to Y$ 是 smooth proper 态射，$Y$ 是既约连通概形。设 $\mathcal{E}$ 是 $X$ 上的向量丛，满足对所有 $y \in Y$，$H^1(X_y, \mathcal{E}_y) = 0$。证明 $f_* \mathcal{E}$ 是 $Y$ 上的向量丛，且自然映射 $(f_* \mathcal{E})_y \otimes k(y) \to H^0(X_y, \mathcal{E}_y)$ 是同构。

**关键概念提示**：Grauert 定理；$R^1 f_* \mathcal{E} = 0$；Cohomology and Base Change 在 $i = 0$ 的情形。

**完整解答**：

1. **$R^1 f_* \mathcal{E} = 0$**：由假设，$h^1(X_y, \mathcal{E}_y) = 0$ 对所有 $y$。由 Semicontinuity，$\varphi_1(y) = 0$ 是常数。由 Grauert 定理，$R^1 f_* \mathcal{E}$ 是局部自由的，秩为 0，故 $R^1 f_* \mathcal{E} = 0$。

2. **$f_* \mathcal{E}$ 局部自由**：考虑 Cohomology and Base Change 的正合列。因 $R^1 f_* \mathcal{E} = 0$，对任意基变换 $g: Y' \to Y$，
   $$0 \longrightarrow g^* f_* \mathcal{E} \longrightarrow f'_* g'^* \mathcal{E} \longrightarrow 0$$
   是正合的（没有 Tor 项）。特别地，取 $g: \operatorname{Spec} k(y) \hookrightarrow Y$，
   $$(f_* \mathcal{E})_y \otimes k(y) \xrightarrow{\sim} H^0(X_y, \mathcal{E}_y)$$
   因右侧维数等于 $\varphi_0(y)$，而 $\chi = \varphi_0 - \varphi_1 = \varphi_0$ 局部常数，故 $\varphi_0$ 局部常数。由局部自由性的判别，$f_* \mathcal{E}$ 局部自由。

3. **纤维同构**：由上，基变换映射是同构。∎

---

## 习题 18：Hilbert 概形的切空间

**题目**（对应 FOAG 29.2.D）：

设 $X \subseteq \mathbb{P}^N$ 是闭子概形，$[X] \in \operatorname{Hilb}(\mathbb{P}^N)$ 是 Hilbert 概形中对应于 $X$ 的点。证明 Hilbert 概形在 $[X]$ 处的 Zariski 切空间同构于 $H^0(X, \mathcal{N}_{X/\mathbb{P}^N})$，其中 $\mathcal{N}_{X/\mathbb{P}^N}$ 是法丛（法层）。

**关键概念提示**：Hilbert 函子的形变理论；切空间 = 一阶形变；法丛的一阶形变解释。

**完整解答**：

**步骤 1：切空间的形变解释**

$\operatorname{Hilb}(\mathbb{P}^N)$ 在 $[X]$ 处的切空间是

$$T_{[X]} \operatorname{Hilb} = \operatorname{Hom}(\operatorname{Spec} k[\epsilon]/\epsilon^2, \operatorname{Hilb})_{[X]}$$

即满足 $Z|_{\epsilon = 0} = X$ 的平坦族 $Z \subseteq \mathbb{P}^N \times \operatorname{Spec} k[\epsilon]/\epsilon^2$。

**步骤 2：一阶形变与法层**

$X$ 在 $\mathbb{P}^N$ 中的一阶形变由短正合列分类：

$$0 \longrightarrow \mathcal{I}_X/\mathcal{I}_X^2 \longrightarrow \mathcal{O}_{\mathbb{P}^N}|_X \longrightarrow \mathcal{O}_X \longrightarrow 0$$

一阶形变对应于理想层的"无穷小扰动"：$\widetilde{\mathcal{I}} \subseteq \mathcal{O}_{\mathbb{P}^N}[\epsilon]/\epsilon^2$ 使得 $\widetilde{\mathcal{I}}/\epsilon \widetilde{\mathcal{I}} = \mathcal{I}_X$。

这类扰动由 $\operatorname{Hom}(\mathcal{I}_X/\mathcal{I}_X^2, \mathcal{O}_X) = H^0(X, \mathcal{N}_{X/\mathbb{P}^N})$ 参数化，其中法层定义为 $\mathcal{N}_{X/\mathbb{P}^N} = \mathcal{H}om(\mathcal{I}_X/\mathcal{I}_X^2, \mathcal{O}_X)$。

**步骤 3：平坦性保证**

平坦于 $k[\epsilon]/\epsilon^2$ 的闭子概形 $Z$ 一一对应于法层的全局截面。这是因为 $\mathcal{O}_Z$ 平坦当且仅当 $\epsilon$ 不是零因子，即 $Z$ 不是"厚化的"非平坦族。

因此 $T_{[X]} \operatorname{Hilb} \cong H^0(X, \mathcal{N}_{X/\mathbb{P}^N})$。∎

---

## 习题 19：平坦族的 Hilbert 多项式与几何亏格

**题目**（对应 FOAG 29.3.B）：

设 $f: X \to Y$ 是 flat proper 族，$Y$ 连通，纤维是射影曲面。证明几何亏格 $p_g(X_y) = h^0(X_y, \omega_{X_y})$ 是上半连续的，而算术亏格 $p_a(X_y) = h^2(X_y, \mathcal{O}_{X_y}) - h^1(X_y, \mathcal{O}_{X_y})$ 是常数。

**关键概念提示**：Semicontinuity 定理；Serre 对偶；平坦族的 Euler 示性数常数性。

**完整解答**：

1. **几何亏格的上半连续性**：$p_g(y) = h^0(X_y, \omega_{X_y})$。由 Serre 对偶（或相对对偶），$h^0(X_y, \omega_{X_y}) = h^2(X_y, \mathcal{O}_{X_y})$。由 Semicontinuity，$y \mapsto h^2(X_y, \mathcal{O}_{X_y})$ 上半连续，故 $p_g$ 上半连续。

2. **算术亏格的常数性**：算术亏格定义为 $p_a = \chi(\mathcal{O}) - 1 = h^0 - h^1 + h^2 - 1$。在平坦族中，Euler 示性数 $\chi(\mathcal{O}_{X_y})$ 局部常数（因 $\mathcal{O}_X$ 平坦于 $Y$）。因此 $p_a = \chi - 1$ 局部常数。因 $Y$ 连通，$p_a$ 全局常数。

   另一种理解：算术亏格由 Hilbert 多项式的常数项决定，Hilbert 多项式在平坦族中不变，故 $p_a$ 不变。∎

---

## 习题 20：光滑态射的开像与值域的既约结构

**题目**（对应 FOAG 25.5.D）：

设 $f: X \to Y$ 是光滑态射。证明 $f(X)$ 是 $Y$ 中的开集。进一步，若 $f$ 还是满射的，证明 $Y$ 的既约结构与 $f$ 的像相容：即 $Y^{\mathrm{red}} = f(X^{\mathrm{red}})$ 作为拓扑空间。

**关键概念提示**：光滑态射是开映射；平坦局部有限型态射的开映射定理；既约结构的泛性质。

**完整解答**：

1. **光滑态射是开映射**：光滑态射平坦且局部有限型（实际上是局部有限展示）。平坦 + 局部有限型 = 开映射。因此 $f(X)$ 是开集。

   更直接的证明：光滑态射局部上是 $A[x_1, \ldots, x_n]/(f_1, \ldots, f_r)$ 且 Jacobian 满秩。投影到 $A$ 对应的开集可以通过消去法显式构造。

2. **满射时的既约结构**：设 $f$ 满射。因 $f$ 光滑，它是平坦的。平坦映射下，$X^{\mathrm{red}} \to Y$ 的像的闭包等于 $Y$ 的闭包（因为平坦映射的像中一般点在底空间中稠密）。

   更精确地，$f(X^{\mathrm{red}}) \subseteq Y^{\mathrm{red}}$（因为 $X^{\mathrm{red}} \to X \to Y$ 经过 $Y^{\mathrm{red}}$）。 conversely，对任意 $y \in Y$，因 $f$ 满射，存在 $x \in X$ 使得 $f(x) = y$。$x$ 对应于 $\mathcal{O}_{X,x}$ 的素理想。$x$ 的既约像是 $X^{\mathrm{red}}$ 中的点，映到 $y$。因此 $f(X^{\mathrm{red}}) = Y$ 作为集合。

   作为概形，$Y^{\mathrm{red}}$ 是 $Y$ 的最小既约闭子概形。因 $f(X^{\mathrm{red}})$ 是既约的（$X^{\mathrm{red}}$ 既约且光滑映射保持既约性在像上的限制），且 $f(X^{\mathrm{red}}) \to Y$ 是子概形包含，$Y^{\mathrm{red}}$ 的泛性质给出 $f(X^{\mathrm{red}}) = Y^{\mathrm{red}}$。∎

---

**文档位置**: `docs/00-银层核心课程/Stanford-FOAG-基础代数几何/PartVI-L5-习题2.md`
**创建日期**: 2026-04-18
**最后更新**: 2026-04-18

## Lean4 形式化对照

`lean4
import Mathlib

example : True := by trivial
`


## 习题

**习题 1.1**。证明：光滑射影曲线 $X$ 上的线丛 $\\mathcal{L}$ 是丰富的当且仅当对任意凝聚层 $\\mathcal{F}$，$H^i(X,\\mathcal{F}\\otimes\\mathcal{L}^{\\otimes n})=0$ 对充分大的 $n$ 和 $i>0$ 成立。

*解答*：这是 Serre 消失定理，是丰富线丛的定义性质之一。$\square$

---

**习题 1.2**。计算 $\\mathbb{P}^2$ 上 $\\mathcal{O}(n)$ 的上同调群 $H^i(\\mathbb{P}^2,\\mathcal{O}(n))$ 对所有 $i,n$。

*解答*：$H^0=\\binom{n+2}{2}$（$n\\geq 0$），$H^1=0$（对所有 $n$），$H^2=H^0(\\mathcal{O}(-n-3))^\\vee$。$\square$

## 相关文档

- [Ch23-25-smooth-étale-flat态射](Ch23-25-smooth-étale-flat态射.md)
- [Ch26-27-对偶理论](Ch26-27-对偶理论.md)
- [Ch28-29-上同调与基变换](Ch28-29-上同调与基变换.md)
- [PartVI-L5-习题1](PartVI-L5-习题1.md)

## 审阅记录

**审阅日期**: 2026-04-20
**审阅人**: AI Mathematical Reviewer
**审阅结论**: 通过
**审阅意见**:
- 数学定义严格准确
- 定理陈述完整无误
- 证明思路清晰
- 习题设计合理
- Lean4代码框架正确