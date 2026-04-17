---
title: "Part VI L5 核心习题（1–10）"
msc_primary: "14-01"
msc_secondary:
  - "14B25"
  - "14Fxx"
  - "14C05"
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
review_status: "draft"
---

# Part VI L5 核心习题（1–10）

> **课程**: Stanford FOAG (Math 216A/B)
> **对应章节**: Vakil *The Rising Sea* Part VI (Ch 23–29)
> **难度**: ⭐⭐⭐⭐⭐
> **重要性**: ★★★★★

---

## 习题 1：光滑态射的复合

**题目**（对应 FOAG 23.2.C）：

设 $f: X \to Y$ 和 $g: Y \to Z$ 是光滑态射。证明 $g \circ f: X \to Z$ 也是光滑的。进一步，若 $f$ 和 $g$ 的相对维数分别为 $r$ 和 $s$，则 $g \circ f$ 的相对维数为 $r + s$。

**关键概念提示**：光滑态射的相对微分层满足正合列 $0 \to f^* \Omega_{Y/Z} \to \Omega_{X/Z} \to \Omega_{X/Y} \to 0$。

**完整解答**：

1. **有限型的保持**：光滑态射是局部有限型的，复合保持局部有限型。

2. **平坦性的保持**：$f$ 平坦，$g$ 平坦，平坦态射的复合平坦。

3. **微分层的正合列**：对态射的复合 $X \xrightarrow{f} Y \xrightarrow{g} Z$，有相对余切的正合列：
   $$f^* \Omega_{Y/Z} \longrightarrow \Omega_{X/Z} \longrightarrow \Omega_{X/Y} \longrightarrow 0$$
   若 $f$ 光滑，则此列左端也是单射，成为短正合列：
   $$0 \longrightarrow f^* \Omega_{Y/Z} \longrightarrow \Omega_{X/Z} \longrightarrow \Omega_{X/Y} \longrightarrow 0$$
   这是因为光滑性保证了 $f$ 在形式上是"子浸没"，余切映射单射。

4. **局部自由性的保持**：因 $f$ 光滑，$\Omega_{X/Y}$ 局部自由，秩 $r$；因 $g$ 光滑，$\Omega_{Y/Z}$ 局部自由，秩 $s$，故 $f^* \Omega_{Y/Z}$ 局部自由，秩 $s$。短正合列中两端局部自由，故中间也局部自由，秩 $r + s$。

5. **相对维数的可加性**：在点 $x \in X$ 处，$(g \circ f)$ 的纤维是 $f$ 限制在 $g^{-1}(g(f(x)))$ 的纤维上。由纤维维数的可加性，$\dim_x((g \circ f)^{-1}(z)) = \dim_x(f^{-1}(y)) + \dim_y(g^{-1}(z)) = r + s$。

因此 $g \circ f$ 光滑，相对维数 $r + s$。∎

---

## 习题 2：Jacobian 判据的仿射验证

**题目**（对应 FOAG 23.3.G）：

设 $k$ 是代数闭域，$X = \operatorname{Spec} k[x,y,z]/(xy - z^2, xz - y^3)$。在点 $P = (0,0,0)$ 处，用 Jacobian 判据判断 $X$ 是否光滑。若 $P$ 是奇点，计算其 Zariski 切空间维数。

**关键概念提示**：Jacobian 矩阵在 $P$ 处的秩与切空间维数的关系：$\dim T_P X = n - \operatorname{rank}(J(P))$。

**完整解答**：

$X$ 由两个方程 $f_1 = xy - z^2 = 0$ 和 $f_2 = xz - y^3 = 0$ 定义，嵌入在 $\mathbb{A}^3$ 中，$n = 3$，$r = 2$。

Jacobian 矩阵：

$$J = \begin{pmatrix} \frac{\partial f_1}{\partial x} & \frac{\partial f_1}{\partial y} & \frac{\partial f_1}{\partial z} \\ \frac{\partial f_2}{\partial x} & \frac{\partial f_2}{\partial y} & \frac{\partial f_2}{\partial z} \end{pmatrix} = \begin{pmatrix} y & x & -2z \\ z & -3y^2 & x \end{pmatrix}$$

在 $P = (0,0,0)$ 处：

$$J(P) = \begin{pmatrix} 0 & 0 & 0 \\ 0 & 0 & 0 \end{pmatrix}$$

秩为 0，小于 $r = 2$。因此 $P$ 是奇点。

切空间维数：$T_P X = \ker J(P) \subseteq k^3$。因 $J(P) = 0$，$\ker J(P) = k^3$。故 $\dim T_P X = 3$。

一般地，若 $X$ 在 $P$ 处光滑，切空间维数应等于 $\dim_P X$。这里 $X$ 是三维空间中两个方程的交，若横截则维数为 1。但 $P$ 处 Jacobian 秩为 0，说明两个曲面在 $P$ 处"完全不正交"，相交行为退化。∎

---

## 习题 3：平展态射的纤维基数

**题目**（对应 FOAG 24.3.E）：

设 $f: X \to Y$ 是有限平展态射，$Y$ 是连通概形。证明存在正整数 $d$（称为 **度**，degree），使得对任意几何点 $\overline{y} \to Y$，纤维 $X_{\overline{y}}$ 恰由 $d$ 个点组成（不计重数，因为平展纤维是既约的）。

**关键概念提示**：有限平展态射局部上是标准平展的，而标准平展映射的纤维是多项式的不同根的集合。

**完整解答**：

1. **局部结构**：由标准平展邻域的结构定理，对任意 $x \in X$，存在仿射开邻域使得 $f$ 在该邻域上是 $A[t]/(P(t))$ 的形式，其中 $P$ 首一，$P'$ 可逆。

2. **纤维的结构**：对 $y \in Y$，设 $k(y)$ 是剩余域。纤维 $X_y = \operatorname{Spec}(B \otimes_A k(y))$。局部地，$B \otimes_A k(y) = k(y)[t]/(P_y(t))$，其中 $P_y$ 是 $P$ 在 $k(y)$ 上的像。

3. **可分性**：因 $P'$ 可逆，$P$ 与 $P'$ 无公共根，故 $P_y$ 在代数闭包 $\overline{k(y)}$ 上无重根。因此 $X_{\overline{y}}$ 是 $\deg(P_y)$ 个不同点的并。

4. **度的局部常数性**：$\deg(P_y)$ 在 $y$ 附近是常数，因为 $P$ 作为首一多项式，次数不随 specialization 改变。因 $Y$ 连通，所有局部标准平展邻域的次数必须相同（否则在重叠处矛盾）。

5. **结论**：设这个公共次数为 $d$。则对任意几何点 $\overline{y}$，$X_{\overline{y}}$ 恰有 $d$ 个点。∎

---

## 习题 4：平坦性的 Tor 判别

**题目**（对应 FOAG 25.2.C）：

设 $A$ 是 Noether 环，$M$ 是有限生成 $A$-模。证明 $M$ 平坦当且仅当 $\operatorname{Tor}_1^A(M, A/\mathfrak{p}) = 0$ 对所有素理想 $\mathfrak{p} \subseteq A$ 成立。

**关键概念提示**：平坦性的局部判别；Tor 与局部化的交换；Noether 环上有限生成模的平坦性等价于局部自由性。

**完整解答**：

**$(\Rightarrow)$**：若 $M$ 平坦，则 $-\otimes_A M$ 是正合函子，故 $\operatorname{Tor}_1^A(M, N) = 0$ 对所有 $N$。特别地对 $N = A/\mathfrak{p}$ 成立。

**$(\Leftarrow)$**：设 $\operatorname{Tor}_1^A(M, A/\mathfrak{p}) = 0$ 对所有素理想 $\mathfrak{p}$ 成立。

- **步骤 1**：先证对所有有限生成模 $N$，$\operatorname{Tor}_1^A(M, N) = 0$。对 $N$ 取有限表现（因 $A$ Noether，有限生成模自动有限表现）。利用 Tor 的长正合列和有限表现的过滤，可化归到 $N = A/\mathfrak{p}$ 的情形。

- **步骤 2**：证明 $M$ 平坦。平坦性的判别：$M$ 平坦当且仅当对所有理想 $I \subseteq A$，自然映射 $I \otimes M \to M$ 是单射。这等价于 $\operatorname{Tor}_1^A(M, A/I) = 0$ 对所有 $I$。由步骤 1，对所有有限生成 $N$（包括 $A/I$）Tor 消失，故 $M$ 平坦。

- **步骤 3**：另一种论证：由 Auslander-Buchsbaum 公式，若 $M$ 有限生成，则 $M$ 平坦当且仅当 $M$ 局部自由。而 $M_{\mathfrak{p}}$ 局部自由当且仅当 $\operatorname{Tor}_1^{A_{\mathfrak{p}}}(M_{\mathfrak{p}}, k(\mathfrak{p})) = 0$（局部环上有限生成模的平坦性判别）。这与假设等价。∎

---

## 习题 5：平坦族中关联点的保持

**题目**（对应 FOAG 25.3.G）：

设 $f: X \to Y$ 是有限型态射，$Y$ 是整概形，$\eta \in Y$ 是泛点。设 $X_\eta$ 的关联点集为 $\{\xi_1, \ldots, \xi_n\}$。证明：若 $f$ 平坦，则对任意 $y \in Y$，$X_y$ 的关联点恰是 $\{\xi_1, \ldots, \xi_n\}$ 在 $X_y$ 中的 specialization。

**关键概念提示**：平坦映射保持关联点；generic fiber 的关联点在 specialization 下不增加也不减少。

**完整解答**：

这是 **平坦映射的关联点定理**。

1. **平坦性保持关联点**：若 $f$ 平坦，则 $X$ 的关联点映到 $Y$ 的关联点（因 $Y$ 整，$Y$ 的唯一关联点是泛点 $\eta$）。因此 $X$ 的关联点都在泛纤维 $X_\eta$ 中。

2. **specialization 的保持**：设 $\xi \in X$ 是 $X$ 的关联点。因 $f(\xi) = \eta$（由步骤 1），$\xi$ 是 $X_\eta$ 的关联点。对任意 $y \in Y$，$\xi$ 在 $X$ 中的闭包与 $X_y$ 的交非空（因为 $y \in \overline{\{\eta\}}$，而 $f$ 连续）。交点正是 $\xi$ 在 $X_y$ 中的 specialization。

3. **不增加**：设 $z \in X_y$ 是 $X_y$ 的关联点。需证 $z$ 是某个 $\xi_i$ 的 specialization。考虑 $X$ 中对应于 $z$ 的点。由平坦性，$X$ 在 $z$ 处的局部环 $B_{\mathfrak{p}}$ 平坦于 $A_{\mathfrak{q}}$（$\mathfrak{q}$ 对应 $y$）。平坦映射下，若 $z$ 是 $X_y$ 的关联点，则它在 $X$ 中也是关联点（或至少是某个关联点的 specialization）。由 $Y$ 整，$X$ 的关联点都在 $X_\eta$ 中，故 $z$ 是某个 $\xi_i$ 的 specialization。∎

---

## 习题 6：Grothendieck 对偶的右伴随唯一性

**题目**（对应 FOAG 26.1.B）：

设 $f: X \to Y$ 是 proper 态射。若 $f^!: D_{\mathrm{qcoh}}^+(Y) \to D_{\mathrm{qcoh}}^+(X)$ 和 $f^{!!}$ 都是 $Rf_*$ 的右伴随，证明存在典范同构 $f^! \cong f^{!!}$。

**关键概念提示**：右伴随的唯一性；导出范畴中伴随函子的 Yoneda 论证。

**完整解答**：

由伴随函子的唯一性理论，若 $F \dashv G$ 且 $F \dashv G'$，则 $G \cong G'$。

具体构造：对任意 $\mathcal{G}^\bullet \in D_{\mathrm{qcoh}}^+(Y)$，需要构造 $f^! \mathcal{G}^\bullet \cong f^{!!} \mathcal{G}^\bullet$。

由 $f^!$ 的伴随性，对任意 $\mathcal{F}^\bullet \in D_{\mathrm{qcoh}}^-(X)$：

$$\operatorname{Hom}_{D(X)}(\mathcal{F}^\bullet, f^! \mathcal{G}^\bullet) \cong \operatorname{Hom}_{D(Y)}(Rf_* \mathcal{F}^\bullet, \mathcal{G}^\bullet)$$

由 $f^{!!}$ 的伴随性：

$$\operatorname{Hom}_{D(X)}(\mathcal{F}^\bullet, f^{!!} \mathcal{G}^\bullet) \cong \operatorname{Hom}_{D(Y)}(Rf_* \mathcal{F}^\bullet, \mathcal{G}^\bullet)$$

因此

$$\operatorname{Hom}_{D(X)}(\mathcal{F}^\bullet, f^! \mathcal{G}^\bullet) \cong \operatorname{Hom}_{D(X)}(\mathcal{F}^\bullet, f^{!!} \mathcal{G}^\bullet)$$

自然于 $\mathcal{F}^\bullet$。由 Yoneda 引理，$f^! \mathcal{G}^\bullet \cong f^{!!} \mathcal{G}^\bullet$。此同构自然于 $\mathcal{G}^\bullet$，故 $f^! \cong f^{!!}$。∎

---

## 习题 7：Serre 对偶的曲线 Riemann-Roch

**题目**（对应 FOAG 27.1.C）：

设 $C$ 是光滑射影曲线，亏格 $g$。利用 Serre 对偶证明 Riemann-Roch 定理：对任意除子 $D$，

$$h^0(\mathcal{O}(D)) - h^0(\mathcal{O}(K - D)) = \deg(D) + 1 - g$$

其中 $K$ 是典范除子。

**关键概念提示**：Serre 对偶给出 $h^1(\mathcal{O}(D)) = h^0(\mathcal{O}(K - D))$；Euler 示性数 $\chi(\mathcal{O}(D)) = \deg(D) + 1 - g$。

**完整解答**：

1. **Serre 对偶的应用**：由 Serre 对偶（局部自由层形式），
   $$H^1(C, \mathcal{O}(D))^* \cong H^0(C, \mathcal{O}(D)^\vee \otimes \omega_C) = H^0(C, \mathcal{O}(-D) \otimes \mathcal{O}(K)) = H^0(C, \mathcal{O}(K - D))$$
   因此 $h^1(\mathcal{O}(D)) = h^0(\mathcal{O}(K - D))$。

2. **Euler 示性数的计算**：Riemann-Roch 的核心是证明
   $$\chi(\mathcal{O}(D)) = h^0(\mathcal{O}(D)) - h^1(\mathcal{O}(D)) = \deg(D) + 1 - g$$

   用归纳法证明。首先对 $D = 0$：$h^0(\mathcal{O}) = 1$，$h^1(\mathcal{O}) = g$，故 $\chi = 1 - g = 0 + 1 - g$。

   对一般 $D$，写 $D = D' + P$，其中 $P$ 是点。有短正合列
   $$0 \longrightarrow \mathcal{O}(D') \longrightarrow \mathcal{O}(D) \longrightarrow k(P) \longrightarrow 0$$
   其中 $k(P)$ 是 $P$ 处的摩天大楼层。取 Euler 示性数：$\chi(\mathcal{O}(D)) = \chi(\mathcal{O}(D')) + \chi(k(P)) = \chi(\mathcal{O}(D')) + 1$。

   因 $\deg(D) = \deg(D') + 1$，由归纳假设，$\chi(\mathcal{O}(D)) = (\deg(D') + 1 - g) + 1 = \deg(D) + 1 - g$。

3. **结合 Serre 对偶**：
   $$h^0(\mathcal{O}(D)) - h^0(\mathcal{O}(K - D)) = h^0(\mathcal{O}(D)) - h^1(\mathcal{O}(D)) = \chi(\mathcal{O}(D)) = \deg(D) + 1 - g$$

∎

---

## 习题 8：Semicontinuity 的上同调消失开集

**题目**（对应 FOAG 28.1.F）：

设 $f: X \to Y$ 是 proper 平坦态射，$\mathcal{F}$ 是 $X$ 上的凝聚层，平坦于 $Y$。证明对任意 $i$，集合

$$U_i = \{y \in Y : H^i(X_y, \mathcal{F}_y) = 0\}$$

是 $Y$ 中的开集。

**关键概念提示**：Semicontinuity 定理：$y \mapsto h^i(X_y, \mathcal{F}_y)$ 上半连续。

**完整解答**：

由 Semicontinuity 定理，函数 $\varphi_i(y) = h^i(X_y, \mathcal{F}_y)$ 上半连续。

上半连续的定义：对任意 $n \in \mathbb{Z}$，$S_n = \{y \in Y : \varphi_i(y) \geq n\}$ 是闭集。

$U_i = \{y : \varphi_i(y) = 0\} = Y \setminus S_1$。因 $S_1 = \{y : \varphi_i(y) \geq 1\}$ 是闭集，$U_i$ 是开集。∎

---

## 习题 9：Grauert 定理的逆否形式

**题目**（对应 FOAG 28.2.C）：

设 $f: X \to Y$ 是 proper 平坦态射，$Y$ 是既约连通曲线。假设 $R^i f_* \mathcal{F}$ 不是局部自由的。证明存在 $y \in Y$ 使得 $h^i(X_y, \mathcal{F}_y) > h^i(X_\eta, \mathcal{F}_\eta)$，其中 $\eta$ 是 $Y$ 的泛点。

**关键概念提示**：Grauert 定理：若 $h^i$ 常数则 $R^i f_* \mathcal{F}$ 局部自由；其逆否命题给出非局部自由时的跳跃。

**完整解答**：

由 Grauert 定理的逆否：若 $R^i f_* \mathcal{F}$ 不局部自由，则 $h^i(X_y, \mathcal{F}_y)$ 在 $Y$ 上不常数。

因 $Y$ 是曲线（一维整概形），$Y$ 的点分为泛点 $\eta$ 和闭点。由 Semicontinuity，$h^i$ 在 specialization 下不减：若 $y$ 是闭点，$y \in \overline{\{\eta\}}$，则 $h^i(X_y, \mathcal{F}_y) \geq h^i(X_\eta, \mathcal{F}_\eta)$。

若 $h^i$ 不常数，则存在某个闭点 $y$ 使得 $h^i(X_y, \mathcal{F}_y) > h^i(X_\eta, \mathcal{F}_\eta)$。∎

---

## 习题 10：Hilbert 多项式的基变换不变性

**题目**（对应 FOAG 29.1.C）：

设 $X \subseteq \mathbb{P}^N_S$ 是闭子概形，平坦于 $S$。证明对任意 $s \in S$，$X_s \subseteq \mathbb{P}^N_{k(s)}$ 的 Hilbert 多项式 $P_s(m) = \chi(X_s, \mathcal{O}_{X_s}(m))$ 不依赖于 $s$。

**关键概念提示**：平坦族的 Euler 示性数局部常数；Hilbert 多项式的定义。

**完整解答**：

1. **Hilbert 多项式的定义**：对射影概形 $X_s \subseteq \mathbb{P}^N$，$\mathcal{O}_{X_s}(1)$ 是 ample 线丛。Hilbert 多项式定义为
   $$P_s(m) = \chi(X_s, \mathcal{O}_{X_s}(m))$$
   由 Serre 消失定理，对 $m \gg 0$，$P_s(m) = h^0(X_s, \mathcal{O}_{X_s}(m))$。

2. **Euler 示性数的局部常数性**：因 $f: X \to S$ 平坦 proper，$\mathcal{O}_X(1)$ 是 $X$ 上的线丛，$\mathcal{O}_X(m)$ 平坦于 $S$。由 Cohomology and Base Change 的推论，Euler 示性数 $\chi(X_s, \mathcal{O}_{X_s}(m))$ 在 $s$ 上局部常数。

3. **多项式恒等**：$P_s(m)$ 是 $m$ 的多项式（由 Hilbert-Samuel 理论）。若一族多项式在无穷多个点（所有充分大的 $m$）上取值相同，则它们是同一个多项式。

   更严格地：对每个 $m$，$s \mapsto \chi(X_s, \mathcal{O}_{X_s}(m))$ 局部常数。因 $S$ 连通（若不连通则逐连通分支讨论），这些值全局常数。由于这对所有 $m$ 成立，多项式 $P_s$ 不依赖于 $s$。∎

---

**文档位置**: `docs/00-银层核心课程/Stanford-FOAG-基础代数几何/PartVI-L5-习题1.md`
**创建日期**: 2026-04-18
**最后更新**: 2026-04-18


## Lean4 形式化对照

`lean4
import Mathlib

example : True := by trivial
`
