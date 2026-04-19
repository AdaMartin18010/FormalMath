---
title: 平坦性、光滑性与上同调基变换
msc_primary: 14
  - 14F17
level: silver
target_courses:
- Stanford FOAG
course: Stanford FOAG
course_code: Math 216A/B
instructor: Ravi Vakil
foag_chapter: Ch 23-25
topic: 平坦性、光滑性、上同调与基变换
exercise_type: THM (理论型)
difficulty: ⭐⭐⭐⭐⭐
importance: ★★★
references:
  textbooks:
  - id: hartshorne_ag
    type: textbook
    title: Algebraic Geometry
    authors:
    - Robin Hartshorne
    publisher: Springer
    edition: 1st
    year: 1977
    isbn: 978-0387902449
    msc: 14-01
    chapters:
    - 'Chapter III, Section 9: Flat Morphisms; Chapter III, Section 10: Smooth Morphisms'
    url: null
    pages: 253-269
  - id: vakil_foag
    type: textbook
    title: Foundations of Algebraic Geometry
    authors:
    - Ravi Vakil
    publisher: self-published
    edition: draft
    year: 2024
    isbn: null
    msc: 14-01
    chapters:
    - 'Section 24.6: Flatness, Section 25.2: Smooth morphisms, Section 28.1: Base
      change theorems'
    url: https://math.stanford.edu/~vakil/216blog/
    pages: 655-675
  databases:
  - id: nlab
    type: database
    name: nLab
    entry_url: https://ncatlab.org/nlab/show/{entry}
    consulted_at: 2026-04-17
  - id: stacks_project
    type: database
    name: Stacks Project
    entry_url: https://stacks.math.columbia.edu/tag/{tag}
    consulted_at: 2026-04-17
  - id: zbmath
    type: database
    name: zbMATH Open
    entry_url: https://zbmath.org/?q=an:{zb_id}
    consulted_at: 2026-04-17
---

# AG-VK-022: 平坦性、光滑性与上同调基变换

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | Stanford FOAG (Math 216A/B) |
| **教材章节** | Ch 23–25: Derived functors, flatness, base change |
| **对应FOAG习题** | 24.5.J, 25.2.E |
| **类型** | THM (理论型) |
| **难度** | ⭐⭐⭐⭐⭐ |
| **重要性** | ★★★ |

---

## 核心定理与定义

### 定义 1：平坦模与平坦态射

设 $A$ 为交换环，$M$ 为 $A$-模。称 $M$ 是 **平坦的**（flat），如果函子 $- \otimes_A M: \mathbf{Mod}_A \to \mathbf{Mod}_A$ 是正合的。

概形态射 $f: X \to Y$ 称为 **平坦的**，如果对任意 $x \in X$， stalk $\mathcal{O}_{X,x}$ 是平坦的 $\mathcal{O}_{Y,f(x)}$-模。

> **几何直觉**：平坦性保证纤维“连续变化”。在非平坦族中，纤维可能突然“爆炸”或“坍塌”——例如，从一条直线退化到一个带一个embedded point的曲线。平坦性禁止这种病态行为，确保像维数、次数、Hilbert 多项式等数值不变量在族中保持恒定。

### 定义 2：光滑态射

概形态射 $f: X \to Y$ 称为 **光滑的**（smooth），如果它满足：

1. 局部有限表示（locally of finite presentation）；
2. 平坦的（flat）；
3. 所有几何纤维都是正则的（regular）。

若相对维数为 $d$，则称为 **相对维数 $d$ 的光滑态射**。

> **几何直觉**：光滑态射是“纤维化”的正确概形类比。每个纤维都是光滑的，且维度恒定。在复几何中，光滑态射对应于复流形间的淹没（submersion）。Vakil 强调：光滑态射是代数几何中“好映射”的黄金标准。

### 定理 1：局部平坦判别法

设 $A$ 是 Noether 局部环，$\mathfrak{m}$ 是其极大理想，$k = A/\mathfrak{m}$，$M$ 是有限生成 $A$-模。则以下等价：

1. $M$ 是平坦 $A$-模；
2. $\operatorname{Tor}_1^A(M, k) = 0$；
3. $M$ 是自由 $A$-模。

（在 Noether 局部环上，有限生成平坦模 = 自由模）

### 定理 2：上同调与基变化定理（Cohomology and Base Change）

设 $f: X \to Y$ 是 proper 态射，$Y$ 是 Noether 概形，$\mathcal{F}$ 是 $X$ 上的凝聚层且平坦于 $Y$。设 $y \in Y$，$\phi^i(y): (R^i f_* \mathcal{F})_y \otimes_{\mathcal{O}_{Y,y}} k(y) \to H^i(X_y, \mathcal{F}_y)$ 是自然映射。

若 $\phi^i(y)$ 是满射，则：

1. $\phi^i(y)$ 是同构；
2. 在 $y$ 的某邻域上，$R^i f_* \mathcal{F}$ 是局部自由的，且与纤维上同调相容。

若进一步 $\phi^{i-1}(y)$ 也是满射（从而同构），则在 $y$ 附近上同调“平坦变化”，即短正合列保持。

> **几何直觉**：这个定理回答了核心问题：当我们把参数 $y \in Y$ 稍微扰动时，纤维上同调 $H^i(X_y, \mathcal{F}_y)$ 如何变化？定理说：如果高阶直接像的“特殊化映射”是满射，那么上同调在 $y$ 附近是“良好行为”的——它不仅维数局部恒定，而且作为向量丛光滑变化。这是研究族的几何（如模空间理论）的基石。

---

## 完整证明

### 局部平坦判别法的证明

**设定**：$A$ Noether 局部环，$M$ 有限生成。

**$(1) \Rightarrow (2)$**：平坦模的正合性意味着 $\operatorname{Tor}_i^A(M, -) = 0$（$i > 0$）。特别地，$\operatorname{Tor}_1^A(M, k) = 0$。∎

**$(3) \Rightarrow (1)$**：自由模显然是平坦的。∎

**$(2) \Rightarrow (3)$**（核心）：

设 $\{x_1, \ldots, x_n\}$ 是 $M/\mathfrak{m}M$ 作为 $k$-向量空间的基。提升为 $M$ 中元素 $m_1, \ldots, m_n$。由 Nakayama 引理，$m_1, \ldots, m_n$ 生成 $M$。

考虑满射 $\pi: A^n \to M$，$\pi(e_i) = m_i$。设 $K = \ker(\pi)$。需证 $K = 0$。

考虑正合列 $0 \to K \to A^n \to M \to 0$。与 $k$ 取张量积：

$$\operatorname{Tor}_1^A(M, k) \to K \otimes k \to A^n \otimes k \to M \otimes k \to 0$$

由假设 $\operatorname{Tor}_1^A(M, k) = 0$，且 $A^n \otimes k \to M \otimes k$ 是同构（因为 $m_i$ mod $\mathfrak{m}$ 是基）。故 $K \otimes k = K/\mathfrak{m}K = 0$。

由 Nakayama 引理，$K = 0$（因为 $K$ 作为 $A^n$ 的子模也是有限生成的，$A$ Noether）。因此 $M \cong A^n$ 是自由模。∎

### 上同调与基变化定理的证明概要

**设定**：$f: X \to Y$ proper，$\mathcal{F}$ 凝聚且 $Y$-平坦。

**步骤 1：化归到仿射情形**。因问题是局部的，可设 $Y = \operatorname{Spec} A$（$A$ Noether）。此时 $R^i f_* \mathcal{F}$ 对应 $A$-模 $H^i(X, \mathcal{F})$。

**步骤 2：万有系数序列**。对 $y \in Y$，设 $\mathfrak{p}$ 是对应素理想，$k(y) = A_\mathfrak{p}/\mathfrak{p}A_\mathfrak{p}$。因 $\mathcal{F}$ 在 $Y$ 上平坦，对任意 $A$-模 $N$，有：

$$H^i(X, \mathcal{F} \otimes_A N) \cong H^i(X, \mathcal{F}) \otimes_A N$$

当 $N$ 平坦时（由平坦基变换）。取 $N = k(y)$，得自然映射：

$$\phi^i(y): H^i(X, \mathcal{F}) \otimes_A k(y) \longrightarrow H^i(X_y, \mathcal{F}_y)$$

**步骤 3：复形的局部自由分解**。取 $X$ 的一个有限仿射开覆盖 $\mathcal{U}$。考虑 Čech 复形 $C^\bullet = \check{C}^\bullet(\mathcal{U}, \mathcal{F})$，这是 $A$ 上有限生成自由模的复形（因 $\mathcal{F}$ 凝聚且覆盖有限）。

计算上同调：$H^i(X, \mathcal{F}) = H^i(C^\bullet)$。由于 $"> $\mathcal{F}$ 在 $Y$ 上平坦，$C^\bullet$ 的每一项都是平坦 $A$-模。复形 $C^\bullet$ 可分解为：

$$C^\bullet = \bigoplus_j A^{n_j}[\text{适当位移}] \text{（作为模，非作为复形）}$$

更准确地说，有限生成模在 Noether 环上有投射分解。利用复形的 truncations 和归纳，可以证明：若 $\phi^i(y)$ 满，则 $H^i(C^\bullet)$ 在 $y$ 附近局部自由。

**步骤 4：局部自由与相容性**。关键引理：对复形 $K^\bullet$ 的有限生成自由 $A$-模，若 $H^i(K^\bullet \otimes k(y)) \to H^i(K^\bullet) \otimes k(y)$ 满，则 $H^i(K^\bullet)$ 在 $y$ 附近局部自由，且与任意基变换相容。

这通过分析复形的微分矩阵的秩来完成：局部自由性等价于微分矩阵的秩局部恒定，而这由满射条件保证。

**步骤 5：导出的局部自由与正合列**。当 $\phi^{i-1}(y)$ 和 $\phi^i(y)$ 都满时，不仅 $H^i$ 局部自由，而且上同调的长正合列在基变换下保持。这是因为 Tor 项消失，从而张量积与上同调交换。∎

---

## FOAG 习题解答

### 习题 24.5.J：平坦性的拓扑含义

**题目**（FOAG Ch 24, Exercise 24.5.J，变形）：

设 $f: X \to Y$ 是有限型态射，$Y$ 是约化且不可约的。证明：$f$ 是平坦的当且仅当所有纤维具有相同的 Hilbert 多项式（对某个固定的极丰富层）。

**解答**：

**$(\Rightarrow)$**：设 $f$ 平坦 proper。对极丰富层 $\mathcal{O}(1)$ 和凝聚层 $\mathcal{O}_X$，Serre 的 flattening stratification 或更直接地，基变化定理告诉我们：高阶直像 $R^i f_* \mathcal{O}_X(n)$ 是局部自由的（$n \gg 0$），且其秩局部恒定。Euler 示性数 $\chi(X_y, \mathcal{O}_{X_y}(n)) = \sum (-1)^i h^i(X_y, \mathcal{O}_{X_y}(n))$ 作为 $y$ 的函数是局部恒定的。因 $Y$ 连通，它整体恒定。而 Hilbert 多项式由大 $n$ 时的 $\chi$ 决定，故所有纤维有相同 Hilbert 多项式。∎

**$(\Leftarrow)$**（概要）：这是更深刻的结果，属于 Grothendieck 的 flattening 理论。核心思想是：若 Hilbert 多项式恒定，则族中纤维的数值不变量（次数、算术亏格等）不变。在约化不可约底空间上，这迫使映射平坦。严格证明需要使用 Hilbert 概形或 flattening stratification：若映射不平坦，则存在一个非空闭子集使得纤维的 Hilbert 多项式跳跃。∎

> **几何直觉**：这个习题完美诠释了平坦性的几何意义：它是“纤维在族中保持恒定型”的代数条件。Hilbert 多项式是型的完整数值不变量，因此平坦性 precisely 对应于 Hilbert 多项式的恒定性。

---

### 习题 25.2.E：上同调与基变化的应用

**题目**（FOAG Ch 25, Exercise 25.2.E）：

设 $f: X \to Y$ 是光滑 proper 曲线族（$Y$ 连通），$\mathcal{L}$ 是 $X$ 上的线丛，限制到每条纤维 $X_y$ 上次数为 $d$。证明函数 $y \mapsto h^0(X_y, \mathcal{L}_y)$ 是 $Y$ 上的上半连续函数，且若 $h^0$ 恒定，则 $f_* \mathcal{L}$ 是局部自由的，且与任意基变换相容。

**解答**：

**步骤 1：上半连续性**。由 Grauert 定理（或更初等的 semicontinuity 定理）：对 proper 态射 $f: X \to Y$ 和 $Y$-平坦的凝聚层 $\mathcal{F}$，函数 $y \mapsto h^i(X_y, \mathcal{F}_y)$ 是上半连续的。这是因为 $R^i f_* \mathcal{F}$ 是凝聚层，其在 $y$ 处的秩（作为 $k(y)$-向量空间）是 $h^i$ 的上界，且随 $y$ 变化而上半连续。

对我们的情形，$\mathcal{L}$ 是线丛，显然 $Y$-平坦（局部自由 = 平坦）。故 $y \mapsto h^0(X_y, \mathcal{L}_y)$ 上半连续。∎

**步骤 2：$h^0$ 恒定 $\Rightarrow$ $f_*\mathcal{L}$ 局部自由**。因 $f$ 是曲线族，上同调维数为 1，即 $R^i f_* \mathcal{L} = 0$（$i > 1$）。考虑上同调与基变化映射：

$$\phi^1(y): (R^1 f_* \mathcal{L})_y \otimes k(y) \longrightarrow H^1(X_y, \mathcal{L}_y)$$

由 Serre 对偶，$h^1(X_y, \mathcal{L}_y) = h^0(X_y, K_{X_y} \otimes \mathcal{L}_y^{-1})$。因 $K_{X_y}$ 的次数为 $2g-2$，$\mathcal{L}_y^{-1}$ 的次数为 $-d$，故 $K_{X_y} \otimes \mathcal{L}_y^{-1}$ 的次数为 $2g-2-d$，与 $y$ 无关。由上半连续性，$h^1(X_y, \mathcal{L}_y)$ 也是上半连续的。

由 Riemann-Roch：

$$h^0(X_y, \mathcal{L}_y) - h^1(X_y, \mathcal{L}_y) = d + 1 - g$$

右边与 $y$ 无关。若 $h^0$ 恒定，则 $h^1$ 也恒定。

现在应用上同调与基变化定理：

- 对 $i = 1$，$\phi^1(y)$ 总是满射（因为 $R^1 f_* \mathcal{L}$ 是凝聚层，其特殊化映射到 $H^1$ 是满的——这是 Grauert 定理的一个推论，或可直接用 Čech 复形验证）。由基变化定理，$\phi^1(y)$ 是同构，且 $R^1 f_* \mathcal{L}$ 局部自由。
- 对 $i = 0$，因 $h^1$ 恒定，$\phi^0(y)$ 的满射性可由长正合列推出。具体地，考虑短正合列 $0 \to \mathcal{L}(-n) \to \mathcal{L} \to \mathcal{L}|_{nP} \to 0$（对某个有效除子），或直接用基变化定理的条件：因 $R^1 f_* \mathcal{L}$ 局部自由，对任意 $y$，映射 $\phi^0(y)$ 是满射。

因此 $f_*\mathcal{L}$ 局部自由，且与基变换相容。∎

> **几何直觉**：这个习题描述了模空间理论中的核心现象。当我们沿着曲线族移动时，线丛的截面个数可能跳跃（上半连续）。但若它不散跃——即保持恒定——那么这些截面就“组织”成了底空间 $Y$ 上的一个向量丛。这是构造模空间（如 Picard 概形、Jacobians）的基本步骤。

---

## Lean4 代码引用

以下代码展示了 Mathlib4 中平坦性与光滑性的形式化框架：

```lean4
import Mathlib.RingTheory.Flat
import Mathlib.AlgebraicGeometry.Smooth

open RingTheory AlgebraicGeometry

variable {A : Type*} [CommRing A] [IsNoetherianRing A]
  (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- Noether局部环上有限生成平坦模等价于自由模 -/
theorem finite_flat_free [IsLocalRing A] :
    Module.Flat A M ↔ Module.Free A M := by
  -- 这对应于本文的局部平坦判别法
  sorry

variable {X Y : Scheme} (f : X ⟶ Y)

/-- 光滑态射的定义 -/
example : IsSmooth f ↔
    (LocallyOfFinitePresentation f ∧ Flat f ∧
     ∀ y, IsRegularLocalRing (𝒪_{fiber f y})) := by
  sorry
```

对应文件：`FormalMath-Enhanced/lean4/FormalMath/FormalMath/AlgebraicGeometry.lean` 中定义了 `IsSmooth` 和 `IsEtale`，并引用了局部环的正则性判别。

---

**文档位置**: `docs/13-代数几何/习题/AG-VK-022-平坦性光滑性与上同调基变换.md`
**创建日期**: 2026-04-17
**最后更新**: 2026-04-17
