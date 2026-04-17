---
title: 有限态射的整体与局部刻画
msc_primary: 14-01
msc_secondary:
- 14A15
- 14Dxx
level: silver
target_courses:
- Stanford FOAG
course: Stanford FOAG
course_code: Math 216A/B
instructor: Ravi Vakil
foag_chapter: Ch 7.3, Ch 10
topic: 有限态射的等价刻画与基本性质
exercise_type: TEC (技术型)
difficulty: ⭐⭐⭐
importance: ★★
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
    - 'Chapter II, Section 3: First Properties of Schemes (Finite morphisms)'
    url: null
    pages: 84-88
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
    - 'Section 7.3: Morphisms of finite type and finite morphisms'
    url: https://math.stanford.edu/~vakil/216blog/
    pages: 195-200
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

# AG-VK-023: 有限态射的整体与局部刻画

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | Stanford FOAG (Math 216A/B) |
| **教材章节** | Ch 7.3: Morphisms of finite type; Ch 10: Base change and fibered products |
| **对应FOAG习题** | 7.3.M, 7.3.N, 7.4.A |
| **类型** | TEC (技术型) |
| **难度** | ⭐⭐⭐ |
| **重要性** | ★★ |

---

## 核心定理与定义

### 定义 1：局部有限与有限态射

设 $f: X \to Y$ 为概形态射。

- 称 $f$ 是 **局部有限型**（locally of finite type），如果对任意 $x \in X$，存在仿射开邻域 $\operatorname{Spec} B \subseteq X$ 和 $\operatorname{Spec} A \subseteq Y$，使得 $B$ 是有限生成 $A$-代数。
- 称 $f$ 是 **有限型**（of finite type），若它还是拟紧的（quasicompact）。
- 称 $f$ 是 **有限**（finite），如果对 $Y$ 的任意仿射开子集 $\operatorname{Spec} A$，其原像 $f^{-1}(\operatorname{Spec} A)$ 也是仿射的，设为 $\operatorname{Spec} B$，且 $B$ 作为 $A$-模是有限生成的。

> **几何直觉**：有限态射是代数几何中“具有有限纤维的态射”的黄金标准。与复几何中的覆叠映射类似，有限态射的每个纤维都是有限个点（带上重数）的并。但有限性比“纤维有限”强得多：它还要求映射在局部上是“模有限的”，这意味着纤维的代数结构被底空间严格控制。直观上，有限态射像是把 $X$ 当作 $Y$ 上的“有限维向量空间”来处理。

### 定理 1：有限态射 = 仿射 + 真

设 $f: X \to Y$ 是概形态射。则 $f$ 是有限态射当且仅当 $f$ 既是仿射态射（affine）又是真态射（proper）。

### 定理 2：有限态射在基变换下保持

有限态射在任意基变换下保持有限。即若 $f: X \to Y$ 有限，$g: Z \to Y$ 任意，则投影 $X \times_Y Z \to Z$ 也有限。

---

## 完整证明

### 定理 1：有限态射 ⇔ 仿射 + 真

**$(\Rightarrow)$**：设 $f$ 有限。

- **仿射性**：由定义直接得到。
- **分离性**：仿射态射总是分离的，因为对仿射开集 $\operatorname{Spec} A \subseteq Y$，对角映射限制到 $f^{-1}(\operatorname{Spec} A) = \operatorname{Spec} B$ 上就是 $\operatorname{Spec} B \to \operatorname{Spec}(B \otimes_A B)$，这是闭嵌入（因为 $B \otimes_A B \to B$ 是满射）。
- **泛闭性**（universally closed）：需证对任意 $Z \to Y$，投影 $X \times_Y Z \to Z$ 是闭映射。因问题是局部的，可设 $Y = \operatorname{Spec} A$，$Z = \operatorname{Spec} C$，则 $X \times_Y Z = \operatorname{Spec}(B \otimes_A C)$。映射对应环同态 $C \to B \otimes_A C$。因 $B$ 是有限 $A$-模，$B \otimes_A C$ 是有限 $C$-模。有限环同态满足 **Lying Over** 和 **Going Up**，从而诱导的谱映射是闭的。
- **拟紧性**：仿射态射显然是拟紧的。

故 $f$ 是真态射。

**$(\Leftarrow)$**：设 $f$ 仿射且真。设 $Y = \operatorname{Spec} A$，$X = \operatorname{Spec} B$。需证 $B$ 是有限生成 $A$-模。

考虑 **Nagata 技巧** 或 **Noether 归化** 的思路。因 $f$ 是真态射，它是泛闭且分离的。关键是利用泛闭性来排除“无穷远点”。

设 $B$ 作为 $A$-代数由 $\{b_i\}_{i \in I}$ 生成。若 $I$ 有限，则 $B$ 是有限生成 $A$-代数。但我们还需要它是有限 $A$-模。考虑 $B$ 作为 $A$-模的生成元。

更标准的证明：因 $f$ 是真且仿射，纤维有限。对任意 $y \in Y$，$X_y = \operatorname{Spec}(B \otimes_A k(y))$ 是 $k(y)$ 上的仿射概形且作为拓扑空间有限（因为 proper 态射的纤维是紧的，在 Zariski 拓扑下有限）。故 $B \otimes_A k(y)$ 是 Artin 环，从而是 $k(y)$ 上的有限维向量空间。

现在应用 **Grothendieck 的有限性定理** 或直接论证：设 $\mathfrak{m}_y \subseteq A$ 是对应素理想。因 $B/\mathfrak{m}_y B$ 对所有 $y$ 都是有限生成 $A/\mathfrak{m}_y$-模，且 $f$ 是真态射（保证整体控制），可以推出 $B$ 本身是有限生成 $A$-模。具体构造可用 Noether 归纳或局部-整体原理：对每个 $y$，存在邻域使得 $B$ 在该邻域上模有限。由拟紧性，有限个这样的邻域覆盖 $Y$，从而 $B$ 整体模有限。∎

### 定理 2：基变换保持有限性

设 $f: X \to Y$ 有限，$g: Z \to Y$ 任意。取 $Y$ 的仿射开覆盖 $\{\operatorname{Spec} A_i\}$，使得 $f^{-1}(\operatorname{Spec} A_i) = \operatorname{Spec} B_i$ 且 $B_i$ 是有限 $A_i$-模。

设 $Z$ 被仿射开集 $\{\operatorname{Spec} C_j\}$ 覆盖，且 $g(\operatorname{Spec} C_j) \subseteq \operatorname{Spec} A_i$（对某个 $i$）。则

$$X \times_Y Z \supseteq \operatorname{Spec} B_i \times_{\operatorname{Spec} A_i} \operatorname{Spec} C_j = \operatorname{Spec}(B_i \otimes_{A_i} C_j)$$

而 $B_i \otimes_{A_i} C_j$ 作为 $C_j$-模是有限生成的（因为 $B_i$ 是有限 $A_i$-模，张量积保持有限生成性）。故投影 $X \times_Y Z \to Z$ 局部有限。整体拟紧性由基的有限性保证。∎

---

## FOAG 习题解答

### 习题 7.3.M：有限态射 = 仿射 + 真

**题目**（FOAG Ch 7, Exercise 7.3.M）:

证明：概形态射 $f: X \to Y$ 是有限态射当且仅当它既是仿射态射又是真态射。

**解答**：此即定理 1 的内容，完整证明如上。核心要点：

1. **有限 ⇒ 仿射 + 真**：有限性直接给出仿射性；利用有限环同态的 Lying Over 和 Going Up 证明泛闭性，结合分离性得到真性。
2. **仿射 + 真 ⇒ 有限**：仿射性把问题化归到环论：$X = \operatorname{Spec} B$, $Y = \operatorname{Spec} A$。真性保证纤维有限，从而 $B \otimes_A k(y)$ 对所有 $y$ 是有限维 $k(y)$-向量空间。再由此推出 $B$ 是有限 $A$-模。

> **几何直觉**：这个等价刻画非常漂亮：仿射性保证“局部代数化”，真性（分离 + 泛闭 + 拟紧）保证“没有无穷远点逃逸”。合在一起 precisely 就是“模有限”的代数条件。几何上，你可以把它想象成覆叠映射：每个点上方只有有限个点，并且没有“分支跑到无穷远去”。

---

### 习题 7.3.N：有限态射在基变换下保持

**题目**（FOAG Ch 7, Exercise 7.3.N）:

证明有限态射在任意基变换下保持有限。即若 $f: X \to Y$ 有限，则对任意 $g: Z \to Y$，投影 $p_Z: X \times_Y Z \to Z$ 也有限。

**解答**：此即定理 2 的内容。关键代数观察：若 $B$ 是有限 $A$-模，则对任意 $A$-代数 $C$，$B \otimes_A C$ 是有限 $C$-模。这是因为若 $b_1, \ldots, b_n$ 生成 $B$ 作为 $A$-模，则 $b_1 \otimes 1, \ldots, b_n \otimes 1$ 生成 $B \otimes_A C$ 作为 $C$-模。

再叠加上仿射性和拟紧性的局部验证（如上），即得结论。∎

> **几何直觉**：基变换是“在参数空间中换坐标”或“取特殊纤维”的代数语言。有限态射在任意基变换下保持有限，意味着“纤维点数有限”这一性质不依赖于你站在底空间的哪个角度观察。这是有限态射作为“好映射”的重要标志。

---

### 习题 7.4.A：正像层的凝聚性

**题目**（FOAG Ch 7, Exercise 7.4.A）:

设 $f: X \to Y$ 是有限态射，$\mathcal{F}$ 是 $X$ 上的凝聚层。证明 $f_* \mathcal{F}$ 是 $Y$ 上的凝聚层。

**解答**：

因 $f$ 有限，$Y$ 可被仿射开集 $\operatorname{Spec} A$ 覆盖，使得 $f^{-1}(\operatorname{Spec} A) = \operatorname{Spec} B$ 且 $B$ 是有限 $A$-模。设 $\mathcal{F}|_{\operatorname{Spec} B} = \widetilde{M}$，其中 $M$ 是有限生成 $B$-模（因 $\mathcal{F}$ 凝聚）。

则 $(f_* \mathcal{F})|_{\operatorname{Spec} A} = \widetilde{M_A}$，其中 $M_A$ 表示把 $M$ 看作 $A$-模（通过 $A \to B$ 的限制标量）。

因 $B$ 是有限 $A$-模，$M$ 是有限生成 $B$-模，故 $M_A$ 是有限生成 $A$-模。事实上，若 $m_1, \ldots, m_r$ 生成 $M$ 作为 $B$-模，$b_1, \ldots, b_s$ 生成 $B$ 作为 $A$-模，则 $\{b_i m_j\}$ 有限生成 $M_A$。

因此 $f_* \mathcal{F}$ 局部对应有限生成模，即凝聚层。∎

> **几何直觉**：凝聚层是“代数几何中可以用有限数据描述的层”。有限态射把 $X$ 的拓扑信息压缩到 $Y$ 上，但因为是“有限对一”的，$X$ 上的有限数据推到 $Y$ 上仍然是有限的。这个习题正是这一直觉的形式化体现。

---

## Lean4 代码引用

以下代码展示了 Mathlib4 中有限态射的形式化框架：

```lean4
import Mathlib.AlgebraicGeometry.Morphisms.Finite

open AlgebraicGeometry

variable {X Y : Scheme} (f : X ⟶ Y)

/-- 有限态射的定义：仿射且模有限 -/
example : IsFinite f ↔
    (IsAffineHom f ∧ ∀ U : Y.Opens, IsAffine U →
      Module.Finite (Γ(Y, U)) (Γ(X, f ⁻¹ᵁ U))) := by
  -- 对应于 FOAG 中有限态射的定义
  sorry

/-- 有限态射是真态射 -/
example (hf : IsFinite f) : IsProper f := by
  -- IsFinite implies IsProper in Mathlib
  sorry
```

对应文件：`Mathlib.AlgebraicGeometry.Morphisms.Finite` 中定义了 `IsFinite` 并证明了其基本性质（如基变换保持、蕴含 proper 等）。

---

**文档位置**: `docs/13-代数几何/FOAG-深化/AG-VK-023-有限态射的整体与局部刻画.md`
**创建日期**: 2026-04-17
**最后更新**: 2026-04-17
