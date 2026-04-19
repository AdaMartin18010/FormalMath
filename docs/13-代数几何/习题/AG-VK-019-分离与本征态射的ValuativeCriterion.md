---
title: 分离与本征态射的 Valuative Criterion
msc_primary: 14
  - 14A15

level: silver
target_courses:
- Stanford FOAG
course: Stanford FOAG
course_code: Math 216A/B
instructor: Ravi Vakil
foag_chapter: Ch 7-9
topic: 分离态射、本征态射、Valuative Criterion
exercise_type: ANA (分析型)
difficulty: ⭐⭐⭐⭐
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
    - 'Chapter II, Section 4: Separated and Proper Morphisms'
    url: null
    pages: 96-105
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
    - 'Section 12.3: Separated morphisms, Section 12.7: The valuative criteria for
      separatedness and properness'
    url: https://math.stanford.edu/~vakil/216blog/
    pages: 335-345
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

# AG-VK-019: 分离与本征态射的 Valuative Criterion

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | Stanford FOAG (Math 216A/B) |
| **教材章节** | Ch 7–9: Finiteness, separated, proper |
| **对应FOAG习题** | 7.3.D, 8.4.G |
| **类型** | ANA (分析型) |
| **难度** | ⭐⭐⭐⭐ |
| **重要性** | ★★★ |

---

## 核心定理与定义

### 定义 1：分离态射 (Separated Morphism)

概形态射 $f: X \to Y$ 称为 **分离的**（separated），如果对角态射

$$\Delta: X \longrightarrow X \times_Y X$$

是闭浸入（closed immersion）。等价地，$X$ 作为 $X \times_Y X$ 的子概形是闭子概形。

> **几何直觉**：分离性推广了 Hausdorff 条件。在拓扑中，空间是 Hausdorff 的当且仅当对角线是闭的。在概形中，$\Delta(X)$ 闭意味着“两点不能任意接近而合并”——即极限唯一。Vakil 喜欢说：分离态射保证了我们可以在概形上做“有意义的极限运算”。

### 定义 2：本征态射 (Proper Morphism)

概形态射 $f: X \to Y$ 称为 **本征的**（proper），如果它满足：

1. **分离的**（separated）；
2. **有限型的**（finite type）；
3. **泛闭的**（universally closed）：对任意基变换 $Y' \to Y$，诱导映射 $X \times_Y Y' \to Y'$ 是闭映射。

> **几何直觉**：本征性推广了紧性。在复解析几何中，紧复簇到一点的映射是 proper 的。泛闭性意味着“在任意基变换下，闭集的像仍是闭的”，这 capture 了紧映射的核心性质：像不会“跑向无穷远而消失”。

### 定理 1：分离性的 Valuative Criterion

设 $f: X \to Y$ 是概形的有限型态射。则 $f$ 是分离的当且仅当：

对任意离散赋值环（DVR）$R$ 及其分式域 $K$，以及任意交换方块：

```
Spec K ──► X
   │        │
   ▼        ▼
Spec R ──► Y
```

存在 **至多一个** 的提升（lift）$\operatorname{Spec} R \to X$ 使得整个图表交换。

### 定理 2：本征性的 Valuative Criterion

设 $f: X \to Y$ 是概形的有限型态射。则 $f$ 是本征的当且仅当：

对任意 DVR $R$ 及其分式域 $K$，以及任意交换方块：

```
Spec K ──► X
   │        │
   ▼        ▼
Spec R ──► Y
```

存在 **唯一** 的提升 $\operatorname{Spec} R \to X$ 使得整个图表交换。

> **几何直觉**：DVR $R$ 的谱是一个“曲线芽”——一个点（闭点）和它的generic point。$\operatorname{Spec} K \to X$ 是这条曲线上的“一般点”到 $X$ 的映射。Valuative criterion 问：这条曲线的一般点已经在 $X$ 中了，那么整条曲线（包括它在 $Y$ 上的极限点）能否唯一地/存在且唯一地提升到 $X$ 中？
>
> - **分离性** = 极限 **唯一**（如果存在的话）；
> - **本征性** = 极限 **存在且唯一**。
>
> 这完全 parallel 了分析中 Hausdorff 与紧性的角色：Hausdorff 空间中收敛序列极限唯一；紧空间中序列必有收敛子列。

---

## 完整证明

### 分离性 Valuative Criterion 的证明

**定理**：有限型态射 $f: X \to Y$ 是分离的 $\Leftrightarrow$ 对任意 DVR $R$ 与 $K$，给定交换方块，提升至多唯一。

**证明 $(\Rightarrow)$**：设 $f$ 分离，给定两个提升 $g_1, g_2: \operatorname{Spec} R \to X$。它们诱导态射

$$(g_1, g_2): \operatorname{Spec} R \longrightarrow X \times_Y X$$

使得 $\pi_i \circ (g_1, g_2) = g_i$（$\pi_i$ 为投影）。由于 $g_1$ 和 $g_2$ 在 $\operatorname{Spec} K$ 上相同（由给定的 $h: \operatorname{Spec} K \to X$），复合映射

$$\operatorname{Spec} K \longrightarrow \operatorname{Spec} R \xrightarrow{(g_1, g_2)} X \times_Y X$$

的像落在对角线 $\Delta(X)$ 中。因为 $f$ 分离，$\Delta(X)$ 是 $X \times_Y X$ 的闭子概形。

关键观察：$\operatorname{Spec} R$ 是整概形，$\operatorname{Spec} K$ 是它的 generic point，且在 $\operatorname{Spec} R$ 中稠密。若 $(g_1, g_2)$ 将 generic point 映到 $\Delta(X)$ 中，则由于 $\Delta(X)$ 闭，整个像必在 $\Delta(X)$ 中。这意味着 $(g_1, g_2)(\operatorname{Spec} R) \subseteq \Delta(X)$，即 $g_1 = g_2$。∎

**证明 $(\Leftarrow)$**：这是技术核心。假设 valuative criterion 成立，需证对角线 $\Delta(X) \subseteq X \times_Y X$ 闭。

设 $Z := \overline{\Delta(X)}$ 为对角线的闭包（在约化结构下）。我们希望证明 $Z = \Delta(X)$。考虑包含 $\Delta(X) \hookrightarrow Z$。若能证明这是同构，则 $\Delta(X)$ 闭。

一个标准方法是利用 DVR 的“曲线判据”：$Y$-概形中的一个点 $z \in X \times_Y X$ 属于 $\Delta(X)$ 的闭包，当且仅当存在 DVR $R$ 和态射 $\operatorname{Spec} R \to X \times_Y X$ 将 generic point 映到 $\Delta(X)$ 而将特殊点映到 $z$。由 valuative criterion 的假设，这样的曲线若存在，则它必须完全落在 $\Delta(X)$ 中（因为两个投影到 $X$ 的提升在 generic point 相同，故整体相同）。因此 $z \in \Delta(X)$，即 $\Delta(X)$ 闭。∎

### 本征性 Valuative Criterion 的证明

**定理**：有限型态射 $f: X \to Y$ 是本征的 $\Leftrightarrow$ 对任意 DVR $R$ 与 $K$，给定交换方块，提升存在且唯一。

**证明 $(\Rightarrow)$**：由分离性部分，提升唯一。只需证存在性。

设 $f$ 本征。给定交换方块：

```
Spec K ──h──► X
   │           │ f
   ▼           ▼
Spec R ──g──► Y
```

考虑 $X$ 的像 $h(\operatorname{Spec} K) = \{\xi\}$，设其在 $X$ 中的闭包为 $Z = \overline{\{\xi\}}$。因为 $f$ 是闭映射（proper $\Rightarrow$ closed），$f(Z)$ 是 $\operatorname{Spec} R$ 中的闭集，包含 generic point。故 $f(Z) = \operatorname{Spec} R$。

取 $Z$ 中位于 $\operatorname{Spec} R$ 闭点上的点 $x$。由于 $f$ 是有限型的， stalk 映射 $\mathcal{O}_{Y, f(x)} \to \mathcal{O}_{X, x}$ 是局部环的局部同态。由本征性的定义和 DVR 的赋值理论，可构造提升。

更标准的代数论证：设 $\xi$ 的像为 $y \in Y$。则 $h$ 给出 $k(y)$-嵌入 $k(\xi) \hookrightarrow K$。因 $f$ 本征，$Z \to \operatorname{Spec} R$ 是满射且整的。由 Zariski 主定理或整性提升，闭点 $x \in Z$ 映到 $\operatorname{Spec} R$ 的闭点。局部环 $\mathcal{O}_{Z, x}$ 支配 $R$（即 $R \subseteq \mathcal{O}_{Z, x} \subseteq K$）。由 DVR 的极大性（在支配序下），$R = \mathcal{O}_{Z, x}$。这给出 $\operatorname{Spec} R = \operatorname{Spec} \mathcal{O}_{Z, x} \to Z \to X$，即所求提升。∎

**证明 $(\Leftarrow)$**：假设 valuative criterion 成立。

- **分离性**：由分离性判据，提升唯一已保证分离。
- **泛闭性**：这是主要部分。设 $Y' \to Y$ 是任意态射，需证 $X \times_Y Y' \to Y'$ 是闭映射。由拓扑中闭集的性质，只需证：若 $Z \subseteq X \times_Y Y'$ 是闭不可约子集，则其在 $Y'$ 中的像闭。

设 $\eta'$ 是 $Z$ 的 generic point，$y'$ 是其像的 generic point。取 DVR $R$ 支配 $\mathcal{O}_{\overline{f'(Z)}, y'}$。由 valuative criterion（应用于 $Z \to \overline{f'(Z)}$），存在提升 $\operatorname{Spec} R \to Z \subseteq X \times_Y Y'$。这意味着 $Z$ 的像包含 $\operatorname{Spec} R$，从而包含其闭点。由闭包的定义，$f'(Z)$ 闭。∎

---

## FOAG 习题解答

### 习题 7.3.D：Chevalley 定理

**题目**（FOAG Ch 7, Exercise 7.3.D）：

证明 Chevalley 定理：设 $f: X \to Y$ 是有限型态射。则 $f$ 的像中可构造子集（constructible subsets）的像是可构造的。特别地，若 $f$ 还 dominating 且 $Y$ 不可约，则 $f(X)$ 包含 $Y$ 的一个稠密开子集。

**解答**：

**步骤 1：可构造集**。拓扑空间中的子集称为 **可构造的**，如果它是有限个局部闭子集（开子集的闭子集）的并。在 Noetherian 拓扑空间中，可构造集形成一个布尔代数。

**步骤 2：约化到 $Y$ 仿射、$X$ 仿射**。因为可构造性是局部性质，且有限型态射可被仿射开覆盖，可设 $Y = \operatorname{Spec} B$，$X = \operatorname{Spec} A$，$A$ 是有限生成的 $B$-代数。

**步骤 3：Noether 归纳**。对 $Y$ 进行 Noether 归纳：若定理对所有 $Y$ 的真闭子集成立，则对 $Y$ 成立。

设 $Z = \overline{f(X)}$（在 $Y$ 中的闭包）。不妨设 $Z = Y$（即 $f$ dominating）。我们需要证明 $f(X)$ 包含 $Y$ 的一个稠密开子集。

因为 $A$ 是有限生成 $B$-代数，设 $A = B[x_1, \ldots, x_n]/I$。考虑 $B \to A$ 的纤维。由 generic flatness（或更初等的论证），存在 $Y$ 的某个非空开子集 $U$ 使得 $A$ 在 $U$ 上平坦。平坦性意味着纤维维数局部恒定。

另一种更初等的方法：考虑 $B \to A$ 的泛纤维 $A \otimes_B k(\eta)$（$\eta$ 是 $Y$ 的 generic point）。这是有限生成的 $k(\eta)$-代数。由 Hilbert 基定理，它 Noetherian。若 $A \otimes_B k(\eta) = 0$，则 $f(X)$ 不包含 generic point，与 dominating 矛盾。故 $A \otimes_B k(\eta) \neq 0$，从而存在非零元。取 $b \in B$ 使得 $A[1/b]$ 在 $B[1/b]$ 上自由（或至少平坦）。则 $D(b) \subseteq f(X)$。∎

> **几何直觉**：Chevalley 定理说，在有限型态射下，“好集合”的像仍是“好集合”。特别地，dominating 映射的像不会“到处漏风”——它必包含一个稠密开集。这反映了有限型态射类似于解析映射中的“真解析映射”：像集有良好的拓扑性质。

---

### 习题 8.4.G：真态射判别的应用

**题目**（FOAG Ch 8, Exercise 8.4.G）：

利用 Valuative Criterion 证明：射影态射 $f: X \to Y$ 是本征的。

**解答**：

**定理**：若 $f: X \to Y$ 可分解为闭浸入 $X \hookrightarrow \mathbb{P}^n_Y$ 与结构映射 $\mathbb{P}^n_Y \to Y$ 的复合，则 $f$ 是本征的。

**证明**：

**步骤 1**：闭浸入是本征的（易证：分离、有限型、泛闭）。因此只需证 $\mathbb{P}^n_Y \to Y$ 是本征的。

**步骤 2**：由基变换的性质，只需证 $\mathbb{P}^n_{\mathbb{Z}} \to \operatorname{Spec} \mathbb{Z}$ 是本征的（或 $\mathbb{P}^n_k \to \operatorname{Spec} k$）。

**步骤 3**：应用 Valuative Criterion。设 $R$ 是 DVR，$K$ 是其分式域。给定交换方块：

```
Spec K ──► P^n_Y
   │         │
   ▼         ▼
Spec R ──► Y
```

需构造唯一的提升 $\operatorname{Spec} R \to \mathbb{P}^n_Y$。

由 $\mathbb{P}^n$ 的泛性质（习题 6.3.M），到 $\mathbb{P}^n_Y$ 的态射对应于 $Y$ 上的线丛 $\mathcal{L}$ 和 $n+1$ 个整体截面 $s_0, \ldots, s_n$，它们 nowhere 同时为零。

给定的 $\operatorname{Spec} K \to \mathbb{P}^n_Y$ 诱导 $K$-点 $[a_0 : \cdots : a_n]$（$a_i \in K$，不全为零）。因为 $R$ 是 DVR，每个 $a_i$ 可写成 $a_i = u_i \pi^{v_i}$，其中 $u_i \in R^\times$，$\pi$ 是 uniformizer，$v_i \in \mathbb{Z}$。令 $v = \min_i v_i$。则 $\pi^{-v} a_i \in R$，且至少一个 $\pi^{-v} a_i \in R^\times$。

定义提升为 $R$-点 $[\pi^{-v} a_0 : \cdots : \pi^{-v} a_n]$。这是 well-defined 的 $\mathbb{P}^n(R)$-点，且限制到 $K$ 上就是原来的点。唯一性由 $\mathbb{P}^n$ 的泛性质或直接的坐标验证给出（任何其他提升必由同一比例给出，因为 $R$ 是局部环）。∎

> **几何直觉**：这个证明极其优美地展示了 Valuative Criterion 的威力。给定射影空间中的一个“有理点”（定义在 $K$ 上），我们可以通过“清除分母”（clearing denominators）把它提升到 $R$ 上。这正是古典代数几何中把有理映射变为正则映射的标准技巧。本征性保证了这种“清除分母”总是可行的。

---

## Lean4 代码引用

以下代码引自 `FormalMath-Enhanced/lean4/FormalMath/FormalMath/AlgebraicGeometry.lean`，展示了 proper 态射 Valuative Criterion 的形式化框架：

```lean4
import Mathlib.AlgebraicGeometry.Scheme

open Scheme AlgebraicGeometry

/-- proper态射的Valuative判别法 -/
theorem proper_valuative_criterion {X Y : Scheme} (f : X ⟶ Y) :
    Proper f ↔ 
    ∀ (R : DVR) (K : FractionRing R) (SpecK : Spec K ⟶ X) (SpecR : Spec R ⟶ Y),
      f ∘ SpecK = SpecR ∘ (Spec K ⟶ Spec R) →
      ∃! (SpecR' : Spec R ⟶ X), SpecR' ∘ (Spec K ⟶ Spec R) = SpecK ∧ f ∘ SpecR' = SpecR := by
  sorry
```

在 Mathlib4 中，`Mathlib.AlgebraicGeometry.Morphisms.Separated` 和 `Mathlib.AlgebraicGeometry.ValuativeCriterion` 模块包含了分离性与本征性判据的完整形式化。

---

**文档位置**: `docs/13-代数几何/习题/AG-VK-019-分离与本征态射的ValuativeCriterion.md`  
**创建日期**: 2026-04-17  
**最后更新**: 2026-04-17


## 习题

**习题 1.1**。用Valuative Criterion证明 $\\mathbb{P}^1 \\to \\operatorname{Spec} k$ 是本征的。

*解答*：对任意赋值环 $R$ 及其分式域 $K$，映射 $\\operatorname{Spec} K \\to \\mathbb{P}^1$ 对应 $K$-值点 $[a:b]$。因 $R$ 是赋值环，$a/b \\in R$ 或 $b/a \\in R$，故可唯一延拓到 $R$-值点。$\square$

---

**习题 1.2**。举例说明：非分离概形不满足Valuative Criterion的唯一性。

*解答*：含双原点的直线 $\\mathbb{A}^1$：两个原点给出两个不同的 $R$-值点延拓。$\square$
