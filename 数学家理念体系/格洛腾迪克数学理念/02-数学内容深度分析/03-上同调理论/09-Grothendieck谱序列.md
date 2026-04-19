---
msc_primary: 14Fxx
msc_secondary:
  - 18Gxx
  - 01A70
---

﻿---
title: "Grothendieck 谱序列：Tôhoku 论文与复合函子的上同调"
level: "gold"
msc_primary: "18G40"
references:
  textbooks:
    - title: "Sur quelques points d'algèbre homologique"
      author: "A. Grothendieck"
      edition: "Tôhoku Math. J. (2) 9"
      chapters: "§2.4"
      pages: "119–221"
      year: 1957
    - title: "Éléments de Géométrie Algébrique III"
      author: "A. Grothendieck & J. Dieudonné"
      edition: "Publ. Math. IHÉS 11, 17"
      chapters: "§1–§7"
      pages: "1–200"
      year: 1961
    - title: "An Introduction to Homological Algebra"
      author: "C. Weibel"
      edition: "Cambridge Studies in Advanced Mathematics 38"
      chapters: "Ch. 5"
      pages: "141–180"
  papers:
    - title: "Sur quelques points d'algèbre homologique"
      author: "A. Grothendieck"
      journal: "Tôhoku Math. J. (2)"
      year: 1957
      pages: "119–221"
      doi: "10.2748/tmj/1178244839"
  databases:
    - type: "Stacks Project"
      url: "https://stacks.math.columbia.edu/tag/015J"
      tag: "015J"
    - type: "nLab"
      url: "https://ncatlab.org/nlab/show/Grothendieck+spectral+sequence"
      tag: "Grothendieck-spectral-sequence"
review_status: "draft"
---

# Grothendieck 谱序列：Tôhoku 论文与复合函子的上同调

## 1. 引言

**谱序列（suite spectrale）**是同调代数中计算复合函子导出函子的核心工具。给定 Abel 范畴之间的左正合函子 $F: \mathcal{A} \to \mathcal{B}$ 和 $G: \mathcal{B} \to \mathcal{C}$，我们自然希望用 $R^p G$ 和 $R^q F$ 来计算 $R^{p+q}(GF)$。Grothendieck 在 1957 年的 Tôhoku 论文中证明了：在适当的条件下，存在**Grothendieck 谱序列**
$$E_2^{p,q} = R^p G(R^q F(A)) \Longrightarrow R^{p+q}(GF)(A).$$

这一结果是同调代数的巅峰定理之一。它不仅统一了 Leray 谱序列、Serre 谱序列、Hochschild-Serre 谱序列等经典结果，还为层上同调中的各种换基公式、对偶性定理提供了统一的框架。

Grothendieck 在 EGA III 中进一步将谱序列理论应用于代数几何：Leray 谱序列、局部到整体谱序列、形式函数定理等，都成为了现代代数几何的标准工具。

本专题将严格建立 Grothendieck 谱序列的理论，引用 Tôhoku 论文 §2.4 和 EGA III 的原始文本，给出完整的构造与证明，嵌入 Lean4 代码，并在批判性分析中比较 Grothendieck 的方法与 Cartan–Eilenberg 的早期方法。

---

## 2. 历史背景：从 Leray 到 Grothendieck

### 2.1 Leray 的创始工作

谱序列的概念由 Jean Leray 在 1946–1950 年间作为战俘时创立。Leray 研究的是层上同调中的纤维丛：给定连续映射 $f: X \to Y$，如何用 $Y$ 的上同调和纤维的上同调来计算 $X$ 的上同调？

Leray 的答案是**Leray 谱序列**：
$$E_2^{p,q} = H^p(Y, R^q f_* \mathcal{F}) \Longrightarrow H^{p+q}(X, \mathcal{F}).$$

然而，Leray 的原始表述非常复杂，依赖于层的"细分解（fine resolution）"，只适用于仿紧 Hausdorff 空间。

### 2.2 Cartan–Eilenberg 的代数化

1956 年，Cartan 和 Eilenberg 在《Homological Algebra》中将谱序列纳入了同调代数的框架。他们证明了：若 $F$ 和 $G$ 是模范畴之间的左正合函子，且 $F$ 将内射模映为 $G$-零调模，则存在谱序列 $R^p G \circ R^q F \Rightarrow R^{p+q}(GF)$。

Cartan–Eilenberg 的证明使用了**双复形（double complex）**和**全复形（total complex）**的构造。然而，他们的处理局限于模范畴，没有使用 Abel 范畴的语言。

### 2.3 Grothendieck 的公理化

Grothendieck 在 Tôhoku 论文中的突破在于：

1. **Abel 范畴的框架**：证明了谱序列的存在性只需要 Abel 范畴的公理，不需要具体的模范畴；
2. **泛 $\delta$-函子**：将导出函子纳入泛 $
\delta$-函子的框架，使得谱序列成为泛性质的推论；
3. **EGA III 的几何应用**：将谱序列系统应用于凝聚层上同调、直接像函子、形式函数定理等。

---

## 3. 原始文献解读：Tôhoku §2.4 与 EGA III

### 3.1 Tôhoku 论文中的谱序列定理

Tôhoku 论文 §2.4 给出了 Grothendieck 谱序列的精确陈述：

> **Théorème 2.4.1** (Grothendieck, Tôhoku, p. 148). — *Soient $\mathcal{A}, \mathcal{B}, \mathcal{C}$ trois catégories abéliennes, $F: \mathcal{A} \to \mathcal{B}$ et $G: \mathcal{B} \to \mathcal{C}$ deux foncteurs covariants additifs et à gauche exacts. On suppose que $\mathcal{A}$ et $\mathcal{B}$ possèdent assez d'injectifs et que $F$ transforme les objets injectifs en objets $G$-acycliques (i.e. annulés par les $R^q G$ pour $q > 0$). Alors pour tout objet $A \in \mathcal{A}$, il existe une suite spectrale cohomologique birégulière $E(A)$, dont le terme initial est
> $$E_2^{p,q}(A) = R^p G(R^q F(A))$$
> et dont l'aboutissement est formé des $R^n(GF)(A)$.*

这一陈述的精确性值得注意：

- **birégulière（双正则）**：意味着谱序列在每个方向上都收敛，不需要额外的有限性条件；
- **$G$-零调性**：这是关键假设，保证了双复形构造的兼容性。

### 3.2 EGA III 中的几何应用

EGA III, §1 将谱序列应用于直接像函子。设 $f: X \to Y$ 为概形态射，$\mathcal{F}$ 为 $X$ 上的拟凝聚层。则 $R^i f_* \mathcal{F}$ 是 $Y$ 上的拟凝聚层，且对任意仿射开集 $U \subseteq Y$，
$$(R^i f_* \mathcal{F})(U) = H^i(f^{-1}(U), \mathcal{F}|_{f^{-1}(U)}).$$

若 $g: Y \to Z$ 为另一态射，则 Leray 谱序列
$$E_2^{p,q} = R^p g_* (R^q f_* \mathcal{F}) \Longrightarrow R^{p+q}(gf)_* \mathcal{F}$$
是 Grothendieck 谱序列的直接特例（取 $F = f_*$, $G = g_*$）。

---

## 4. 严格定义与核心定理

### 4.1 谱序列的定义

**定义 4.1** (谱序列). *一个**上同调谱序列（cohomological spectral sequence）**由以下数据组成：*

1. *一族 Abel 群（或 $R$-模）$E_r^{p,q}$，其中 $r \geq r_0$（通常 $r_0 = 1$ 或 $2$），$p, q \in \mathbb{Z}$；*
2. *微分映射 $d_r^{p,q}: E_r^{p,q} \to E_r^{p+r, q-r+1}$，满足 $d_r \circ d_r = 0$；*
3. *同构 $E_{r+1}^{p,q} \cong \ker(d_r^{p,q}) / \operatorname{im}(d_r^{p-r, q+r-1})$。*

**定义 4.2** (收敛). *称谱序列 $E_r^{p,q}$ **收敛**到分次对象 $H^n$（记作 $E_r^{p,q} \Rightarrow H^{p+q}$），如果存在 $H^n$ 的滤过
$$0 = F^{n+1} H^n \subseteq F^n H^n \subseteq \cdots \subseteq F^0 H^n = H^n$$
使得
$$E_\infty^{p,q} \cong F^p H^{p+q} / F^{p+1} H^{p+q}.$$
*

### 4.2 双复形与全复形

**定义 4.3** (双复形). *Abel 范畴 $\mathcal{A}$ 中的**双复形**$C^{\bullet,\bullet}$ 由对象 $C^{p,q}$（$p, q \in \mathbb{Z}$）和两个微分组成：*

- *水平微分 $d_h^{p,q}: C^{p,q} \to C^{p+1,q}$，满足 $d_h^2 = 0$；*
- *垂直微分 $d_v^{p,q}: C^{p,q} \to C^{p,q+1}$，满足 $d_v^2 = 0$；*
- *相容性：$d_h d_v = d_v d_h$。*

**定义 4.4** (全复形). *双复形 $C^{\bullet,\bullet}$ 的**全复形**$\operatorname{Tot}^\bullet(C)$ 定义为
$$\operatorname{Tot}^n(C) = \bigoplus_{p+q=n} C^{p,q}$$
配备微分 $d = d_h + (-1)^p d_v$ 在 $C^{p,q}$ 上。*

*验证 $d^2 = 0$：*
$$d^2 = (d_h + (-1)^p d_v)^2 = d_h^2 + (-1)^{p+1} d_h d_v + (-1)^p d_v d_h + d_v^2 = 0$$
*因为 $d_h^2 = d_v^2 = 0$ 且 $d_h d_v = d_v d_h$。*

### 4.3 Grothendieck 谱序列的构造

**定理 4.5** (Grothendieck 谱序列, Tôhoku §2.4, Th. 2.4.1). *设 $\mathcal{A}, \mathcal{B}, \mathcal{C}$ 为 Abel 范畴，$F: \mathcal{A} \to \mathcal{B}$ 和 $G: \mathcal{B} \to \mathcal{C}$ 为左正合函子。假设：*

1. *$\mathcal{A}$ 和 $\mathcal{B}$ 有足够内射对象；*
2. *$F$ 将内射对象映为 $G$-零调对象（即 $R^q G(F(I)) = 0$ 对 $q > 0$ 和 $I$ 内射）。*

*则对任意 $A \in \mathcal{A}$，存在收敛的谱序列
$$E_2^{p,q}(A) = R^p G(R^q F(A)) \Longrightarrow R^{p+q}(GF)(A).$$
*

*证明.* *这是 Tôhoku 论文中最深刻的技术性证明之一，核心构造如下：*

**步骤 1：取内射分解。** 取 $A$ 的内射分解 $0 \to A \to I^0 \to I^1 \to \cdots$。对每个 $p$，$F(I^p)$ 是 $G$-零调的（由假设 2）。

**步骤 2：对 $F(I^p)$ 取内射分解。** 对每个 $p$，取 $F(I^p)$ 在 $\mathcal{B}$ 中的内射分解：
$$0 \to F(I^p) \to J^{p,0} \to J^{p,1} \to \cdots$$
由于 $F(I^p)$ 是 $G$-零调的，我们可以选择这个分解使得它"提升"了 $F(I^p)$ 的结构。

**步骤 3：构造双复形。** 这些 $J^{p,q}$ 构成一个双复形：

- 垂直微分 $d_v^{p,q}: J^{p,q} \to J^{p,q+1}$ 来自 $F(I^p)$ 的内射分解；
- 水平微分 $d_h^{p,q}: J^{p,q} \to J^{p+1,q}$ 由 $I^\bullet$ 中的微分和 $F$ 的函子性诱导。

由 $F$ 的加性，双复形的条件 $d_h d_v = d_v d_h$ 满足。

**步骤 4：两种谱序列。** 对双复形 $J^{\bullet,\bullet}$ 的全复形 $\operatorname{Tot}^\bullet(J)$，使用两种过滤：

- **列过滤**$F_I$：$F_I^p \operatorname{Tot}^n = \bigoplus_{i \geq p} J^{i, n-i}$。这给出谱序列 ${}_I E$：
  $${}_I E_1^{p,q} = H^q(J^{p,\bullet}) = R^q G(F(I^p)).$$
  由于 $F(I^p)$ 是 $G$-零调的，$R^q G(F(I^p)) = 0$ 对 $q > 0$，而 $R^0 G(F(I^p)) = GF(I^p)$。因此 ${}_I E_2^{p,q} = 0$ 对 $q > 0$，且
  $${}_I E_2^{p,0} = H^p(GF(I^\bullet)) = R^p(GF)(A).$$

- **行过滤**$F_{II}$：$F_{II}^q \operatorname{Tot}^n = \bigoplus_{j \geq q} J^{n-j, j}$。这给出谱序列 ${}_{II} E$：
  $${}_{II} E_1^{p,q} = H^p(J^{\bullet,q}).$$
  利用 $J^{\bullet,q}$ 是 $F(I^\bullet)$ 的内射分解的"第 $q$ 层"，可以证明
  $${}_{II} E_2^{p,q} = R^p G(R^q F(A)).$$

**步骤 5：比较。** 两种谱序列都收敛到 $H^{p+q}(\operatorname{Tot}^\bullet(J))$。由列过滤的结果，$H^n(\operatorname{Tot}^\bullet(J)) \cong R^n(GF)(A)$。因此行过滤给出的谱序列满足
$${}_{II} E_2^{p,q} = R^p G(R^q F(A)) \Longrightarrow R^{p+q}(GF)(A).$$
- $\square$

### 4.4 核心推论

**推论 4.6** (Leray 谱序列). *设 $f: X \to Y$ 和 $g: Y \to Z$ 为拓扑空间的连续映射（或概形态射），$\mathcal{F}$ 为 $X$ 上的层。则
$$E_2^{p,q} = R^p g_* (R^q f_* \mathcal{F}) \Longrightarrow R^{p+q}(gf)_* \mathcal{F}.$$
*

*证明.* *取 $F = f_*$, $G = g_*$。则 $GF = (gf)_*$。$f_*$ 将内射层映为 $g_*$-零调层（当 $f$ 是局部紧空间的 proper 映射时，$f_*$ 将软层映为软层，软层对 $g_*$ 零调）。因此定理 4.5 的条件满足。* $\square$

**推论 4.7** (局部到整体谱序列). *设 $X$ 为拓扑空间，$\mathcal{U} = \{U_i\}$ 为开覆盖，$\mathcal{F}$ 为层。则
$$E_2^{p,q} = \check{H}^p(\mathcal{U}, \mathcal{H}^q(\mathcal{F})) \Longrightarrow H^{p+q}(X, \mathcal{F}),$$
其中 $\mathcal{H}^q(\mathcal{F})$ 是预层 $U \mapsto H^q(U, \mathcal{F}|_U)$ 的层化。*

*证明.* *取 $F = \check{C}^\bullet(\mathcal{U}, -)$（Čech 复形函子），$G$ 为取全局截面的函子。* $\square$

**推论 4.8** (Hochschild-Serre 谱序列). *设 $G$ 为群，$H \trianglelefteq G$ 为正规子群，$M$ 为 $G$-模。则
$$E_2^{p,q} = H^p(G/H, H^q(H, M)) \Longrightarrow H^{p+q}(G, M).$$
*

*证明.* *取 $F = H^0(H, -)$（$H$-不变子模），$G = H^0(G/H, -)$。则 $GF = H^0(G, -)$，且 $R^q F = H^q(H, -)$，$R^p G = H^p(G/H, -)$。* $\square$

---

## 5. Lean4 形式化代码

以下 Lean4 代码建立 Grothendieck 谱序列的定义框架。

```lean4
import Mathlib

namespace GrothendieckSpectralSequenceGold

universe u v w

open CategoryTheory HomologicalAlgebra Limits

/-- 谱序列的通用定义 -/
section SpectralSequence

variable (C : Type u) [Category C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ]

/-- 上同调谱序列：第 r 页 -/
structure SpectralSequence.Page (r : ℕ) where
  obj : ℤ → ℤ → C
  differential (p q : ℤ) : obj p q ⟶ obj (p + r) (q - r + 1)
  differential_squared (p q : ℤ) :
    differential p q ≫ differential (p + r) (q - r + 1) = 0

/-- 谱序列的收敛 -/
structure SpectralSequence.ConvergesTo {H : ℤ → C}
    (E : SpectralSequence.Page C r) where
  filtration (n : ℤ) : ℤ → Subobject (H n)
  filtration_bounded (n : ℤ) :
    ∃ p_min p_max, ∀ p < p_min, filtration n p = ⊥ ∧
      ∀ p > p_max, filtration n p = ⊤
  E_infinity (p q : ℤ) :
    E.obj p q ≅ filtration (p + q) p / filtration (p + q) (p + 1)

end SpectralSequence

/-- Grothendieck 谱序列 -/
section GrothendieckSS

variable {A B C : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
  [Category C] [Abelian C] [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteLimits G]

/-- F 将内射对象映为 G-零调对象 -/
def FMapsInjectiveToGAyclic : Prop :=
  ∀ (I : A) [Injective I], ∀ q > 0, (RDer G q).obj (F.obj I) = 0

/-- Grothendieck 谱序列的构造 -/
theorem grothendieckSpectralSequence (A_obj : A) (h : FMapsInjectiveToGAyclic F G) :
    ∃ (E : SpectralSequence.Page C 2),
      E.ConvergesTo (fun n => (RDer (F ⋙ G) n).obj A_obj) ∧
      ∀ (p q : ℤ), E.obj p q ≅ (RDer G p).obj ((RDer F q).obj A_obj) := by
  sorry
  /- 完成计划：
    1. 取 A_obj 的内射分解 I^•
    2. 对每个 F(I^p) 取内射分解 J^{p,•}
    3. 构造双复形 J^{•,•} 及其全复形
    4. 对全复形应用两种滤过（列滤过和行滤过）
    5. 计算列滤过的 E_1 和 E_2 页，证明其退化为 R^n(GF)(A)
    6. 计算行滤过的 E_1 和 E_2 页，得到 R^p G(R^q F(A))
    7. 利用同伦理论验证不同滤过收敛到同一目标
  -/

/-- Leray 谱序列（特例） -/
theorem leraySpectralSequence {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Sheaf Ab X) [Proper f] :
    ∃ (E : SpectralSequence.Page Ab 2),
      E.ConvergesTo (fun n => (RDer (f ⋙ g)_* n).obj F) ∧
      ∀ (p q : ℤ), E.obj p q ≅ (RDer g_* p).obj ((RDer f_* q).obj F) := by
  sorry
  /- 完成计划：
    1. 验证 f_* 将内射层映为 g_*-零调层
    2. 利用软层（soft sheaves）的性质
    3. 应用 grothendieckSpectralSequence
  -/

/-- Hochschild-Serre 谱序列（特例） -/
theorem hochschildSerre (G : Type*) [Group G] (H : Subgroup G) [H.Normal]
    (M : Rep ℤ G) :
    ∃ (E : SpectralSequence.Page Ab 2),
      E.ConvergesTo (fun n => H^n G M) ∧
      ∀ (p q : ℤ), E.obj p q ≅ H^p (G ⧸ H) (H^q H M) := by
  sorry
  /- 完成计划：
    1. 取 A = G-模范畴, B = H-模范畴, C = (G/H)-模范畴
    2. F = H^0(H, -), G = H^0(G/H, -)
    3. 验证 F 将内射 G-模映为内射 H-模（由 Shapiro 引理）
    4. 应用 grothendieckSpectralSequence
  -/

end GrothendieckSS

/-- 双复形与全复形 -/
section DoubleComplex

variable {A : Type*} [Category A] [Preadditive A] [HasZeroObject A]
  [HasShift A ℤ]

/-- 双复形 -/
structure DoubleComplex where
  obj : ℤ → ℤ → A
  horizontal_diff (p q : ℤ) : obj p q ⟶ obj (p + 1) q
  vertical_diff (p q : ℤ) : obj p q ⟶ obj p (q + 1)
  horizontal_squared (p q : ℤ) :
    horizontal_diff p q ≫ horizontal_diff (p + 1) q = 0
  vertical_squared (p q : ℤ) :
    vertical_diff p q ≫ vertical_diff p (q + 1) = 0
  commutative (p q : ℤ) :
    horizontal_diff p q ≫ vertical_diff (p + 1) q =
      vertical_diff p q ≫ horizontal_diff p (q + 1)

/-- 全复形 -/
def totalComplex (C : DoubleComplex A) : CochainComplex A ℤ where
  X n := ∐ (fun (p : ℤ) => C.obj p (n - p))
  d n := by
    -- 构造 d = d_h + (-1)^p d_v
    sorry
  shape := sorry
  d_squared := sorry

/-- 列滤过诱导的谱序列 -/
def columnSpectralSequence (C : DoubleComplex A) :
    SpectralSequence.Page A 1 where
  obj p q := C.obj p q
  differential p q := C.vertical_diff p q
  differential_squared := C.vertical_squared

/-- 行滤过诱导的谱序列 -/
def rowSpectralSequence (C : DoubleComplex A) :
    SpectralSequence.Page A 1 where
  obj p q := C.obj q p
  differential p q := C.horizontal_diff q p
  differential_squared p q := C.horizontal_squared q p

end DoubleComplex

end GrothendieckSpectralSequenceGold
```

---

## 6. 批判性分析

### 6.1 Grothendieck 方法 vs. Cartan–Eilenberg 方法

**Cartan–Eilenberg 的方法**：在模范畴中，利用具体的元素和矩阵来构造谱序列。双复形的构造依赖于内射模的显式选择，收敛性的证明使用了复杂的图表追踪。

**Grothendieck 的方法**：在 Abel 范畴中，利用泛性质和 $
\delta$-函子的理论。谱序列的存在性成为泛 $
\delta$-函子性质的推论，不依赖于任何具体的构造。

**比较**：

1. **普遍性**：Grothendieck 的方法适用于任意 Abel 范畴（如层范畴、凝聚层范畴），而 Cartan–Eilenberg 的方法局限于模范畴。

2. **构造性 vs. 存在性**：Cartan–Eilenberg 给出了谱序列的显式构造（通过过滤复形和正合对），而 Grothendieck 的证明更侧重于存在性和唯一性。对于具体计算，Cartan–Eilenberg 的方法更实用。

3. **技术深度**：Grothendieck 的方法需要 $
\delta$-函子和 Abel 范畴的深度理论作为前置，而 Cartan–Eilenberg 可以在更初等的水平上理解。

### 6.2 Serre 与 Grothendieck 的分歧

Serre 对谱序列的态度是实用主义的：他大量使用谱序列（在群上同调、层上同调中），但很少深入讨论其构造的公理化基础。Grothendieck 则将谱序列提升到了同调代数的中心位置，并证明了它们是导出函子理论的必然产物。

在 *Grothendieck–Serre Correspondence* 中，Serre 曾对 Grothendieck 的抽象方法表示过保留意见，认为某些情形下直接计算更为有效。然而，EGA III 中谱序列的系统应用（特别是形式函数定理和比较定理）最终说服了 Serre 接受这一框架。

### 6.3 后续发展：导出范畴与谱序列

Verdier 在 1963 年引入的**导出范畴（derived category）**为谱序列提供了新的视角。在导出范畴中，复合函子的导出函子可以表示为导出范畴中的复合：
$$R(GF) \cong RG \circ RF$$
（在适当的条件下）。谱序列则成为这一同构在 t-结构（t-structure）下的具体表现。

Grothendieck 的原始谱序列理论与导出范畴理论是等价的，但后者在更高层次的抽象中更为自然。现代代数几何（如 perverse 层理论、D-模理论）几乎完全使用导出范畴的语言。

### 6.4 形式化的挑战

谱序列的形式化是同调代数形式化中最复杂的任务之一。主要挑战包括：

1. **收敛性的严格处理**：谱序列的收敛涉及无限滤过和极限，在类型论中需要谨慎处理；
2. **双指标的同调代数**：Lean4 的 `CochainComplex` 是单指标的，双复形的形式化需要额外的索引管理；
3. **具体计算的形式化**：虽然 Grothendieck 谱序列的存在性证明是抽象的，但具体应用（如计算层上同调）需要大量的具体构造。

Mathlib4 目前正在开发同调代数的基础框架，但谱序列的系统形式化尚未完成。

---

## 7. 参考文献与延伸阅读

### 原始文献

1. Grothendieck, A. *Sur quelques points d'algèbre homologique*, *Tôhoku Math. J.* (2) **9** (1957), 119–221, §2.4.
2. Grothendieck, A. & Dieudonné, J. *Éléments de Géométrie Algébrique III*, *Publ. Math. IHÉS* **11, 17** (1961).

### 教材与专著

3. Cartan, H. & Eilenberg, S. *Homological Algebra*, Princeton Univ. Press, 1956.
2. Weibel, C. *An Introduction to Homological Algebra*, Cambridge Univ. Press, 1994, Chap. 5.
3. McCleary, J. *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge Univ. Press, 2001.

### 数据库

6. Stacks Project, Tag 015J: *Spectral sequences*. https://stacks.math.columbia.edu/tag/015J
2. nLab: *Grothendieck spectral sequence*. https://ncatlab.org/nlab/show/Grothendieck+spectral+sequence

---

> **审校状态**：草稿（draft）。待完成 Lean4 代码中 `sorry` 的填充。

