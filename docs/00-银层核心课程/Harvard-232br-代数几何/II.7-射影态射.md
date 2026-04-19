---
course: Harvard 232br 代数几何
level: silver

title: Harvard 232br - Hartshorne Chapter II §7 习题解答
msc_primary: 00A99
course_code: Harvard Math 232br
textbook: Robin Hartshorne, Algebraic Geometry (GTM 52)
source_textbook: Robin Hartshorne, Algebraic Geometry (GTM 52)
source_chapter: Chapter II - Schemes, Section 7 - Projective Morphisms
source_exercise:
- II.7.1
- II.7.2
- II.7.3
- II.7.4
- II.7.5
- II.7.6
- II.7.7
difficulty: ⭐⭐⭐ to ⭐⭐⭐⭐⭐
processed_at: '2026-04-17'
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
    - 'Chapter II, Section 7: Projective Morphisms'
    url: null
    pages: 150-158
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
    url: https://math.stanford.edu/~vakil/216blog/
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
target_courses: [FormalMath银层核心课程, 代数几何]
status: completed
created_at: 2026-04-18
---

# Harvard 232br - Hartshorne Chapter II §7 习题解答

> 本节覆盖射影态射的判别、分次环的整截面、射影空间自同构、以及 Veronese 嵌入与 Segre 嵌入的性质。

---

## 习题 II.7.1 — 射影态射的丛判别

### 题号与精确引用

**Hartshorne II.7.1**

### 问题重述

设 $f : X \to Y$ 为概形态射。证明：$f$ 是射影态射当且仅当存在 $Y$ 上的凝聚层 $\mathcal{E}$，使得 $X$ 作为 $Y$-概形同构于某个 $\mathbb{P}(\mathcal{E})$ 的闭子概形。

### 详细解答

**$\Rightarrow$**：设 $f$ 是射影的，则由定义存在闭浸入 $i : X \hookrightarrow \mathbb{P}^n_Y$ 对某个 $n$。取 $\mathcal{E} = \mathcal{O}_Y^{\oplus(n+1)}$，则 $\mathbb{P}(\mathcal{E}) = \mathbb{P}^n_Y$。于是 $X$ 是 $\mathbb{P}(\mathcal{E})$ 的闭子概形。

**$\Leftarrow$**：设 $X \hookrightarrow \mathbb{P}(\mathcal{E})$ 为闭浸入，其中 $\mathcal{E}$ 为凝聚层。因 $\mathbb{P}(\mathcal{E})$ 在 $Y$ 上射影（由构造），而闭浸入的复合仍是射影的，故 $f$ 射影。∎

### 关键概念提示

- 这是射影态射的 **相对化刻画**：射影态射恰是“某个相对射影丛的闭子概形”。
- 与 EGA 的定义等价：EGA 将射影态射定义为 $\mathbb{P}(\mathcal{E})$ 的闭子概形，而 Hartshorne 先定义 $\mathbb{P}^n$ 的闭子概形，再相对化。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 认为 $\mathcal{E}$ 必须是自由的 | $\mathcal{E}$ 可以是任意凝聚层；当 $Y$ 仿射时，任何射影态射都可嵌入某个 $\mathbb{P}^n_Y$，此时 $\mathcal{E}$ 自由。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme

open AlgebraicGeometry

-- 射影态射等价于某个 P(E) 的闭子概形
theorem projective_iff_projectiveBundleClosedImmersion
    {X Y : Scheme} (f : X ⟶ Y) :
    IsProjective f ↔
    ∃ (ℰ : CoherentSheaf Y) (i : ClosedImmersion X (ProjectiveBundle ℰ.val)),
      i.toSchemeHom ≫ (ProjectiveBundle ℰ.val).structureHom = f :=
  sorry
```

---

## 习题 II.7.2 — 射影空间的分次截面环

### 题号与精确引用

**Hartshorne II.7.2**

### 问题重述

设 $X = \mathbb{P}^n_A$，$A$ 为 Noetherian 环。证明
$$\Gamma_*(X, \mathcal{O}_X) := \bigoplus_{d \in \mathbb{Z}} H^0(X, \mathcal{O}_X(d)) \cong A[x_0, \dots, x_n].$$

### 详细解答

由标准覆盖 $\{D_+(x_i)\}$ 及 Čech 计算，$H^0(\mathbb{P}^n_A, \mathcal{O}(d))$ 同构于 $A[x_0, \dots, x_n]$ 中次数为 $d$ 的齐次多项式组成的部分。

具体验证：在仿射开集 $D_+(x_i) = \operatorname{Spec} A[x_0/x_i, \dots, x_n/x_i]$ 上，$\mathcal{O}(d)$ 对应于分式环中次数为 $d$ 的元。整体截面 $H^0(X, \mathcal{O}(d))$ 由在所有 $D_+(x_i)$ 上都有定义且相容的截面组成。对 $d \ge 0$，这恰是 $A[x_0, \dots, x_n]_d$；对 $d < 0$，不存在非零整体截面（因负次分式在至少一个坐标卡上无定义）。

因此分次环的直和同构于多项式环 $A[x_0, \dots, x_n]$。∎

### 关键概念提示

- 这是 **分次环的 Proj 构造** 的逆过程：$\operatorname{Proj} S$ 的扭结构层 $\mathcal{O}(d)$ 的整体截面回到 $S_d$（在 $S = A[x_0, \dots, x_n]$ 时精确成立）。
- 对一般分次环 $S$，$\Gamma_*(\operatorname{Proj} S, \mathcal{O})$ 可能与 $S$ 不同（见 II.5.13）。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 忽略 $d < 0$ 时 $H^0 = 0$ | 负次扭层的整体截面确实为零，这是 $\mathbb{P}^n$ 的重要性质。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.Cohomology

open AlgebraicGeometry

-- P^n_A 的分次截面环同构于多项式环
theorem gradedRing_of_projectiveSpace (n : ℕ) [n.AtLeastTwo]
    (A : Type*) [CommRing A] [IsNoetherian A] :
    GradedSectionRing (ProjectiveScheme (Fin (n + 1)) A) ≅
    MvPolynomial (Fin (n + 1)) A :=
  sorry
```

---

## 习题 II.7.3 — Proj 与分次环的泛性质

### 题号与精确引用

**Hartshorne II.7.3**

### 问题重述

设 $S$ 为分次环，$S_1$ 作为 $S_0$-代数生成 $S$。设 $X = \operatorname{Proj} S$，$\mathcal{L}$ 为概形 $Y$ 上的可逆层。证明：给出 $Y$-态射 $f : Y \to X$ 等价于给出一个分次环同态 $\phi : S \to \Gamma_*(Y, \mathcal{L})$（模去适当的等价关系），使得 $\mathcal{L}$ 对应 $f^*\mathcal{O}_X(1)$。

### 详细解答

**从态射到分次环同态**：给定 $f : Y \to X$，拉回 $f^*\mathcal{O}_X(1) \cong \mathcal{L}$。对 $d \ge 0$，$f$ 诱导
$$S_d = H^0(X, \mathcal{O}_X(d)) \longrightarrow H^0(Y, f^*\mathcal{O}_X(d)) \cong H^0(Y, \mathcal{L}^{\otimes d}).$$
这些映射的直和给出分次环同态 $\phi : S \to \Gamma_*(Y, \mathcal{L})$。

**从分次环同态到态射**：给定分次环同态 $\phi : S \to \Gamma_*(Y, \mathcal{L})$，设 $s_0, \dots, s_n \in S_1$ 生成 $S$ 作为 $S_0$-代数。则 $\phi(s_i) \in H^0(Y, \mathcal{L})$。因 $S_1$ 生成 $S$，$\{\phi(s_i)\}$ 生成 $\mathcal{L}$（*待验证*：需假设 $\phi$ 满足某种满射条件，即截面生成 $\mathcal{L}$）。于是由 II.7.1 的构造，这些截面给出态射 $f : Y \to \mathbb{P}^n_{S_0}$，其像落在 $X = \operatorname{Proj} S$ 中。

验证这两个构造互为逆（模去以 $\mathcal{L}$ 的标量乘法给出的等价关系），即得所需等价。∎

### 关键概念提示

- 这是 **Proj 的泛性质**：$\operatorname{Proj}$ 是“由可逆层与整体截面生成的分次环”所表示的函子。
- 该结果是构造射影态射、研究线性系与映射到射影空间关系的基础。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 未要求 $S_1$ 生成 $S$ | 若 $S_1$ 不生成 $S$，则 $\operatorname{Proj} S$ 可能无法被 $S_1$ 的截面嵌入射影空间，泛性质的陈述需调整。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme

open AlgebraicGeometry

-- Proj 的泛性质
def projUniversalProperty {S : Type*} [CommRing S] [GradedRing (fun n => S)]
    (Y : Scheme) (ℒ : LineBundle Y)
    (hgen : Subalgebra.adjoin ℤ (SetLike.grade 1) = ⊤) :
    (Y ⟶ Proj S) ≃
    { φ : S →+* GradedSectionRing Y // φ.homogeneous ∧ φ.degree_one_surjective } :=
  sorry
```

---

## 习题 II.7.4 — 到射影空间的态射与可逆层

### 题号与精确引用

**Hartshorne II.7.4**

### 问题重述

设 $X$ 为域 $k$ 上的概形。证明：给出 $k$-态射 $f : X \to \mathbb{P}^n_k$ 等价于给出 $X$ 上的可逆层 $\mathcal{L}$ 及生成 $\mathcal{L}$ 的整体截面 $s_0, \dots, s_n \in H^0(X, \mathcal{L})$（模去 $(\mathcal{L}, s_i) \sim (\mathcal{L} \otimes \mathcal{M}, s_i \otimes u)$ 的等价关系，其中 $\mathcal{M}$ 为平凡线丛，$u$ 为整体可逆截面）。

### 详细解答

**从态射到数据**：给定 $f : X \to \mathbb{P}^n_k$，取 $\mathcal{L} = f^*\mathcal{O}_{\mathbb{P}^n}(1)$，$s_i = f^*x_i \in H^0(X, \mathcal{L})$，其中 $x_i$ 为 $\mathbb{P}^n$ 的齐次坐标。由构造，$\{s_i\}$ 生成 $\mathcal{L}$。

**从数据到态射**：给定 $(\mathcal{L}, s_0, \dots, s_n)$ 且 $\{s_i\}$ 生成 $\mathcal{L}$。对每点 $x \in X$，存在某个 $s_i(x) \neq 0$（在茎的意义下）。定义
$$f(x) = [s_0(x) : \dots : s_n(x)] \in \mathbb{P}^n(k(x)).$$
因 $s_i$ 生成 $\mathcal{L}$，这是良定义的。由局部平凡化，$f$ 是态射。具体地，在 $U_i = \{x \mid s_i(x) \neq 0\}$ 上，$f$ 对应于环同态
$$k[x_0/x_i, \dots, x_n/x_i] \longrightarrow \mathcal{O}_X(U_i), \quad x_j/x_i \mapsto s_j/s_i,$$
后者是良定义的因 $s_i$ 在 $U_i$ 上可逆。

验证等价关系：$(\mathcal{L}, s_i) \sim (\mathcal{L}, \lambda s_i)$（$\lambda \in \mathcal{O}_X(X)^*$）给出相同的射影坐标，故等价关系正确。∎

### 关键概念提示

- 这是 **线性系与射影嵌入** 的核心定理：到 $\mathbb{P}^n$ 的映射由“可逆层 + 生成截面”完全分类。
- 该结果是构造典范映射、研究射影正规性、证明 Chow 引理等的出发点。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 未要求截面生成 $\mathcal{L}$ | 若截面不生成，则某些点可能没有良定义的射影坐标，态射无法构造。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme

open AlgebraicGeometry

-- 到 P^n 的态射等价于 (ℒ, s_0, ..., s_n)
def morphismsToProjectiveSpace {X : Scheme} {k : Type*} [Field k]
    [Algebra k (X.presheaf.obj ⊤)] :
    (X ⟶ ProjectiveScheme (Fin (n + 1)) k) ≃
    { p : Σ ℒ : LineBundle X, Fin (n + 1) → H^0(X, ℒ) |
      p.2.generates_p.1 } :=
  sorry
```

---

## 习题 II.7.5 — 射影空间的自同构

### 题号与精确引用

**Hartshorne II.7.5**

### 问题重述

设 $k$ 为域。证明：$\mathbb{P}^n_k$ 的 $k$-自同构群 $\operatorname{Aut}_k(\mathbb{P}^n)$ 同构于 $\operatorname{PGL}_{n+1}(k)$。

### 详细解答

由 II.7.4，$\mathbb{P}^n$ 的自同构对应于 $(\mathcal{O}(1), s_0, \dots, s_n)$，其中 $s_i$ 生成 $\mathcal{O}(1)$。因 $\operatorname{Pic}(\mathbb{P}^n) \cong \mathbb{Z}$ 且 $\mathcal{O}(1)$ 是生成元，任何自同构 $f$ 满足 $f^*\mathcal{O}(1) \cong \mathcal{O}(1)$（或 $\mathcal{O}(-1)$；但 $f^*$ 保持有效除子，故只能是 $\mathcal{O}(1)$）。

因此 $f$ 由 $H^0(\mathbb{P}^n, \mathcal{O}(1)) \cong k^{n+1}$ 的基变换决定，即由某个 $A \in \operatorname{GL}_{n+1}(k)$ 给出坐标变换
$$[x_0 : \dots : x_n] \mapsto [\sum a_{0j}x_j : \dots : \sum a_{nj}x_j].$$
两个矩阵给出相同自同构当且仅当它们相差标量矩阵 $\lambda I$，故
$$\operatorname{Aut}_k(\mathbb{P}^n) \cong \operatorname{GL}_{n+1}(k) / k^* \cdot I = \operatorname{PGL}_{n+1}(k).$$

*待验证*：严格来说，需先证明 $f^*\mathcal{O}(1) \cong \mathcal{O}(1)$。这可通过比较次数或利用 Picard 群的结构完成。∎

### 关键概念提示

- $\operatorname{PGL}_{n+1}(k)$ 是射影几何的 **基本变换群**，任何两个一般位置的超平面配置都可由其元素相互转化。
- 对 $n = 1$，这就是 Möbius 变换群。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 直接用坐标变换定义自同构 | 需先证明任何自同构必拉回 $\mathcal{O}(1)$ 到自身，才能断言它由线性变换诱导。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.LinearAlgebra.Projectivization

open AlgebraicGeometry

-- P^n 的自同构群同构于 PGL_{n+1}(k)
theorem automorphism_of_projectiveSpace (n : ℕ) [n.AtLeastTwo] (k : Type*) [Field k] :
    Aut (ProjectiveScheme (Fin (n + 1)) k) ≅
    PGL (Fin (n + 1)) k :=
  sorry
```

---

## 习题 II.7.6 — 射影空间在 $\operatorname{Spec} \mathbb{Z}$ 上的 Proper 性

### 题号与精确引用

**Hartshorne II.7.6**

### 问题重述

证明 $\mathbb{P}^n_{\mathbb{Z}}$ 在 $\operatorname{Spec} \mathbb{Z}$ 上是 proper 的。

### 详细解答

**步骤 1：局部性质**。properness 是局部在底空间上的性质。对任意仿射开集 $\operatorname{Spec} A \subseteq \operatorname{Spec} \mathbb{Z}$，需证 $\mathbb{P}^n_A = \mathbb{P}^n_{\mathbb{Z}} \times_{\operatorname{Spec} \mathbb{Z}} \operatorname{Spec} A$ 在 $\operatorname{Spec} A$ 上 proper。

**步骤 2：仿射基上的 properness**。由标准结果（Hartshorne II.4.9 或 EGA），$\mathbb{P}^n_A$ 在 $\operatorname{Spec} A$ 上是 projective 的：它是由分次环 $A[x_0, \dots, x_n]$ 的 Proj 构造给出的，而 Proj 构造天然给出闭浸入到某个 $\mathbb{P}^N_A$（此处 $N$ 恰为 $n$，即标准嵌入）。

**步骤 3：projective 推出 proper**。因 projective 态射是 proper 的（Hartshorne II.4.9：射影态射是真态射），故 $\mathbb{P}^n_A \to \operatorname{Spec} A$ 是 separated、of finite type 且 universally closed。

因 $\operatorname{Spec} \mathbb{Z}$ 可由 $\operatorname{Spec} \mathbb{Z}$ 本身覆盖，以上已足够。∎

### 关键概念提示

- $\mathbb{P}^n_{\mathbb{Z}}$ 是 **算术几何** 中的基本对象：它是所有 $\mathbb{P}^n_{\mathbb{F}_p}$ 和 $\mathbb{P}^n_{\mathbb{Q}}$ 的“统一族”。
- properness 在 $\operatorname{Spec} \mathbb{Z}$ 上尤其重要，因为它保证了算术紧性（arithmetic compactness）。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 试图直接验证赋值判别法 | 对 $\mathbb{P}^n$ 直接验证赋值判别法虽然可行，但远不如利用“projective 必 proper”的标准结论简洁。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme

open AlgebraicGeometry

-- P^n_Z 在 Spec Z 上 proper
theorem projectiveSpace_over_Z_isProper (n : ℕ) [n.AtLeastTwo] :
    IsProper (ProjectiveScheme (Fin (n + 1)) ℤ).structureHom :=
  sorry
```

---

## 习题 II.7.7 — Veronese 嵌入是闭浸入

### 题号与精确引用

**Hartshorne II.7.7**

### 问题重述

设 $k$ 为代数闭域。考虑 $d$-uple 嵌入 $v_d : \mathbb{P}^n_k \hookrightarrow \mathbb{P}^N_k$，其中 $N = \binom{n+d}{d} - 1$。
(a) 证明 $v_d$ 是闭浸入。
(b) 证明 $v_d(\mathbb{P}^n)$ 的理想由所有二次 Veronese 关系生成（当 $d \ge 2$ 时）。

### 详细解答

**(a) $v_d$ 是闭浸入**

$v_d$ 由完全线性系 $|\mathcal{O}(d)|$ 给出。取 $M_0, \dots, M_N$ 为 $x_0, \dots, x_n$ 的所有次数为 $d$ 的单项式。则 $v_d$ 将点 $P = [a_0 : \dots : a_n]$ 映为 $[M_0(P) : \dots : M_N(P)]$。

要证 $v_d$ 是闭浸入，需证：

1. $v_d$ 是拓扑闭嵌入；
2. $v_d^\# : \mathcal{O}_{\mathbb{P}^N} \to (v_d)_*\mathcal{O}_{\mathbb{P}^n}$ 是满射。

拓扑层面：因 $\mathbb{P}^n$ 是 proper 的而 $\mathbb{P}^N$ 是 separated 的，$v_d$ 的像是闭的。且 $v_d$ 是单射（不同的射影点给出不同的单项式取值比例，可由适当的 $d$ 次齐次多项式区分）。

层论层面：在每个标准仿射开集 $D_+(x_i)$ 上，$v_d$ 对应环同态
$$k[y_0, \dots, y_N]/I \longrightarrow k[x_0/x_i, \dots, x_n/x_i],$$
其中 $y_j \mapsto M_j/x_i^d$。该映射的像生成整个坐标环（因为 $x_j/x_i$ 可表为适当的 $M_j/x_i^d$ 之比），故为满射。∎

**(b) 理想的生成元**

$v_d(\mathbb{P}^n)$ 的点满足：若 $y_\alpha, y_\beta, y_\gamma, y_\delta$ 对应单项式 $M_\alpha, M_\beta, M_\gamma, M_\delta$ 且 $M_\alpha M_\beta = M_\gamma M_\delta$，则 $y_\alpha y_\beta = y_\gamma y_\delta$。这些二次关系生成整个齐次理想。证明思路：

- 设 $S = k[x_0, \dots, x_n]$，$T = k[y_0, \dots, y_N]$。Veronese 子环 $S^{(d)} = \bigoplus_m S_{md}$ 同构于 $T/I$。
- $S^{(d)}$ 是 $T$ 在 Veronese 映射下的像，其核 $I$ 由所有 $y_\alpha y_\beta - y_\gamma y_\delta$ 生成。
- 由交换代数，Veronese 子代数是由二次关系定义的。∎

### 关键概念提示

- Veronese 嵌入将低次几何对象（如 $\mathbb{P}^n$ 中的超曲面）转化为高次嵌入空间中的超平面截影，是研究射影不变量的基本工具。
- 该嵌入的像称为 **Veronese variety**，是 toric variety 和 Grassmannian 的重要特例。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 混淆 Veronese 与 Segre 嵌入 | Veronese 是 $v_d : \mathbb{P}^n \to \mathbb{P}^N$（单个空间的 $d$-次嵌入），Segre 是 $s : \mathbb{P}^n \times \mathbb{P}^m \to \mathbb{P}^{nm+n+m}$（乘积到射影空间的嵌入）。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme

open AlgebraicGeometry

-- d-uple 嵌入是闭浸入，且像理想由二次关系生成
theorem veronese_isClosedImmersion (n d : ℕ) [n.AtLeastTwo] (hd : 2 ≤ d)
    (k : Type*) [Field k] [IsAlgClosed k] :
    ∃ (vd : ClosedImmersion
      (ProjectiveScheme (Fin (n + 1)) k)
      (ProjectiveScheme (Fin (Nat.choose (n + d) d)) k)),
      IsVeroneseEmbedding vd ∧
      ∀ I : HomogeneousIdeal _,
        vd.toSchemeHom.range = ZeroLocus I →
        I = Ideal.span (veroneseRelations n d k) :=
  sorry
```

---

**文档位置**: `docs/13-代数几何/Harvard-232br-习题解答/II.7-射影态射.md`
**创建日期**: 2026-04-17


## 习题

**习题 1.1**。证明：闭浸入是射影态射。

*解答*：闭浸入 $Z \\hookrightarrow X$ 可看作由 $\\mathcal{O}_X$ 的某个理想层 $\\mathcal{I}$ 确定的相对Proj，即 $Z \\cong \\operatorname{Proj} \\bigoplus \\mathcal{I}^n / \\mathcal{I}^{n+1}$。$\square$

---

**习题 1.2**。说明为什么 $\\mathbb{A}^1 \\to \\operatorname{Spec} k$ 不是射影态射。

*解答*：射影态射要求存在到某个 $\\mathbb{P}^n$ 的闭浸入分解。$\\mathbb{A}^1$ 不是紧的（在经典拓扑下），而射影态射的纤维是紧的（proper），故 $\\mathbb{A}^1 \\to \\operatorname{Spec} k$ 不是射影的。$\square$
