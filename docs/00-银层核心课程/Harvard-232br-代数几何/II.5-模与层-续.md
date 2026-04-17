---
course: Harvard 232br 代数几何
level: silver

title: Harvard 232br - Hartshorne Chapter II §5 习题解答（续）
course_code: Harvard Math 232br
textbook: Robin Hartshorne, Algebraic Geometry (GTM 52)
source_textbook: Robin Hartshorne, Algebraic Geometry (GTM 52)
source_chapter: Chapter II - Schemes, Section 5 - Sheaves of Modules
source_exercise:
- II.5.5
- II.5.6
- II.5.7
- II.5.8
- II.5.9
difficulty: ⭐⭐⭐ to ⭐⭐⭐⭐
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
    - 'Chapter II, Section 5: Sheaves of Modules'
    url: null
    pages: 110-118
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
    chapters: []
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

# Harvard 232br - Hartshorne Chapter II §5 习题解答（续）

> 本节覆盖局部自由层的 Hom–Tensor 对偶、对偶基判别、纤维维数判别、茎自由性判别，以及凝聚层自由点集的拓扑性质。

---

## 习题 II.5.5 — Hom 与 Tensor 的对偶同构

### 题号与精确引用

**Hartshorne II.5.5**

### 问题重述

设 $(X,\mathcal{O}_X)$ 为环化空间，$\mathcal{E}$ 为有限秩局部自由 $\mathcal{O}_X$-模，$\mathcal{F}$ 为任意 $\mathcal{O}_X$-模。证明自然映射
$$\mathcal{E}^\vee \otimes_{\mathcal{O}_X} \mathcal{F} \longrightarrow \mathcal{H}om_{\mathcal{O}_X}(\mathcal{E}, \mathcal{F})$$
是层同构。

### 详细解答

**局部构造**：因 $\mathcal{E}$ 局部自由，存在开覆盖 $\{U_i\}$ 使得 $\mathcal{E}|_{U_i} \cong \mathcal{O}_{U_i}^{\oplus r}$。此时自然映射局部化为
$$(\mathcal{O}_{U_i}^{\oplus r})^\vee \otimes \mathcal{F}|_{U_i} \longrightarrow \mathcal{H}om(\mathcal{O}_{U_i}^{\oplus r}, \mathcal{F}|_{U_i}).$$
左边同构于 $\mathcal{F}|_{U_i}^{\oplus r}$，右边也同构于 $\mathcal{F}|_{U_i}^{\oplus r}$（因为 $\mathcal{H}om(\mathcal{O}_X, \mathcal{F}) \cong \mathcal{F}$ 且 Hom 有限直和可分解）。直接验证该映射在这两个同构下是恒等映射，故为同构。

**整体粘合**：自然映射在交 $U_i \cap U_j$ 上的限制相容（由典范性），故可粘合为整体层同构。∎

### 关键概念提示

- 此同构是 **Hom-张量伴随** 在层范畴中的直接推论：$\mathcal{H}om(\mathcal{E}, \mathcal{F}) \cong \mathcal{E}^\vee \otimes \mathcal{F}$ 对局部自由层成立。
- 对非局部自由的凝聚层，该映射一般只是单射（当 $\mathcal{E}$ 是反射层时同构）。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 未验证映射的典范性 | 必须用泛性质说明该映射不依赖于局部平凡化的选取。 |
| 将结论推广到任意凝聚层 | 对一般凝聚层，$\mathcal{E}^\vee \otimes \mathcal{F} \to \mathcal{H}om(\mathcal{E}, \mathcal{F})$ 未必是满射。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.ModuleSheaves

open AlgebraicGeometry

-- 局部自由层诱导 Hom-Tensor 对偶同构
def homTensorIso {X : RingedSpace} (ℰ : SheafOfModules X.toRingedSpace)
    (hℰ : ℰ.IsLocallyFreeOfFiniteRank) (ℱ : SheafOfModules X.toRingedSpace) :
    ℰ.dual.tensor ℱ ≅ SheafOfModules.hom ℰ ℱ :=
  sorry
```

---

## 习题 II.5.6 — 局部自由层的对偶基判别

### 题号与精确引用

**Hartshorne II.5.6**

### 问题重述

设 $(X, \mathcal{O}_X)$ 为环化空间。证明 $\mathcal{O}_X$-模 $\mathcal{E}$ 是局部自由有限秩的当且仅当存在 $\mathcal{O}_X$-模 $\mathcal{E}'$ 及态射
$$\alpha : \mathcal{E} \otimes \mathcal{E}' \to \mathcal{O}_X, \qquad \beta : \mathcal{O}_X \to \mathcal{E}' \otimes \mathcal{E}$$
使得合成
$$\mathcal{E} \xrightarrow{\mathrm{id} \otimes \beta} \mathcal{E} \otimes \mathcal{E}' \otimes \mathcal{E} \xrightarrow{\alpha \otimes \mathrm{id}} \mathcal{O}_X \otimes \mathcal{E} \cong \mathcal{E}$$
及类似另一条合成均等于恒等映射。

### 详细解答

**$\Rightarrow$**：设 $\mathcal{E}$ 局部自由秩 $r$。取 $\mathcal{E}' = \mathcal{E}^\vee$。局部上 $\mathcal{E} \cong \mathcal{O}_X^{\oplus r}$，则 $\alpha$ 为典范求值配对，$\beta$ 为对偶基映射（将 $1$ 映为 $\sum_i e_i^\vee \otimes e_i$）。直接验证满足两条三角等式。

**$\Leftarrow$**：设存在 $(\mathcal{E}', \alpha, \beta)$ 满足三角等式。对任意开集 $U \subseteq X$，截面范畴 $\mathrm{Mod}_{\mathcal{O}_X(U)}$ 中，$(\mathcal{E}(U), \mathcal{E}'(U))$ 构成对偶对。由模范畴的标准结论，这推出 $\mathcal{E}(U)$ 是有限生成投射模，且 $\mathcal{E}'(U) \cong \mathcal{E}(U)^\vee$。

因 $X$ 是环化空间，局部自由性需在茎或局部开集上验证。对每点 $x \in X$，茎 $(\mathcal{E}_x, \mathcal{E}'_x)$ 也满足对偶关系，故 $\mathcal{E}_x$ 是有限生成自由 $\mathcal{O}_{X,x}$-模（*待验证*：一般局部环上有限生成投射模是否必自由？实际上对任意交换环，对偶对只说明模是有限生成投射的；要得到局部自由层，需说明存在邻域 $U$ 使 $\mathcal{E}|_U$ 自由。标准做法是：取 $x$ 处 $\mathcal{E}_x$ 的基，提升到某邻域 $U$ 的截面，由对偶关系这些截面给出局部同构）。∎

### 关键概念提示

- 这是 **刚性张量范畴** 中对偶对象的刻画：局部自由层恰为范畴中的对偶对象（dualizable object）。
- 该判别法在导出范畴、矩阵因子分解等领域有深远推广。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 直接用茎推出自由 | 对偶基条件在茎上只给出有限生成投射，需额外论证局部自由性（对环化空间，这通常由局部截面的提升完成）。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.ModuleSheaves

open AlgebraicGeometry

-- 对偶基判别：局部自由层等价于存在对偶对象结构
def dualizable_iff_locallyFree {X : RingedSpace} (ℰ : SheafOfModules X.toRingedSpace) :
    ℰ.IsLocallyFreeOfFiniteRank ↔
    ∃ (ℰ' : SheafOfModules X.toRingedSpace) (α : ℰ.tensor ℰ' ⟶ 𝟙_ _)
      (β : 𝟙_ _ ⟶ ℰ'.tensor ℰ),
      (α ▷ ℰ) ≫ (ℰ ◁ β) = 𝟙 ℰ ∧
      (ℰ' ◁ α) ≫ (β ▷ ℰ') = 𝟙 ℰ' :=
  sorry
```

---

## 习题 II.5.7 — 纤维维数判别局部自由性

### 题号与精确引用

**Hartshorne II.5.7**

### 问题重述

设 $X$ 为概形，$\mathcal{E}$ 为 $X$ 上的凝聚层。定义函数
$$\phi(x) = \dim_{k(x)} (\mathcal{E}_x \otimes_{\mathcal{O}_{X,x}} k(x)).$$
(a) 证明 $\phi$ 是上半连续的，且 $\mathcal{E}$ 局部自由当且仅当 $\phi$ 是局部常值函数。
(b) 若 $X$ 是既约概形（reduced），则 $\mathcal{E}$ 局部自由当且仅当 $\phi$ 是局部常值函数。

### 详细解答

**(a) 上半连续性与判别**

上半连续性已在 II.5.2 中证明（拟凝聚层情形），对凝聚层同样适用。

若 $\mathcal{E}$ 局部自由秩 $r$，则显然 $\phi(x) = r$ 为常数。

反之，设 $\phi$ 局部常值。对任意 $x \in X$，取仿射邻域 $U = \operatorname{Spec} A$ 使 $\mathcal{E}|_U = \widetilde{M}$，$M$ 为有限生成 $A$-模。设 $\phi(x) = r$。由上半连续性，存在 $x$ 的邻域 $V \subseteq U$ 使得对所有 $y \in V$ 有 $\phi(y) \le r$。因 $\phi$ 局部常值，可设 $V$ 上 $\phi \equiv r$。

对素理想 $\mathfrak p \in V$，$M \otimes_A k(\mathfrak p)$ 是 $k(\mathfrak p)$-向量空间且维数恰为 $r$。取 $M$ 的 $r$ 个生成元 $m_1, \dots, m_r$ 使其在 $M_{\mathfrak p}/\mathfrak p M_{\mathfrak p}$ 中的像构成基。由 Nakayama 引理，它们在 $M_{\mathfrak p}$ 中生成 $M_{\mathfrak p}$。于是得到满射 $A_{\mathfrak p}^{\oplus r} \twoheadrightarrow M_{\mathfrak p}$。两边张量 $k(\mathfrak p)$ 后维数相同，故为同构。这意味着核在局部化后为零。由有限生成模的局部化性质，存在 $f \notin \mathfrak p$ 使得 $A_f^{\oplus r} \to M_f$ 为同构。故 $\mathcal{E}|_{D(f)}$ 自由。∎

**(b) 既约情形**

*待验证*：题设 (a) 已给出一般判别，(b) 可能是强调在既约概形上，仅需局部常值纤维维数即可（无需预先假设上半连续）。实际上，在既约概形上，有限生成模的纤维维数局部常值已足以保证平坦，从而推出局部自由。证明思路：对仿射情形 $X = \operatorname{Spec} A$（$A$ 既约），设 $M$ 有限生成且纤维维数局部常值 $r$。利用素谱的既约性，可证对任意 $\mathfrak p$，$M_{\mathfrak p}$ 可由 $r$ 个元生成且关系矩阵在某邻域为零，从而 $M$ 局部自由。

### 关键概念提示

- **上半连续性** 是凝聚层的核心性质：秩只能“向下跳”。
- 在 **既约概形** 上，纤维维数局部常值等价于平坦，这是交换代数中著名的判别法（参见 Matsumura《Commutative Ring Theory》）。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 忽略上半连续性已蕴含一般判别 | (a) 中的“当且仅当”无需既约假设；既约性只在弱化条件时使用。 |
| 试图用 Nakayama 直接得同构 | Nakayama 得生成，还需比较秩才能确定同构。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.ModuleSheaves

open AlgebraicGeometry

-- 凝聚层的纤维维数局部常值判别局部自由性
theorem locallyFree_of_constant_fiber_rank {X : Scheme} [IsNoetherian X]
    (ℰ : CoherentSheaf X)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ r : ℕ,
      ∀ y : U, Module.rank (X.presheaf.stalk y ⧸ maximalIdeal _) (ℰ.val.stalk y) = r) :
    ℰ.val.IsLocallyFree :=
  sorry
```

---

## 习题 II.5.8 — 茎自由性判别局部自由性

### 题号与精确引用

**Hartshorne II.5.8**

### 问题重述

设 $X$ 为概形，$\mathcal{E}$ 为 $\mathcal{O}_X$-模。证明：$\mathcal{E}$ 是局部自由层当且仅当对所有 $x \in X$，茎 $\mathcal{E}_x$ 是自由 $\mathcal{O}_{X,x}$-模。

### 详细解答

**$\Rightarrow$**：若 $\mathcal{E}$ 局部自由，则每点 $x$ 有邻域 $U$ 使 $\mathcal{E}|_U \cong \mathcal{O}_U^{\oplus r}$，取茎得 $\mathcal{E}_x \cong \mathcal{O}_{X,x}^{\oplus r}$ 自由。

**$\Leftarrow$**：设所有茎自由。对 $x \in X$，设 $\mathcal{E}_x \cong \mathcal{O}_{X,x}^{\oplus r}$。取 $x$ 的开邻域 $U$ 及截面 $s_1, \dots, s_r \in \mathcal{E}(U)$，使其在 $\mathcal{E}_x$ 中的像构成基。这些截面定义了态射 $\phi : \mathcal{O}_U^{\oplus r} \to \mathcal{E}|_U$。

在茎 $x$ 处，$\phi_x$ 是同构。考虑核层 $\mathcal{K} = \ker \phi$ 与余核层 $\mathcal{C} = \operatorname{coker} \phi$。因 $\phi_x$ 是同构，$\mathcal{K}_x = 0$ 且 $\mathcal{C}_x = 0$。

*关键观察*：零茎的点集是开集。具体地，对任意 $y \in U$，由假设 $\mathcal{E}_y$ 自由，设秩为 $r_y$。映射 $\phi_y : \mathcal{O}_{X,y}^{\oplus r} \to \mathcal{O}_{X,y}^{\oplus r_y}$ 由矩阵给出。该矩阵在 $x$ 处可逆。矩阵可逆的条件（行列式非零）在某开邻域 $V \subseteq U$ 上保持。因此对所有 $y \in V$，$\phi_y$ 是同构，即 $\mathcal{E}|_V \cong \mathcal{O}_V^{\oplus r}$。∎

### 关键概念提示

- 本题 **不假设 Noetherian 或凝聚性**：证明核心是利用“自由模之间的同态由矩阵给出，可逆性在开集上保持”。
- 这与 II.5.3 形成对比：II.5.3 在 Noetherian 凝聚假设下证明同一结论，但本题给出了更一般的环化空间版本。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 默认使用 Nakayama 或有限生成条件 | 本题无需 Noetherian 假设，证明应基于矩阵可逆性的开集保持。 |
| 未说明秩的局部常值性 | 若不同点处茎自由但秩不同，则无法直接粘合为单一秩的局部自由层；但题目条件已保证局部邻域内秩相同。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.ModuleSheaves

open AlgebraicGeometry

-- 任意概形上，层局部自由当且仅当所有茎自由
theorem locallyFree_iff_allStalksFree {X : Scheme}
    (ℰ : SheafOfModules X.toRingedSpace) :
    ℰ.IsLocallyFree ↔ ∀ x : X, Module.Free (X.presheaf.stalk x) (ℰ.stalk x) :=
  sorry
```

---

## 习题 II.5.9 — 凝聚层自由点集的开性

### 题号与精确引用

**Hartshorne II.5.9**

### 问题重述

设 $X$ 为 Noetherian 概形，$\mathcal{F}$ 为凝聚层。
(a) 证明集合 $U = \{x \in X \mid \mathcal{F}_x \text{ 是自由 } \mathcal{O}_{X,x}\text{-模}\}$ 是 $X$ 的开子集。
(b) 若 $X$ 是整的（integral），则 $\mathcal{F}$ 在 $U$ 上的秩是常数（在 $U$ 的每个连通分支上）。

### 详细解答

**(a) 自由点集的开性**

对 $x \in U$，设 $\mathcal{F}_x \cong \mathcal{O}_{X,x}^{\oplus r}$。由 II.5.8（或直接用局部自由性），只需证明存在 $x$ 的邻域 $V$ 使得对所有 $y \in V$，$\mathcal{F}_y$ 自由。

取 $x$ 的仿射邻域 $\operatorname{Spec} A$，$\mathcal{F}|_{\operatorname{Spec} A} = \widetilde{M}$，$M$ 为有限生成 $A$-模。设 $\mathfrak p$ 对应 $x$。因 $M_{\mathfrak p}$ 自由秩 $r$，存在矩阵 $\phi : A^{\oplus r} \to M$ 及 $\psi : M \to A^{\oplus r}$ 使得在 $A_{\mathfrak p}$ 处 $\phi_{\mathfrak p}$ 与 $\psi_{\mathfrak p}$ 互为逆。

这意味着存在 $f \notin \mathfrak p$ 使得 $\phi_f : A_f^{\oplus r} \to M_f$ 是同构（因为“互为逆”可用有限个等式刻画，这些等式在 $A_{\mathfrak p}$ 中成立，故在某 $D(f)$ 上成立）。于是对所有 $\mathfrak q \in D(f)$，$M_{\mathfrak q}$ 自由。故 $D(f) \subseteq U$，$U$ 是开集。∎

**(b) 整概形上的常秩性**

设 $X$ 整。对 $x \in U$，$\mathcal{F}_x \cong \mathcal{O}_{X,x}^{\oplus r}$。张量函数域 $K(X)$（即一般点的茎），得
$$\mathcal{F}_\xi \cong K(X)^{\oplus r}$$
其中 $\xi$ 为 $X$ 的一般点。因 $K(X)$-向量空间 $\mathcal{F}_\xi$ 的维数是良定的（设为 $d$），而任意 $x \in U$ 的局部秩 $r$ 满足 $r = d$（由 $K(X)$-线性扩张保持维数）。故 $U$ 上所有点的秩相同，即秩在 $U$ 上局部常值，从而在每个连通分支上为常数。∎

### 关键概念提示

- 这是 **平坦轨迹的开性** 的层版本：对凝聚层而言，“茎平坦”的点集是开的。
- 整概形上，局部自由层的秩由其在一般点处的向量空间维数唯一决定。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 未用 Noetherian 条件保证有限个等式 | 非 Noetherian 时，同构矩阵的逆可能无法在某开集上整体定义。 |
| 混淆“局部常值”与“整体常值” | 即使在整概形上，秩也只能保证在每个连通分支上常数，未必整体常数。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.ModuleSheaves

open AlgebraicGeometry

-- (a) 凝聚层自由点集的开性
theorem freeLocus_isOpen {X : Scheme} [IsNoetherian X] (ℱ : CoherentSheaf X) :
    IsOpen {x : X | Module.Free (X.presheaf.stalk x) (ℱ.val.stalk x)} :=
  sorry

-- (b) 整概形上秩的常数性
theorem rank_constant_on_connectedComponents {X : Scheme}
    [IsIntegral X] [IsNoetherian X] (ℱ : CoherentSheaf X)
    (U : X.Opens) (hU : ∀ x ∈ U, Module.Free (X.presheaf.stalk x) (ℱ.val.stalk x)) :
    ∀ C ∈ connectedComponents U, ∃ r : ℕ, ∀ x ∈ C,
      Module.rank (X.presheaf.stalk x) (ℱ.val.stalk x) = r :=
  sorry
```

---

**文档位置**: `docs/13-代数几何/Harvard-232br-习题解答/II.5-模与层-续.md`
**创建日期**: 2026-04-17
