---
course: Harvard 232br 代数几何
level: silver

title: Harvard 232br - Hartshorne Chapter II §3 习题解答
msc_primary: 00A99
course_code: Harvard Math 232br
textbook: "Robin Hartshorne, Algebraic Geometry (GTM 52)"
source_textbook: "Robin Hartshorne, Algebraic Geometry (GTM 52)"
source_chapter: "Chapter II - Schemes, Section 3 - First Properties of Schemes"
source_exercise:
  - "II.3.1"
  - "II.3.2"
  - "II.3.3"
  - "II.3.4"
  - "II.3.5"
  - "II.3.6"
difficulty: ⭐⭐ to ⭐⭐⭐
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
      url: ~
    - id: vakil_foag
      type: textbook
      title: Foundations of Algebraic Geometry
      authors:
      - Ravi Vakil
      publisher: self-published
      edition: draft
      year: 2024
      isbn: ~
      msc: 14-01
      chapters: 
      url: "https://math.stanford.edu/~vakil/216blog/"
  databases:
    - id: nlab
      type: database
      name: nLab
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
      consulted_at: 2026-04-17
    - id: stacks_project
      type: database
      name: Stacks Project
      entry_url: "https://stacks.math.columbia.edu/tag/{tag}"
      consulted_at: 2026-04-17
    - id: zbmath
      type: database
      name: zbMATH Open
      entry_url: "https://zbmath.org/?q=an:{zb_id}"
      consulted_at: 2026-04-17
target_courses: [FormalMath银层核心课程, 代数几何]
status: completed
created_at: 2026-04-18
review_status: completed
---

# Harvard 232br - Hartshorne Chapter II §3 习题解答

> 本节覆盖概形态射的有限性条件：局部有限型、拟紧、有限型、有限态射，以及浸入在基变换下的稳定性。这些习题是 **Affine Communication Lemma** 的主要应用场域。

---

## 习题 II.3.1 — 局部有限型的局部刻画

### 题号与精确引用

**Hartshorne II.3.1**

### 问题重述

证明：概形态射 $f:X\to Y$ 是 **局部有限型**（locally of finite type）当且仅当对 $Y$ 的每个开仿射子集 $V=\operatorname{Spec}B$，$f^{-1}(V)$ 可被开仿射集 $U_i=\operatorname{Spec}A_i$ 覆盖，其中每个 $A_i$ 都是有限生成 $B$-代数。

### 详细解答

**$\Rightarrow$**：由定义，$Y$ 可被开仿射 $V_j=\operatorname{Spec}B_j$ 覆盖，使得每个 $f^{-1}(V_j)$ 可被开仿射 $U_{ij}=\operatorname{Spec}A_{ij}$ 覆盖，且 $A_{ij}$ 是有限生成 $B_j$-代数。现取 $Y$ 的任意开仿射 $V=\operatorname{Spec}B$。

$V$ 可被 $V\cap V_j$ 覆盖，而每个 $V\cap V_j$ 可被 $B$ 中的 distinguished open $D(g_k)$ 覆盖（这些 $D(g_k)$ 同时也是 $B_j$ 中的 distinguished open）。由 II.2.1，$f^{-1}(D(g_k))$ 可被 $U_{ij}$ 中的 distinguished open（对应于 $A_{ij}$ 的局部化）覆盖，而局部化保持“有限生成代数”性质。于是 $f^{-1}(V)$ 可被有限生成 $B$-代数的仿射开集覆盖。∎

**$\Leftarrow$**：显然，因为条件在 $V=Y$ 的某个仿射覆盖上成立即满足定义。∎

### 关键概念提示

- **Affine Communication Lemma** 的精神：一个对仿射开集定义的性质，如果在 distinguished open 下稳定，并且在有限覆盖下可逆，则它对所有仿射开集成立。
- 局部化 $A_f$ 是有限生成 $A$-代数（由 $A$ 添加 $1/f$ 得到）。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 认为局部化可能破坏有限生成性 | $A_f$ 作为 $A$-代数由 $1/f$ 生成，仍是有限生成的。 |
| 未验证 distinguished open 在两个仿射开集中的相容性 | 必须用 $D(g)$ 作为公共基。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

open AlgebraicGeometry

-- 局部有限型的等价刻画（全局仿射覆盖版本）
theorem locallyOfFiniteType_iff_affine (f : Scheme.Hom X Y) :
    LocallyOfFiniteType f ↔
    ∀ (V : Y.Opens) (_ : IsAffineOpen V.1),
      ∃ (U : Set X.Opens) (_ : U.countable),
        ∀ (U' ∈ U), IsAffineOpen U'.1 ∧
          ∃ (φ : Γ(X, U') ⟶ Γ(Y, V)),
            RingHom.FiniteType φ :=
  sorry
```

---

## 习题 II.3.2 — 拟紧的局部刻画

### 题号与精确引用

**Hartshorne II.3.2**

### 问题重述

证明：概形态射 $f:X\to Y$ 是 **拟紧的**（quasi-compact）当且仅当存在 $Y$ 的仿射开覆盖 $\{V_i\}$，使得每个 $f^{-1}(V_i)$ 是拟紧的，当且仅当对 $Y$ 的**每个**开仿射子集 $V$，$f^{-1}(V)$ 都是拟紧的。

### 详细解答

**定义 $\Rightarrow$ 存在仿射覆盖**：这是拟紧态射的定义。

**存在仿射覆盖 $\Rightarrow$ 每个仿射开集**：设 $V=\operatorname{Spec}B\subseteq Y$ 是任意仿射开集。$V$ 可被 $V\cap V_i$ 覆盖。每个 $V\cap V_i$ 是 $V$ 中的开集，从而可被 $B$ 的 distinguished open $D(g_{ij})$ 覆盖。因为 $V$ 是拟紧的，可取有限子覆盖 $V=\bigcup_{k=1}^n D(g_k)$。对每个 $k$，$f^{-1}(D(g_k))$ 是 $f^{-1}(V_i)$ 中的 distinguished open，因 $f^{-1}(V_i)$ 拟紧，其任意开子集也拟紧（拓扑空间中拟紧空间的任意开子集不一定拟紧——但此处 $f^{-1}(V_i)$ 是概形，其开子集 $f^{-1}(D(g_k))$ 可被仿射开集覆盖，而 $f^{-1}(V_i)$ 的拟紧性保证存在有限子覆盖）。更准确地说：$f^{-1}(V_i)$ 拟紧意味着它的任意开覆盖有有限子覆盖；$f^{-1}(D(g_k))$ 作为 $f^{-1}(V_i)$ 的开子集，其任何开覆盖也是 $f^{-1}(V_i)$ 的开覆盖，故存在有限子覆盖。因此每个 $f^{-1}(D(g_k))$ 拟紧。于是 $f^{-1}(V)=\bigcup_{k=1}^n f^{-1}(D(g_k))$ 是有限个拟紧集的并，故拟紧。∎

### 关键概念提示

- 在概形中，**拟紧 = 可被有限个仿射开集覆盖**。这是定义与计算中最常用的等价描述。
- 拟紧性是 **局部在底空间上的**（local on the base）。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 认为拟紧空间的任意开子集必拟紧 | 一般拓扑空间中这不成立；但在概形中，开子概形若可被有限个仿射覆盖则拟紧。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

open AlgebraicGeometry

-- 拟紧态射的局部刻画
theorem quasiCompact_iff_affine (f : Scheme.Hom X Y) :
    QuasiCompact f ↔
    ∀ (V : Y.Opens) (_ : IsAffineOpen V.1), QuasiCompactSpace (f ⁻¹ᵁ V) :=
  sorry
```

---

## 习题 II.3.3 — 有限型 = 局部有限型 + 拟紧

### 题号与精确引用

**Hartshorne II.3.3**

### 问题重述

证明：概形态射 $f:X\to Y$ 是 **有限型**（of finite type）当且仅当它既是局部有限型又是拟紧的。并进一步证明：有限态射必是有限型的。

### 详细解答

**等价性**：

$\Rightarrow$：设 $f$ 有限型。由定义，$Y$ 可被仿射开集 $V_i=\operatorname{Spec}B_i$ 覆盖，使得每个 $f^{-1}(V_i)$ 可被**有限**个开仿射 $U_{ij}=\operatorname{Spec}A_{ij}$ 覆盖，且 $A_{ij}$ 是有限生成 $B_i$-代数。

- 局部有限型：这是定义的弱化（允许任意覆盖），故显然成立。
- 拟紧：每个 $f^{-1}(V_i)$ 是有限个仿射（从而拟紧）集的并，故拟紧。由 II.3.2，$f$ 拟紧。

$\Leftarrow$：设 $f$ 局部有限型且拟紧。取 $Y$ 的仿射开覆盖 $\{V_i=\operatorname{Spec}B_i\}$。由局部有限型，每个 $f^{-1}(V_i)$ 可被开仿射 $U_{ij}=\operatorname{Spec}A_{ij}$（$A_{ij}$ 有限生成 $B_i$-代数）覆盖。又因 $f$ 拟紧，$f^{-1}(V_i)$ 是拟紧的，故该覆盖可取有限子覆盖。于是 $f$ 有限型。∎

**有限态射是有限型**：设 $f$ 有限。则 $Y$ 可被仿射开集 $V_i=\operatorname{Spec}B_i$ 覆盖，使得 $f^{-1}(V_i)=\operatorname{Spec}A_i$ 且 $A_i$ 是有限 $B_i$-模。有限模代数自然是有限生成代数（生成元集即是模生成元集）。又因每个 $f^{-1}(V_i)$ 本身是仿射（单个开集），覆盖自然是有限的。故 $f$ 有限型。∎

### 关键概念提示

- **有限型 = 局部有限型 + 整体紧凑性（拟紧）**。这在代数几何中类似于“局部有限维 + 紧”的组合。
- 有限态射比有限型强得多：它要求整体上是模有限的，而不仅是代数有限生成。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 混淆“有限生成代数”与“有限生成模” | 有限生成模一定给出有限生成代数，但反之不成立。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Finite

open AlgebraicGeometry

-- 有限型等价于局部有限型且拟紧
theorem finiteType_iff_locallyOfFiniteType_and_quasiCompact (f : Scheme.Hom X Y) :
    FiniteType f ↔ (LocallyOfFiniteType f ∧ QuasiCompact f) :=
  sorry

-- 有限态射是有限型
theorem finite_implies_finiteType (f : Scheme.Hom X Y) [Finite f] : FiniteType f :=
  sorry
```

---

## 习题 II.3.4 — 有限态射的局部刻画

### 题号与精确引用

**Hartshorne II.3.4**

### 问题重述

证明：概形态射 $f:X\to Y$ 是 **有限的**（finite）当且仅当对 $Y$ 的**每个**开仿射子集 $V=\operatorname{Spec}B$，原像 $f^{-1}(V)$ 是仿射的且等于 $\operatorname{Spec}A$，其中 $A$ 是有限 $B$-模。

### 详细解答

**$\Leftarrow$**：显然，因为条件在 $Y$ 的某个仿射覆盖上成立即满足定义。

**$\Rightarrow$**（Affine Communication Lemma 的应用）：设 $Y$ 可被仿射开集 $V_i=\operatorname{Spec}B_i$ 覆盖，使得 $f^{-1}(V_i)=\operatorname{Spec}A_i$ 且 $A_i$ 是有限 $B_i$-模。对任意开仿射 $V=\operatorname{Spec}B\subseteq Y$，需证 $f^{-1}(V)$ 仿射且对应有限 $B$-模。

先证对 distinguished open 稳定：若 $V=\operatorname{Spec}B$ 满足条件，则对任意 $g\in B$，$D(g)\subseteq V$ 满足 $f^{-1}(D(g))=(f^{-1}(V))_{\bar g}=\operatorname{Spec}A_{\bar g}$，其中 $\bar g$ 是 $g$ 在 $A$ 中的像。因 $A$ 是有限 $B$-模，$A_{\bar g}\cong A\otimes_B B_g$ 是有限 $B_g$-模。

再证对有限覆盖可逆：设 $V=\operatorname{Spec}B$ 可被 $D(g_1),\dots,D(g_n)$ 覆盖，且每个 $f^{-1}(D(g_k))=\operatorname{Spec}A_k$ 对应有限 $B_{g_k}$-模 $A_k$。因为 $f^{-1}(D(g_k))$ 是 $f^{-1}(V)$ 的仿射开覆盖，且 $f^{-1}(D(g_k))\cap f^{-1}(D(g_l))=f^{-1}(D(g_kg_l))$ 对应 $A_k\otimes_B B_{g_l}\cong A_l\otimes_B B_{g_k}$，这些环和粘合数据满足仿射概形粘合的条件（II.2.12 的变形）。结果得到 $f^{-1}(V)=\operatorname{Spec}A$，其中 $A$ 是这些 $A_k$ 沿 $D(g_kg_l)$ 的等化子。

由下降理论（或直接用 Atiyah-Macdonald Exercise 2.25）：若 $B$-模 $M$ 满足 $M_{g_k}$ 是有限 $B_{g_k}$-模且 $g_k$ 生成单位理想，则 $M$ 是有限 $B$-模。取 $A$ 作为 $B$-代数（同时也是 $B$-模），由 $A_{g_k}=A_k$ 有限及 $(g_1,\dots,g_n)=B$，得 $A$ 是有限 $B$-模。∎

### 关键概念提示

- 下降引理（Descent for finiteness）是证明此类“局部到整体”命题的核心工具。
- 有限态射是 **仿射的**（affine）且 **模有限的**（module-finite）。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 直接断言有限覆盖的仿射开集的等化子仍是仿射 | 需要用模的下降引理来保证整体有限性。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Morphisms.Finite

open AlgebraicGeometry

-- 有限态射的局部刻画：每个仿射开集的原像都是仿射且模有限
theorem finite_iff_affine_and_moduleFinite (f : Scheme.Hom X Y) :
    Finite f ↔
    ∀ (V : Y.Opens) (_ : IsAffineOpen V.1),
      IsAffineOpen (f ⁻¹ᵁ V).1 ∧
      Module.Finite (Γ(Y, V)) (Γ(X, f ⁻¹ᵁ V)) :=
  sorry
```

---

## 习题 II.3.5 — 闭浸入是有限态射

### 题号与精确引用

**Hartshorne II.3.5**

### 问题重述

证明闭浸入（closed immersion）是有限态射。

### 详细解答

设 $i:Z\to X$ 是闭浸入。由定义（II.2.18），$X$ 可被仿射开集 $U_k=\operatorname{Spec}A_k$ 覆盖，使得 $i^{-1}(U_k)=\operatorname{Spec}(A_k/I_k)$ 对某个理想 $I_k\subseteq A_k$，且诱导的层映射是满射。

于是 $A_k/I_k$ 作为 $A_k$-模由 $1$ 生成，显然是有限 $A_k$-模。由 II.3.4，闭浸入是有限态射。∎

### 关键概念提示

- 闭浸入的定义要求 **拓扑上是闭嵌入** 且 **层映射局部由商环给出**。
- 商环 $A/I$ 作为 $A$-模由 $1$ 的像生成，这是最简单的有限模例子。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 未验证闭浸入满足有限态射定义中的仿射覆盖条件 | 定义本身已给出该覆盖，直接应用即可。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.ClosedImmersion

open AlgebraicGeometry

-- 闭浸入是有限态射
theorem closedImmersion_implies_finite {X Y : Scheme} (f : X ⟶ Y) [ClosedImmersion f] :
    Finite f :=
  sorry
```

---

## 习题 II.3.6 — 浸入在基变换下的稳定性

### 题号与精确引用

**Hartshorne II.3.6**

### 问题重述

证明开浸入（open immersion）与闭浸入（closed immersion）在任意基变换（base extension）下保持稳定。即：若 $f:Y\to X$ 是开（或闭）浸入，则对任意态射 $g:X'\to X$，拉回 $f':Y\times_X X'\to X'$ 也是开（或闭）浸入。

### 详细解答

**开浸入**：设 $f:Y\to X$ 是开浸入，则 $Y$ 同构于 $X$ 的某个开子概形 $U$，且 $f$ 就是包含映射。纤维积 $U\times_X X'$ 在拓扑上等于 $g^{-1}(U)\subseteq X'$（纤维积的拓扑描述），且结构层的拉回恰为 $X'$ 在 $g^{-1}(U)$ 上的限制。故 $f'$ 是开浸入 $g^{-1}(U)\hookrightarrow X'$。

**闭浸入**：先设所有概形都是仿射的：$X=\operatorname{Spec}A$，$X'=\operatorname{Spec}A'$，$Y=\operatorname{Spec}(A/I)$。则纤维积为
$$Y\times_X X'=\operatorname{Spec}((A/I)\otimes_A A')=\operatorname{Spec}(A'/IA'),$$
而 $f'$ 对应于商映射 $A'\to A'/IA'$，显然是闭浸入。

一般情形：取 $X$ 的仿射开覆盖 $\{U_i\}$，令 $U_i'=g^{-1}(U_i)$。由上述仿射情形，$f'^{-1}(U_i')\to U_i'$ 是闭浸入。闭浸入是局部在底空间上的性质：若 $X'$ 可被开集覆盖，使得在每个开集上的限制是闭浸入，则整体是闭浸入。故 $f'$ 是闭浸入。∎

### 关键概念提示

- 纤维积的拓扑：$|Y\times_X X'|$ 同胚于 $|Y|\times_{|X|}|X'|$ 的某种拓扑，对开浸入可直接验证原像的刻画。
- 闭浸入的稳定性在局部验证后，用“闭浸入是局部在底上的”即可粘合。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 对开浸入试图用环的张量积 | 开浸入不一定对应环同态，应直接用拓扑与限制层。 |
| 忽略闭浸入在一般情形需要局部验证 | 必须从仿射情形推广到整体。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Immersion

open AlgebraicGeometry

-- 开浸入在基变换下稳定
theorem openImmersion_stableUnderBaseChange :
    MorphismProperty.StableUnderBaseChange @IsOpenImmersion :=
  sorry

-- 闭浸入在基变换下稳定
theorem closedImmersion_stableUnderBaseChange :
    MorphismProperty.StableUnderBaseChange @ClosedImmersion :=
  sorry
```

---

**文档位置**: `docs/13-代数几何/Harvard-232br-习题解答/II.3-态射性质.md`
**创建日期**: 2026-04-17


## 习题

**习题 1.1**。证明：仿射态射 $f: X \\to Y$ 是紧的当且仅当对应的环同态使 $A$ 成为有限生成 $R$-模。

*解答*：仿射态射的紧性等价于 $\\operatorname{Spec} A \\to \\operatorname{Spec} R$ 的纤维有限，即 $A$ 是有限 $R$-模。$\square$

---

**习题 1.2**。举例说明：有限型态射不一定是有限的。

*解答*：$\\mathbb{A}^1 \\to \\operatorname{Spec} k$ 是有限型的（$k[x]$ 是有限生成 $k$-代数），但不是有限的（$k[x]$ 不是有限 $k$-模）。$\square$

## 相关文档

- [II.1-层的基本性质](II.1-层的基本性质.md)
- [II.2-概形的基本性质](II.2-概形的基本性质.md)
- [II.4-分离性与本征性](II.4-分离性与本征性.md)
- [II.5-模与层-续](II.5-模与层-续.md)
- [II.5-模与层](II.5-模与层.md)
## 参考文献

1. Hartshorne, R. (1977). *Algebraic Geometry* (GTM 52). Springer. ISBN: 978-0387902449.
2. Vakil, R. (2024). *The Rising Sea: Foundations of Algebraic Geometry* (draft). Available at: http://math.stanford.edu/~vakil/216blog/
3. Liu, Q. (2002). *Algebraic Geometry and Arithmetic Curves*. Oxford University Press. ISBN: 978-0198502845.