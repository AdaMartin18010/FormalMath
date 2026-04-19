---
course: Harvard 232br 代数几何
level: silver

title: Harvard 232br - Hartshorne Chapter II §2 习题解答
msc_primary: 00A99
course_code: Harvard Math 232br
textbook: "Robin Hartshorne, Algebraic Geometry (GTM 52)"
source_textbook: "Robin Hartshorne, Algebraic Geometry (GTM 52)"
source_chapter: "Chapter II - Schemes, Section 2 - Schemes"
source_exercise:
  - "II.2.1"
  - "II.2.2"
  - "II.2.3"
  - "II.2.4"
  - "II.2.5"
  - "II.2.6"
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
---

# Harvard 232br - Hartshorne Chapter II §2 习题解答

> 本节覆盖概形的基本构造：局部化对应的子概形、开子概形、既约概形、$\operatorname{Spec}$ 与全局截面的伴随关系，以及 $\operatorname{Spec}\mathbb{Z}$ 与 $\operatorname{Spec}0$ 的泛对象性质。

---

## 习题 II.2.1 — $D(f)\cong\operatorname{Spec}A_f$

### 题号与精确引用

**Hartshorne II.2.1**

### 问题重述

设 $A$ 为环，$X=\operatorname{Spec}A$，$f\in A$，$D(f)\subseteq X$ 为 $V((f))$ 的补开集。证明局部环化空间 $(D(f),\mathcal{O}_X|_{D(f)})$ 同构于 $\operatorname{Spec}A_f$。

### 详细解答

**步骤 1：拓扑同胚**

由交换代数，$A_f$ 的素理想与 $A$ 中不含 $f$ 的素理想一一对应：$\mathfrak q\subseteq A_f$ 对应于其在 $A\to A_f$ 下的原像 $\mathfrak p$，且 $f\notin\mathfrak p$。这给出双射
$$\phi:\operatorname{Spec}A_f\longrightarrow D(f),\quad\mathfrak q\longmapsto\mathfrak p.$$

验证 $\phi$ 是闭映射：对任意理想 $I\subseteq A_f$，$\phi(V(I))=V(J)\cap D(f)$，其中 $J$ 是 $I$ 在 $A$ 中的原像。故 $\phi$ 是闭的。同理 $\phi^{-1}$ 也是闭的，因此是同胚。

**步骤 2：结构层的同构**

由 II.1.1(d)，对任意 $g\in A$ 使得 $D(g)\subseteq D(f)$（即 $f\in\sqrt{(g)}$），有 $\mathcal{O}_X(D(g))\cong A_g$。而 $A_g\cong (A_f)_{g/1}$（$g/1$ 在 $A_f$ 中的像）。于是对 $D(f)$ 的基 $\{D(g)\}$，预层 $U\mapsto\mathcal{O}_X(U)$ 与 $\operatorname{Spec}A_f$ 的结构层在该基上的取值相同。由层的唯一性（或**命题 2.2**(b)），它们诱导出同构的层。∎

### 关键概念提示

- $A_f$ 的素理想对应是 **局部化基本定理**，它是概形局部性质的基石。
- 这说明 **$D(f)$ 本身也是仿射概形**，因此仿射概形上的 distinguished open 构成仿射开覆盖的基。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 只证拓扑同胚而忽略结构层 | 概形同构必须同时验证拓扑与结构层。 |
| 试图全局定义环同态 $A_f\to\mathcal{O}_X(D(f))$ 但不验证层条件 | 实际上 II.1.1(d) 已经给出了这层同构。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Spec

open AlgebraicGeometry PrimeSpectrum

-- D(f) ≅ Spec A_f
def basicOpenIso (A : Type*) [CommRing A] (f : A) :
    (Spec.structureSheaf A).presheaf.restrict (Opens.isOpenEmbedding (basicOpen f)) ≅
    Spec.structureSheaf (Localization.Away f) :=
  sorry
```

---

## 习题 II.2.2 — 开子概形仍是概形

### 题号与精确引用

**Hartshorne II.2.2**

### 问题重述

设 $(X,\mathcal{O}_X)$ 是概形，$U\subseteq X$ 是任意开子集。证明 $(U,\mathcal{O}_X|_U)$ 也是概形。我们称之为 **开子概形**（open subscheme）。

### 详细解答

对任意 $x\in U$，因 $X$ 是概形，存在 $x$ 的开仿射邻域 $V=\operatorname{Spec}A\subseteq X$。则 $U\cap V$ 是 $V$ 中的开集。由仿射概形拓扑的基性质，$U\cap V$ 可被 $V$ 中的 distinguished open 集 $D(f_i)$ 覆盖。由 II.2.1，每个 $D(f_i)$ 都是仿射概形。于是 $U$ 的每一点都有仿射开邻域（在 $U$ 内），故 $(U,\mathcal{O}_X|_U)$ 是概形。∎

### 关键概念提示

- 概形的定义只要求 **局部仿射**；开子集显然保持这一性质。
- 这说明“概形”概念对开子集是封闭的，类似于流形对开子集的封闭性。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 认为 $U$ 必须能被 $X$ 的仿射覆盖直接限制得到 | 关键是 $U\cap V$ 在 $V$ 中可被 distinguished open 覆盖，而 distinguished open 是仿射的。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Scheme

open AlgebraicGeometry

-- 开子概形仍是概形（类型类推断即可，这里给出显式构造占位）
def openSubscheme (X : Scheme) (U : X.Opens) : Scheme :=
  sorry
```

---

## 习题 II.2.3 — 既约概形（Reduced Schemes）

### 题号与精确引用

**Hartshorne II.2.3**

### 问题重述

(a) 证明 $(X,\mathcal{O}_X)$ 是既约概形当且仅当对所有 $P\in X$，局部环 $\mathcal{O}_{X,P}$ 无幂零元。
(b) 对任意概形 $(X,\mathcal{O}_X)$，证明存在唯一的既约闭子概形 $(X_{\mathrm{red}},\mathcal{O}_{X_{\mathrm{red}}})$ 使得其底拓扑空间与 $X$ 相同，并满足：若 $Y$ 是既约概形，则任何态射 $f:X\to Y$ 唯一地通过 $X_{\mathrm{red}}$ 分解。
(c) 证明若 $f:X\to Y$ 且 $Y$ 既约，则 $f$ 唯一地通过 $X_{\mathrm{red}}$ 分解。

### 详细解答

**(a) 既约的 stalk 判别**

$\Rightarrow$：设 $X$ 既约，$P\in X$。若 $f\in\mathcal{O}_{X,P}$ 幂零，则存在 $P$ 的邻域 $U$ 及代表元 $s\in\mathcal{O}_X(U)$ 使得 $s^n=0$。因 $X$ 既约，$\mathcal{O}_X(U)$ 无幂零，故 $s=0$，从而 $f=0$。

$\Leftarrow$：设所有 stalk 既约。取开仿射覆盖 $\{U_i=\operatorname{Spec}A_i\}$。stalk 既约意味着 $(A_i)_{\mathfrak p}$ 既约对所有 $\mathfrak p\in\operatorname{Spec}A_i$，从而 $A_i$ 本身既约（幂零元的局部化仍为幂零元，若所有局部化无幂零则原环亦无）。于是 $\mathcal{O}_X(U_i)=A_i$ 既约。对任意开集 $U$，$\mathcal{O}_X(U)$ 是这些 $A_i$ 的等化子，无幂零元的环的等化子仍无幂零元，故 $U$ 既约。∎

**(b) 既约闭子概形的构造**

令 $\mathcal{N}\subseteq\mathcal{O}_X$ 为幂零根层（nilradical sheaf）：$\mathcal{N}(U)=\operatorname{Nil}(\mathcal{O}_X(U))$。由 (a)，这是拟凝聚理想层（在仿射开集 $U=\operatorname{Spec}A$ 上对应于 $\operatorname{Nil}(A)$）。定义
$$X_{\mathrm{red}}:=X,\quad\mathcal{O}_{X_{\mathrm{red}}}:=\mathcal{O}_X/\mathcal{N}.$$
则 $(X_{\mathrm{red}},\mathcal{O}_{X_{\mathrm{red}}})$ 是闭子概形，且显然既约。唯一性：若有两个这样的闭子概形 $Z_1,Z_2$，则它们对应的理想层 $\mathcal{I}_1,\mathcal{I}_2$ 都满足 $\mathcal{O}_X/\mathcal{I}_i$ 既约，即 $\mathcal{I}_i=\mathcal{N}$。故 $Z_1=Z_2$。∎

**(c) 分解性质**

由 (b)，$X_{\mathrm{red}}\to X$ 是闭浸入。复合 $X_{\mathrm{red}}\to X\xrightarrow{f}Y$ 给出所求分解。唯一性：若有另一分解 $X_{\mathrm{red}}'\to Y$，则它必对应于商去相同的幂零根层。∎

### 关键概念提示

- **幂零根层** 是拟凝聚的，这是因为它在仿射局部上由幂零根生成。
- $X_{\mathrm{red}}$ 的函子性说明“去幂零”是概形范畴的右伴随（或反射子范畴的左伴随）。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 直接断言任意开集的截面环既约 | 需先对仿射开集证明，再推广到一般开集。 |
| 忽略唯一性的证明 | 必须说明任何满足条件的闭子概形理想层都等于幂零根层。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Scheme

open AlgebraicGeometry

-- 既约闭子概形的存在与唯一性（以陈述方式占位）
def reducedSubscheme (X : Scheme) :
    { Z : ClosedImmersion X // Z.scheme.IsReduced ∧
      ∀ (Y : Scheme) [IsReduced Y] (f : X ⟶ Y), ∃! g : Z.scheme ⟶ Y, Z.morphism ≫ g = f } :=
  sorry
```

---

## 习题 II.2.4 — $\operatorname{Spec}$ 是全局截面函子的右伴随

### 题号与精确引用

**Hartshorne II.2.4**

### 问题重述

设 $A$ 为环，$(X,\mathcal{O}_X)$ 为概形。给定环同态 $\varphi:A\to\Gamma(X,\mathcal{O}_X)$，证明存在唯一的概形态射 $(f,f^\#):X\to\operatorname{Spec}A$，使得 $f^\#:\mathcal{O}_{\operatorname{Spec}A}\to f_*\mathcal{O}_X$ 在整体截面上诱导的映射恰好是 $\varphi$。

### 详细解答

**存在性**：取 $X$ 的仿射开覆盖 $\{U_i=\operatorname{Spec}A_i\}$。限制映射给出环同态
$$\varphi_i:A\xrightarrow{\varphi}\Gamma(X,\mathcal{O}_X)\longrightarrow A_i.$$
由**命题 2.3**(b)，每个 $\varphi_i$ 诱导概形态射 $f_i:U_i\to\operatorname{Spec}A$。

在 $U_i\cap U_j$ 上，$f_i$ 与 $f_j$ 的连续映射相同：对 $x\in U_i\cap U_j$，$f_i(x)=\varphi_i^{-1}(\mathfrak p_x)=\varphi^{-1}(\mathfrak p_x)=f_j(x)$（这里 $\mathfrak p_x\subseteq A_i$ 是对应于 $x$ 的素理想）。层映射的相容性由限制映射的交换性保证。于是这些局部态射可粘合为整体连续映射 $f:X\to\operatorname{Spec}A$。

层映射 $f^\#:\mathcal{O}_{\operatorname{Spec}A}\to f_*\mathcal{O}_X$ 也在仿射开集上由 $\varphi_i$ 诱导，由层的粘合公理得到整体层映射。整体截面恰好是 $\varphi$。

**唯一性**：设 $(g,g^\#)$ 也诱导 $\varphi$。对任意仿射开集 $U_i=\operatorname{Spec}A_i$，$g|_{U_i}$ 对应的环同态 $A\to A_i$ 必为 $\varphi_i$（由整体截面的条件），故 $g|_{U_i}=f_i$。由粘合唯一性，$g=f$ 且 $g^\#=f^\#$。∎

### 关键概念提示

- 这是 **$\operatorname{Spec}$ 与 $\Gamma$ 的伴随关系** 的核心：$\operatorname{Hom}_{\text{Ring}}(A,\Gamma(X,\mathcal{O}_X))\cong\operatorname{Hom}_{\text{Sch}}(X,\operatorname{Spec}A)$。
- 该伴随说明仿射概形是“可表示的”，是概形理论的计算基石。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 只定义拓扑映射而忽略层映射的相容性 | 层映射必须在交集上一致，这是粘合的关键。 |
| 试图直接整体定义 $f$ 而不取仿射覆盖 | 必须先在局部构造再粘合。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Spec

open AlgebraicGeometry

-- Spec 是全局截面函子的右伴随（同构陈述）
def specGammaAdjunction (A : Type*) [CommRing A] (X : Scheme) :
    (X ⟶ Spec (CommRingCat.of A)) ≃ (A ⟶ Γ.obj (Opposite.op X)) :=
  sorry
```

---

## 习题 II.2.5 — $\operatorname{Spec}\mathbb{Z}$ 是终对象

### 题号与精确引用

**Hartshorne II.2.5**

### 问题重述

描述 $\operatorname{Spec}\mathbb{Z}$，并证明它是概形范畴的终对象：即每个概形 $X$ 都有唯一的态射 $X\to\operatorname{Spec}\mathbb{Z}$。

### 详细解答

$\operatorname{Spec}\mathbb{Z}=\{(0)\}\cup\{(p)\mid p\text{ 为素数}\}$。拓扑上，$(0)$ 是一般点，其闭包为全空间；每个 $(p)$ 是闭点。

对任意概形 $X$，整体截面环 $\Gamma(X,\mathcal{O}_X)$ 是含幺环，故有唯一的环同态 $\mathbb{Z}\to\Gamma(X,\mathcal{O}_X)$（将 $1$ 映到 $1$）。由 II.2.4，这对应唯一的概形态射 $X\to\operatorname{Spec}\mathbb{Z}$。∎

### 关键概念提示

- $\mathbb{Z}$ 是 **环范畴的始对象**（在含幺环同态要求 $1\mapsto 1$ 的约定下），因此 $\operatorname{Spec}\mathbb{Z}$ 是 **概形范畴的终对象**。
- 这意味着每个概形都是“在 $\mathbb{Z}$ 上”的，即绝对概形（absolute scheme）。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 忽略环同态必须将 $1$ 映到 $1$ | 在此约定下 $\mathbb{Z}\to A$ 确实唯一。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Spec

open AlgebraicGeometry

-- Spec ℤ 是终对象
def specZIsTerminal : IsTerminal (Spec (CommRingCat.of ℤ)) :=
  sorry
```

---

## 习题 II.2.6 — $\operatorname{Spec}0$ 是初对象

### 题号与精确引用

**Hartshorne II.2.6**

### 问题重述

描述零环的谱，并证明它是概形范畴的初对象（initial object）。

### 详细解答

零环 $0$ 只有一个元素 $0=1$，故 $\operatorname{Spec}0=\varnothing$（空集），结构层是零环上的平凡层。

对任意概形 $X$，存在唯一的环同态 $\Gamma(X,\mathcal{O}_X)\to 0$（将所有元素映到 $0$）。由 II.2.4，这对应唯一的概形态射 $\operatorname{Spec}0\to X$（拓扑上为空集到 $X$ 的包含，层映射平凡）。∎

### 关键概念提示

- 零环是 **环范畴的终对象**，因此其谱是 **概形范畴的初对象**。
- 注意：这里环同态的方向与 II.2.5 相反，伴随关系 $X\mapsto\Gamma(X)$ 是反变的（从概形到环），而 $A\mapsto\operatorname{Spec}A$ 也是反变的；复合后 $\operatorname{Spec}$ 变为从环到概形的协变右伴随。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 认为 $\operatorname{Spec}0$ 不是概形 | 空局部环化空间满足概形定义（空真）。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Spec

open AlgebraicGeometry

-- Spec 0 是初对象
def specZeroIsInitial : IsInitial (Spec (CommRingCat.of PUnit)) :=
  sorry
```

---

**文档位置**: `docs/13-代数几何/Harvard-232br-习题解答/II.2-概形的基本性质.md`
**创建日期**: 2026-04-17


## 习题

**习题 1.1**。证明 $\\operatorname{Spec} \\mathbb{Z}$ 是终对象于概形范畴，即对任意概形 $X$，存在唯一的态射 $X \\to \\operatorname{Spec} \\mathbb{Z}$。

*解答*：由环的泛性质，$\\mathbb{Z}$ 是环范畴的始对象。$\\operatorname{Spec}$ 是反变函子，故 $\\operatorname{Spec}\\mathbb{Z}$ 是终对象。$\square$

---

**习题 1.2**。描述 $\\mathbb{A}^1_\\mathbb{C} = \\operatorname{Spec} \\mathbb{C}[x]$ 的闭点和generic point。

*解答*：闭点对应极大理想 $(x-a)$（$a\\in\\mathbb{C}$），即复平面上的点。Generic point 对应零理想 $(0)$。$\square$
