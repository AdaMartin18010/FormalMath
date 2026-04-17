---
course: Harvard 232br 代数几何
level: silver

title: Harvard 232br - Hartshorne Chapter II §4 习题解答
course_code: Harvard Math 232br
textbook: "Robin Hartshorne, Algebraic Geometry (GTM 52)"
source_textbook: "Robin Hartshorne, Algebraic Geometry (GTM 52)"
source_chapter: "Chapter II - Schemes, Section 4 - Separated and Proper Morphisms"
source_exercise:
  - "II.4.1"
  - "II.4.2"
  - "II.4.3"
  - "II.4.4"
  - "II.4.5 (a)(b)(d)"
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
      chapters: []
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
      chapters: []
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
---

# Harvard 232br - Hartshorne Chapter II §4 习题解答

> 本节覆盖分离性与本征性的核心习题，包括有限态射的固有性、分离性判别（稠密开集上相等的态射必相等）、分离概形中仿射开集的交仍是仿射的，以及赋值判别法的初步应用。

---

## 习题 II.4.1 — 有限态射是固有的（proper）

### 题号与精确引用

**Hartshorne II.4.1**

### 问题重述

证明有限态射（finite morphism）是固有的（proper）。

### 详细解答

设 $f:X\to Y$ 是有限态射。需验证固有性的三个条件：

1. **分离的**：有限态射是仿射的（由 II.3.4），而仿射态射是分离的（因为对角线 $\Delta:X\to X\times_Y X$ 对应于环同态 $A\otimes_B A\to A$，$a\otimes a'\mapsto aa'$，其核为理想 $I=\ker\mu$；$V(I)$ 是闭集，故 $\Delta$ 是闭浸入）。
2. **有限型的**：由 II.3.3，有限态射是有限型的。
3. **泛闭的**（universally closed）：设 $g:Y'\to Y$ 为任意基变换。由 II.3.6，有限态射在基变换下保持有限。有限态射是闭映射（因为仿射局部上 $\operatorname{Spec}A\to\operatorname{Spec}B$ 的像为 $V(\ker(B\to A))$，是闭的），故基变换后的态射 $f':X\times_Y Y'\to Y'$ 也是闭的。因此 $f$ 泛闭。∎

### 关键概念提示

- **仿射态射的分离性**：因为对角线对应于乘法映射，其像由核理想定义，故为闭浸入。
- **有限态射的像**：在仿射局部上，$\operatorname{Spec}A\to\operatorname{Spec}B$ 的像恰好是 $V(\ker(B\to A))$，这是交换代数的基本事实。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 忽略证明分离性 | 固有性要求“分离+有限型+泛闭”，三者缺一不可。 |
| 试图用赋值判别法证明泛闭性 | 对有限态射，直接证明像是闭集更简单。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite

open AlgebraicGeometry

-- 有限态射是固有的
theorem finite_implies_proper {X Y : Scheme} (f : X ⟶ Y) [Finite f] : Proper f :=
  sorry
```

---

## 习题 II.4.2 — 分离性判别：稠密开集上相等的态射必相等

### 题号与精确引用

**Hartshorne II.4.2**

### 问题重述

设 $S$ 为概形，$X$ 为 $S$ 上的既约概形，$Y$ 为 $S$ 上的分离概形。设 $f,g$ 是两个 $S$-态射 $X\to Y$，且它们在 $X$ 的某个稠密开子集 $U\subseteq X$ 上相同。证明 $f=g$。并举例说明：
(a) 若 $X$ 非既约，结论不成立；
(b) 若 $Y$ 非分离，结论不成立。

### 详细解答

**正命题**：考虑乘积态射 $(f,g):X\to Y\times_S Y$。因 $Y$ 分离，对角线 $\Delta:Y\to Y\times_S Y$ 是闭浸入。令 $Z=(f,g)^{-1}(\Delta(Y))\subseteq X$。因闭浸入在基变换下稳定（II.3.6），$Z\to X$ 是闭浸入。拓扑上，$Z$ 恰好是使 $f(x)=g(x)$ 的点集；由假设 $U\subseteq Z$，且 $U$ 稠密，故 $Z=X$（作为拓扑空间）。

于是 $(f,g)$ 穿过 $Y$ 的对角线，即 $f$ 与 $g$ 作为连续映射相同。还需验证层映射相同：层映射 $f^\#,g^\#:\mathcal{O}_Y\to f_*\mathcal{O}_X$ 在 $U$ 上相同。因 $X$ 既约，对任意开集 $W\subseteq X$，限制映射 $\mathcal{O}_X(W)\to\mathcal{O}_X(W\cap U)$ 是单射（II.4.2 证明中的引理：既约概形的稠密开子集上的限制是单的）。由层的性质，$f^\#$ 与 $g^\#$ 在整个 $X$ 上相同。故 $f=g$。∎

**反例 (a) — $X$ 非既约**：令 $X=Y=\operatorname{Spec}k[x,y]/(x^2,xy)$（原点的“fat point”）。设 $f=\operatorname{id}$，$g$ 由 $x\mapsto 0$ 诱导（即消去幂零部分）。$f$ 与 $g$ 在稠密开集 $D(y)$（即去掉原点）上相同，但显然 $f\neq g$（在茎 $(x,y)$ 处层映射不同）。

**反例 (b) — $Y$ 非分离**：令 $Y$ 为“带双原点的仿射直线”（the affine line with two origins），$X$ 为通常的 $\mathbb{A}^1_k$。设 $f,g:X\to Y$ 分别是把 $\mathbb{A}^1_k$ 映入 $Y$ 的两个不同拷贝的 obvious 开浸入。它们在去掉原点后相同，但把原点映到 $Y$ 的两个不同原点，故 $f\neq g$。∎

### 关键概念提示

- 这一结论是 **Hausdorff 空间中“连续映射在稠密集上相等则相等”** 的概形版本。
- **既约条件** 保证了层映射可由其在稠密开集上的限制唯一决定。
- **分离条件** 保证了“相等点集”是闭的，从而若包含稠密集则等于全空间。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 只证连续映射相同而忽略层映射 | 必须验证 $f^\#=g^\#$，这正是既约条件进入的地方。 |
| 反例 (a) 中选取的环不含幂零元 | 必须构造有非平凡幂零元的环。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Scheme

open AlgebraicGeometry

-- 既约 + 分离 ⇒ 稠密开集上相等的态射相等
theorem separated_reduced_morphism_equality
    {S X Y : Scheme} (f g : X ⟶ Y)
    [IsReduced X] [Separated Y]
    (U : X.Opens) (hU : Dense U.1)
    (heq : f ∣_ U = g ∣_ U) : f = g :=
  sorry
```

---

## 习题 II.4.3 — 分离概形中仿射开集的交仍是仿射的

### 题号与精确引用

**Hartshorne II.4.3**

### 问题重述

设 $X$ 是仿射概形 $S$ 上的分离概形。设 $U,V\subseteq X$ 是两个仿射开子集。证明 $U\cap V$ 也是仿射的。并举例说明当 $X$ 不分离时结论可能不成立。

### 详细解答

考虑对角线 $\Delta:X\to X\times_S X$。因 $X$ 分离，$\Delta$ 是闭浸入。由乘积的拓扑，$U\times_S V$ 是 $X\times_S X$ 中的仿射开集（同构于 $U\times V$）。而
$$U\cap V=\Delta^{-1}(U\times_S V).$$
因闭浸入在基变换下稳定（II.3.6），$\Delta$ 限制到 $U\cap V\to U\times_S V$ 仍是闭浸入。闭浸入的像所在的概形是仿射的（II.3.11(b)），而 $U\cap V$ 同构于该闭子概形，故 $U\cap V$ 仿射。∎

**反例**：取 $X$ 为“带双原点的仿射直线”。设 $U,V$ 分别是包含第一个原点和第二个原点的通常仿射直线（均同构于 $\mathbb{A}^1_k$），且它们在非原点处重合。则 $U\cap V\cong\mathbb{A}^1_k\setminus\{0\}$，这不是仿射的（由 II.1.3）。∎

### 关键概念提示

- $U\cap V=\Delta^{-1}(U\times_S V)$ 是分离性的几何核心：两个仿射开集的“交”可嵌入到它们的乘积中。
- 闭子概形 of 仿射概形必仿射，这是 II.3.11(b) 的内容。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 未验证 $U\times_S V$ 是仿射的 | $S$ 仿射时，$U\times_S V\cong\operatorname{Spec}(A\otimes_B C)$ 是仿射的。 |
| 反例选取的 $U\cap V$ 实际上是仿射的 | 必须保证交集确实是 $\mathbb{A}^1\setminus\{0\}$。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Scheme

open AlgebraicGeometry

-- 分离概形中两个仿射开集的交仍是仿射的
theorem intersection_of_affine_opens_is_affine
    {S X : Scheme} [IsAffine S] [Separated X]
    (U V : X.Opens) (hU : IsAffineOpen U.1) (hV : IsAffineOpen V.1) :
    IsAffineOpen (U ⊓ V).1 :=
  sorry
```

---

## 习题 II.4.4 — 固有像的固有性

### 题号与精确引用

**Hartshorne II.4.4**

### 问题重述

设 $f:X\to Y$ 是 Noetherian 概形 $S$ 上的分离有限型态射。设 $Z\subseteq X$ 是 $S$-固有的闭子概形。证明 $f(Z)$ 在 $Y$ 中是闭的，且赋予像子概形结构后，$f(Z)$ 也是 $S$-固有的。

### 详细解答

因 $Z\to S$ 固有且 $Y\to S$ 分离，复合 $Z\hookrightarrow X\xrightarrow{f}Y$ 是固有态射（固有性的复合与稳定性质：分离有限型的复合仍分离有限型；闭浸入固有（II.4.1），固有态射的复合固有；或直接用泛闭性）。

设 $i:Z\to X$ 为闭浸入，则 $f\circ i:Z\to Y$ 是固有的。固有态射是闭映射（因为泛闭 + 自身为闭），故 $(f\circ i)(Z)=f(Z)$ 是 $Y$ 中的闭子集。

赋予像子概形结构 $W=f(Z)$ 后，$Z\to W$ 是满射的固有态射（因为固有性的复合 $Z\to Y$ 可分解为 $Z\to W\hookrightarrow Y$，而 $W\hookrightarrow Y$ 是闭浸入（从而分离），由固有性的 cancellation 性质（若 $Z\to W\to Y$ 固有且 $W\to Y$ 分离，则 $Z\to W$ 固有），可知 $Z\to W$ 固有。但更直接地：$W\to S$ 是 $Z\to S$ 与 $Z\to W$ 的复合的“像”——实际上，$W\to S$ 是分离的（因为 $Y\to S$ 分离，$W\hookrightarrow Y$ 闭浸入，闭浸入的复合分离）；有限型显然。泛闭性：对任意 $S'\to S$，$W\times_S S'\to S'$ 的像等于 $Z\times_S S'\to S'$ 的像（因为 $Z\to W$ 满），而后者是闭的。故 $W\to S$ 固有。∎

### 关键概念提示

- **固有态射的像是闭的**：这是“泛闭”定义的直接推论（取基变换为恒等）。
- **像子概形结构**（image subscheme structure）由 II.3.11(d) 定义：它是使 $Z\to Y$ 穿过它的最小闭子概形。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 试图直接证明 $f(Z)\to S$ 泛闭而不利用 $Z\to S$ 的泛闭性 | 应利用 $Z\to W$ 的满射性将闭性传递下去。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Morphisms.Proper

open AlgebraicGeometry

-- 固有闭子概形的像仍是闭的且固有
theorem image_of_proper_is_proper
    {S X Y : Scheme} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [IsNoetherian S]
    (Z : ClosedImmersion X) [Proper Z.morphism]
    (W : ClosedImmersion Y) (hw : W.toRingHom_surjective) :
    IsClosedImmersion (f ≫ W.morphism) ∧ Proper W.morphism :=
  sorry
```

---

## 习题 II.4.5 — 赋值判别法（中心唯一性）

### 题号与精确引用

**Hartshorne II.4.5 (a), (b), (d)**

### 问题重述

设 $X$ 是域 $k$ 上的有限型整概形，函数域为 $K$。称 $K/k$ 的赋值环 $R$ 在 $X$ 上有中心 $x$，若 $R$ 支配局部环 $\mathcal{O}_{X,x}$。

(a) 若 $X$ 在 $k$ 上分离，则任何赋值环在 $X$ 上的中心（若存在）唯一。
(b) 若 $X$ 在 $k$ 上固有（proper），则每个赋值环在 $X$ 上都有唯一的中心。
(d) 若 $X$ 在 $k$ 上固有且 $k$ 代数闭，则 $\Gamma(X,\mathcal{O}_X)=k$。

### 详细解答

**(a) 分离 $\Rightarrow$ 中心唯一**

设 $R$ 有两个中心 $x_1,x_2\in X$。则有交换图：
$$\begin{array}{ccc}
\operatorname{Spec}K & \longrightarrow & X \\
\downarrow & & \downarrow \\
\operatorname{Spec}R & \longrightarrow & \operatorname{Spec}k
\end{array}$$
其中顶边的两个 $K$-点分别对应于 $x_1,x_2$（以及包含 $\mathcal{O}_{X,x_i}\hookrightarrow R$）。由分离性的赋值判别法（Theorem II.4.3），从 $\operatorname{Spec}R\to X$ 的提升至多一个。而 $x_1,x_2$ 都给出提升，故 $x_1=x_2$。∎

**(b) 固有 $\Rightarrow$ 中心存在且唯一**

存在性：由固有性的赋值判别法（Theorem II.4.7），对任意赋值环 $R$ 及上述交换图，存在唯一的提升 $\operatorname{Spec}R\to X$。该提升的像的闭点给出中心。唯一性由 (a) 给出。∎

**(d) 整体截面等于 $k$**

设 $a\in\Gamma(X,\mathcal{O}_X)$，则 $a\in K$（因 $X$ 整）。若 $a\notin k$，考虑 $t=1/a\in K$。因 $k$ 代数闭，$t$ 在 $k$ 上超越，故存在 $K/k$ 的赋值环 $R$ 使得 $t$ 在 $R$ 中非单位（即 $t\in\mathfrak m_R$），例如对 $k[t]$ 在素理想 $(t)$ 处局部化并取某个支配该局部化的赋值环。

由 (b)，$R$ 在 $X$ 上有唯一中心 $x$，即 $R$ 支配 $\mathcal{O}_{X,x}$。但 $a\in\mathcal{O}_{X,x}\subseteq R$，故 $1/t=a\in R$ 且 $t\in\mathfrak m_R$，这意味着 $t$ 与 $1/t$ 都在 $R$ 中，从而 $t$ 是单位，矛盾（因为 $t\in\mathfrak m_R$）。因此 $a\in k$。显然 $k\subseteq\Gamma(X,\mathcal{O}_X)$，故相等。∎

*注：II.4.5(c) 要求证明 (a)(b) 的逆，这是赋值判别法的深层应用，难度较高，本文件暂不展开，标记为待验证补充项。*

### 关键概念提示
- **赋值环的中心** 是代数几何中“极限点”的代数化：一般点对应 $K$ 的取值，特殊点对应极限位置。
- **赋值判别法** 将分离性/固有性的几何直观（极限唯一/极限存在且唯一）转化为赋值环的提升性质。
- (d) 的推广是：$k$-固有整概形的整体正则函数只能是常数，这推广了紧复流形上全纯函数为常数的经典结果。

### 常见错误警示
| 错误 | 纠正 |
|------|------|
| 将赋值判别法中的提升方向搞反 | 提升是从 $\operatorname{Spec}R$ 到 $X$，不是从 $X$ 到 $\operatorname{Spec}R$。 |
| 在 (d) 中直接断言 $a$ 在全局有界 | 需要显式构造一个使 $a$ 出现矛盾的赋值环。 |

### Lean4 代码占位
```lean4
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ValuativeCriterion

open AlgebraicGeometry

-- (a) 分离 ⇒ 赋值中心唯一（用赋值判别法）
theorem separated_valuative_center_unique
    {k X : Scheme} [IsIntegral X] [IsSeparated (X ⟶ Spec (CommRingCat.of k))]
    (K : Type*) [Field K] [Algebra k K] [IsFractionRing (Γ(X, ⊤)) K]
    (R : ValuationRing K) (hR : R.ring.Dominate (Γ(X, ⊤))) :
    ∃! x : X, R.ring.Dominate (X.presheaf.stalk x) :=
  sorry

-- (d) 固有 + k 代数闭 ⇒ 整体截面为 k
theorem proper_over_algClosed_global_sections
    {k X : Scheme} [IsIntegral X] [Proper (X ⟶ Spec (CommRingCat.of k))]
    [IsAlgClosed k] :
    Γ(X, ⊤) ≅ CommRingCat.of k :=
  sorry
```

---

**文档位置**: `docs/13-代数几何/Harvard-232br-习题解答/II.4-分离性与本征性.md`
**创建日期**: 2026-04-17
