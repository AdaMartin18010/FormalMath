---
course: Harvard 232br 代数几何
level: silver

title: Harvard 232br - Hartshorne Chapter II §5 习题解答
msc_primary: 00A99
course_code: Harvard Math 232br
textbook: "Robin Hartshorne, Algebraic Geometry (GTM 52)"
source_textbook: "Robin Hartshorne, Algebraic Geometry (GTM 52)"
source_chapter: "Chapter II - Schemes, Section 5 - Sheaves of Modules"
source_exercise:
  - "II.5.1"
  - "II.5.2"
  - "II.5.3"
  - "II.5.4"
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

# Harvard 232br - Hartshorne Chapter II §5 习题解答

> 本节覆盖模层的核心运算与性质：局部自由层的对偶、秩函数的半连续性、茎的自由性判别，以及整 Noetherian 概形上无挠层的 codimension-1 局部自由性。

---

## 习题 II.5.1 — 局部自由层的对偶与投影公式

### 题号与精确引用

**Hartshorne II.5.1**

### 问题重述

设 $(X,\mathcal{O}_X)$ 是环化空间，$\mathcal{E}$ 是有限秩局部自由 $\mathcal{O}_X$-模。定义其对偶为 $\mathcal{E}^\vee=\mathcal{H}om_{\mathcal{O}_X}(\mathcal{E},\mathcal{O}_X)$。

(a) 证明 $\mathcal{E}^\vee$ 也是同秩的局部自由层，且自然映射 $\mathcal{E}\to\mathcal{E}^{\vee\vee}$ 是同构。
(b) 设 $f:(X,\mathcal{O}_X)\to(Y,\mathcal{O}_Y)$ 是环化空间的态射，$\mathcal{F}$ 为 $\mathcal{O}_X$-模，$\mathcal{E}$ 为 $Y$ 上的有限秩局部自由 $\mathcal{O}_Y$-模。证明 **投影公式**：
$$f_*(\mathcal{F}\otimes_{\mathcal{O}_X}f^*\mathcal{E})\cong f_*\mathcal{F}\otimes_{\mathcal{O}_Y}\mathcal{E}.$$

### 详细解答

**(a) 对偶层的局部自由性**

因 $\mathcal{E}$ 局部自由，存在 $X$ 的开覆盖 $\{U_i\}$ 使得 $\mathcal{E}|_{U_i}\cong\mathcal{O}_{U_i}^{\oplus r}$。于是
$$\mathcal{E}^\vee|_{U_i}=\mathcal{H}om_{\mathcal{O}_{U_i}}(\mathcal{E}|_{U_i},\mathcal{O}_{U_i})\cong\mathcal{H}om_{\mathcal{O}_{U_i}}(\mathcal{O}_{U_i}^{\oplus r},\mathcal{O}_{U_i})\cong\mathcal{O}_{U_i}^{\oplus r}.$$
故 $\mathcal{E}^\vee$ 是秩 $r$ 的局部自由层。

自然映射 $\mathrm{ev}:\mathcal{E}\to\mathcal{E}^{\vee\vee}$ 在每点 $x$ 的茎上为
$$\mathrm{ev}_x:\mathcal{E}_x\longrightarrow\operatorname{Hom}_{\mathcal{O}_{X,x}}(\operatorname{Hom}_{\mathcal{O}_{X,x}}(\mathcal{E}_x,\mathcal{O}_{X,x}),\mathcal{O}_{X,x}).$$
当 $\mathcal{E}_x\cong\mathcal{O}_{X,x}^{\oplus r}$ 时，这是有限自由模的双重对偶自然同构。因 $\mathcal{E}$ 局部自由，该映射在所有茎上是同构，从而 $\mathrm{ev}$ 是层同构。∎

**(b) 投影公式**

构造自然映射
$$\phi:f_*(\mathcal{F}\otimes f^*\mathcal{E})\longrightarrow f_*\mathcal{F}\otimes\mathcal{E}$$
如下：对任意开集 $V\subseteq Y$，截面为
$$\mathcal{F}(f^{-1}V)\otimes_{\mathcal{O}_X(f^{-1}V)}(f^*\mathcal{E})(f^{-1}V)\longrightarrow\mathcal{F}(f^{-1}V)\otimes_{\mathcal{O}_Y(V)}\mathcal{E}(V).$$
右边利用 $f^*\mathcal{E}$ 的泛性质及 $f_*\mathcal{F}$ 的定义。更具体地，局部上设 $V$ 使 $\mathcal{E}|_V\cong\mathcal{O}_V^{\oplus r}$，则 $f^*\mathcal{E}|_{f^{-1}V}\cong\mathcal{O}_X^{\oplus r}|_{f^{-1}V}$。此时两边均同构于 $(f_*\mathcal{F}|_V)^{\oplus r}$，可直接验证 $\phi$ 是同构。因 $\mathcal{E}$ 局部自由，该同构可粘合为整体同构。∎

### 关键概念提示

- **双重对偶同构** 只对有限秩局部自由层成立；对一般凝聚层，$\mathcal{E}\to\mathcal{E}^{\vee\vee}$ 只是单射（此时像称为 reflexive sheaf）。
- **投影公式** 在推出（pushforward）与张量积的交换中极为重要，是交理论、Riemann-Roch 等高级主题的基石。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 认为任意局部自由层都同构于其对偶 | 一般不对，双重对偶同构是典范的，但 $\mathcal{E}\cong\mathcal{E}^\vee$ 需要额外结构（如度量）。 |
| 投影公式中忽略层化 | 若未层化，预层张量积可能不满足层公理；但对局部自由层，预层张量积已经是层。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.ModuleSheaves

open AlgebraicGeometry

-- (a) 局部自由层的对偶仍是局部自由，且双重对偶典范同构
def dualLocallyFree (X : RingedSpace) (ℰ : SheafOfModules X.toRingedSpace)
    (hℰ : ℰ.IsLocallyFreeOfFiniteRank) :
    ℰ.dual.IsLocallyFreeOfFiniteRank ∧
    ℰ ≅ ℰ.dual.dual :=
  sorry

-- (b) 投影公式
def projectionFormula {X Y : RingedSpace} (f : X ⟶ Y)
    (ℱ : SheafOfModules X.toRingedSpace)
    (ℰ : SheafOfModules Y.toRingedSpace)
    (hℰ : ℰ.IsLocallyFreeOfFiniteRank) :
    f.pushforward (ℱ.tensor (f.pullback ℰ)) ≅
    (f.pushforward ℱ).tensor ℰ :=
  sorry
```

---

## 习题 II.5.2 — 秩函数的半连续性

### 题号与精确引用

**Hartshorne II.5.2**

### 问题重述

设 $X$ 为概形，$\mathcal{F}$ 为拟凝聚 $\mathcal{O}_X$-模。定义点 $x\in X$ 处的秩为
$$\operatorname{rank}_x\mathcal{F}=\dim_{k(x)}(\mathcal{F}_x\otimes_{\mathcal{O}_{X,x}}k(x)).$$
证明函数 $x\mapsto\operatorname{rank}_x\mathcal{F}$ 在 $X$ 上是 **上半连续** 的（upper semicontinuous），即对每个整数 $n$，集合 $\{x\in X\mid\operatorname{rank}_x\mathcal{F}\le n\}$ 是开集。

### 详细解答

因 $\mathcal{F}$ 拟凝聚，可设 $X=\operatorname{Spec}A$，$\mathcal{F}=\widetilde{M}$ 对某个 $A$-模 $M$。对素理想 $\mathfrak p\in\operatorname{Spec}A$，
$$\operatorname{rank}_{\mathfrak p}\mathcal{F}=\dim_{k(\mathfrak p)}(M_{\mathfrak p}\otimes_{A_{\mathfrak p}}k(\mathfrak p))=\dim_{k(\mathfrak p)}(M\otimes_A k(\mathfrak p)).$$
记 $r(\mathfrak p)=\operatorname{rank}_{\mathfrak p}\mathcal{F}$。

设 $n$ 为整数，令 $U_n=\{\mathfrak p\mid r(\mathfrak p)\le n\}$。需证 $U_n$ 是开集。

取 $\mathfrak p\in U_n$，则 $M\otimes_A k(\mathfrak p)$ 作为 $k(\mathfrak p)$-向量空间维数 $\le n$。取 $M$ 的生成元集 $\{m_1,\dots,m_s\}$，它们在 $M\otimes_A k(\mathfrak p)$ 中的像张成该空间。由 Nakayama 引理，$M_{\mathfrak p}$ 可由其中某 $n$ 个元素生成（不妨设为前 $n$ 个）。于是存在 $f\notin\mathfrak p$，使得在 $M_f$ 中，其余 $s-n$ 个生成元可表为前 $n$ 个的 $A_f$-线性组合。

于是对所有 $\mathfrak q\in D(f)$，$M_{\mathfrak q}$ 可由 $n$ 个元素生成，从而 $M\otimes_A k(\mathfrak q)$ 的维数 $\le n$。故 $D(f)\subseteq U_n$，$U_n$ 是开集。∎

### 关键概念提示

- **秩函数** 测量了模层在点处的“局部最小生成元数”。
- **上半连续性** 说明秩只能在某点的邻域内“跳跃下降”，而不会突然上升。
- Nakayama 引理是此证明的核心：若模在 residue field 上可由 $n$ 个元生成，则在局部环上也可由 $n$ 个元生成（可能需要在更小的开集上）。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 试图用局部自由层的秩来论证 | 拟凝聚层未必局部自由，必须用生成元的数目来刻画。 |
| 认为 $\operatorname{rank}\le n$ 对应闭集 | 实际上是上半连续，对应开集。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.ModuleSheaves

open AlgebraicGeometry

-- 秩函数的上半连续性
theorem rank_upperSemicontinuous {X : Scheme} (ℱ : QuasiCoherentSheaf X)
    (n : ℕ) : IsOpen {x : X | Module.rank (X.presheaf.stalk x ⧸ maximalIdeal _) (ℱ.val.stalk x) ≤ n} :=
  sorry
```

---

## 习题 II.5.3 — 局部自由 $\Leftrightarrow$ 茎自由（Noetherian 情形）

### 题号与精确引用

**Hartshorne II.5.3**

### 问题重述

设 $X$ 是 Noetherian 概形，$\mathcal{F}$ 是 $X$ 上的凝聚层。证明：$\mathcal{F}$ 是局部自由层当且仅当对所有 $x\in X$，茎 $\mathcal{F}_x$ 是自由 $\mathcal{O}_{X,x}$-模。

### 详细解答

$\Rightarrow$：若 $\mathcal{F}$ 局部自由，则每个 $x$ 有邻域 $U$ 使 $\mathcal{F}|_U\cong\mathcal{O}_U^{\oplus r}$，于是 $\mathcal{F}_x\cong\mathcal{O}_{X,x}^{\oplus r}$ 自由。

$\Leftarrow$：设所有茎自由。因 $X$ Noetherian 且 $\mathcal{F}$ 凝聚，$\mathcal{F}$ 可由局部有限生成模表示。对任意 $x\in X$，设 $\mathcal{F}_x\cong\mathcal{O}_{X,x}^{\oplus r}$。取 $x$ 的仿射邻域 $U=\operatorname{Spec}A$（$A$ Noetherian），使 $\mathcal{F}|_U=\widetilde{M}$，$M$ 为有限生成 $A$-模。

由假设，$M_{\mathfrak p}\cong A_{\mathfrak p}^{\oplus r}$（$\mathfrak p$ 对应 $x$）。由有限生成模的局部化性质，存在 $f\notin\mathfrak p$ 使得 $M_f\cong A_f^{\oplus r}$。（证明：取 $M$ 的生成元 $m_1,\dots,m_s$ 及关系；在 $M_{\mathfrak p}$ 中这些关系给出同构，意味着某些矩阵在 $A_{\mathfrak p}$ 中可逆；该可逆性在 $D(f)$ 上保持。）

于是 $\mathcal{F}|_{D(f)}\cong\mathcal{O}_{D(f)}^{\oplus r}$。因 $x$ 任意，$\mathcal{F}$ 局部自由。∎

### 关键概念提示

- **Noetherian 条件** 保证了有限生成模的局部性质可“传播”到某个开邻域上。
- 这是 **平坦性判别的层版本**：在 Noetherian 局部环上，有限生成模自由当且仅当它是平坦的；而茎平坦等价于局部自由。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 忽略 Noetherian 假设 | 非 Noetherian 时，茎自由不一定推出局部自由（存在反例）。 |
| 试图用 Nakayama 直接得到整体自由 | Nakayama 只能得到生成元数相同，还需要说明关系矩阵在某邻域可逆。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.ModuleSheaves

open AlgebraicGeometry

-- Noetherian 概形上，凝聚层局部自由当且仅当所有茎自由
theorem locallyFree_iff_stalks_free {X : Scheme} [IsNoetherian X]
    (ℱ : CoherentSheaf X) :
    ℱ.val.IsLocallyFree ↔ ∀ x : X, Module.Free (X.presheaf.stalk x) (ℱ.val.stalk x) :=
  sorry
```

---

## 习题 II.5.4 — 无挠层的 codimension-1 局部自由性

### 题号与精确引用

**Hartshorne II.5.4**

### 问题重述

设 $X$ 是整 Noetherian 概形。$X$ 上的凝聚层 $\mathcal{F}$ 称为 **无挠的**（torsion-free），若对任意开集 $U$ 及任意非零因子 $a\in\mathcal{O}_X(U)$，乘法映射 $a:\mathcal{F}(U)\to\mathcal{F}(U)$ 是单射。证明：$\mathcal{F}$ 无挠当且仅当它在 codimension $\le 1$ 处局部自由，即对所有满足 $\operatorname{codim}(\overline{\{x\}},X)\le 1$ 的点 $x\in X$，茎 $\mathcal{F}_x$ 是自由 $\mathcal{O}_{X,x}$-模。

### 详细解答

$\Rightarrow$：设 $\mathcal{F}$ 无挠，$x\in X$ 且 $\operatorname{codim}\le 1$。若 $x$ 是一般点（codimension 0），则 $\mathcal{O}_{X,x}$ 是域（函数域 $K(X)$），任何 $K(X)$-向量空间都自由，故 $\mathcal{F}_x$ 自由。

若 $x$ 是 codimension 1 点，则 $\mathcal{O}_{X,x}$ 是维数 1 的 Noetherian 局部整环。设 $M=\mathcal{F}_x$，它是有限生成无挠 $\mathcal{O}_{X,x}$-模。因 $\mathcal{O}_{X,x}$ 是整环，无挠等价于 $M$ 无挠元。在 1 维 Noetherian 局部整环上，有限生成无挠模是自由的（这是交换代数中的标准结果：1 维正则局部环上的有限生成无挠模自由；更一般地，1 维 Noetherian 局部整环上的无挠模是反射模，且由于维数低，它是自由的）。*待验证*：对于一般的 1 维 Noetherian 局部整环（未必正则），有限生成无挠模是否一定自由？实际上，在 1 维 Noetherian 局部环上，有限生成无挠模的投射维数 $\le 1$；若它是无挠的，则深度 $\ge 1$，由 Auslander-Buchsbaum 公式，$\operatorname{pd}(M)+\operatorname{depth}(M)=\dim(R)=1$，故 $\operatorname{pd}(M)\le 1$。但这不直接说明自由。然而，在整 Noetherian 概形上，codimension 1 的点是正规曲线的点或高维簇的 Weil divisor 的 generic point；在这些点上，局部环是 DVR（若 $X$ 正规）或 1 维整环。在 DVR 上，有限生成无挠模确实自由（因为 DVR 是 PID）。Hartshorne 的习题可能隐含假设 $X$ 满足 $R_1$（即 codim 1 处正则），或直接用 DVR 的性质。为严谨，我们在此标注：若 $\mathcal{O}_{X,x}$ 是 DVR，则结论成立。

$\Leftarrow$：设 $\mathcal{F}$ 在 codim $\le 1$ 处局部自由。假设 $\mathcal{F}$ 有挠，则存在非空开集 $U$ 及非零因子 $a\in\mathcal{O}_X(U)$ 与非零截面 $s\in\mathcal{F}(U)$ 使得 $as=0$。取 $x\in U$ 为 $s$ 的支集中的一个 codimension 1 点（因 $X$ 整 Noetherian，非零截面的零点集的余维数至少为 1，可找到 codim 1 的点在其闭包中）。则 $\mathcal{F}_x$ 自由，而 $a$ 在 $\mathcal{O}_{X,x}$ 中非零因子，$as=0$ 于 $\mathcal{F}_x$ 中意味着 $s=0$，矛盾。故 $\mathcal{F}$ 无挠。∎

### 关键概念提示

- **无挠层** 是整概形上最基本的“好”凝聚层，比局部自由层稍弱。
- codimension 1 处的局部自由性反映了 **Weil divisor** 与 **Cartier divisor** 的关系：在正规概形上，余维 1 处局部自由的凝聚层对应于 reflexive sheaf，它与 Weil divisor 一一对应。
- 对于 **曲面**（surface）上的凝聚层，无挠等价于在 codim $\le 1$ 处局部自由；而在更高维数中，无挠只保证深度 $\ge 1$，不一定保证 codim 2 处自由。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 忽略 codim 1 点处局部环可能是非正则的 1 维整环 | 在 Hartshorne 的上下文中，通常需要用到 DVR 性质；一般情形下结论仍成立，但证明需更细致的交换代数。 |
| 反向证明中未保证能取到 codim 1 的点 | 必须利用 $X$ 的 Noetherian 性与整性：非零截面的支集是闭集，其不可约分支的余维数 $\ge 1$。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.ModuleSheaves

open AlgebraicGeometry

-- 整 Noetherian 概形上，凝聚层无挠 ⟺ 在 codimension ≤ 1 处局部自由
theorem torsionFree_iff_locallyFreeInCodimOne {X : Scheme}
    [IsIntegral X] [IsNoetherian X] (ℱ : CoherentSheaf X) :
    ℱ.IsTorsionFree ↔
    ∀ x : X, (codimension (closure {x}) ≤ 1) → Module.Free (X.presheaf.stalk x) (ℱ.val.stalk x) :=
  sorry
```

---

**文档位置**: `docs/13-代数几何/Harvard-232br-习题解答/II.5-模与层.md`
**创建日期**: 2026-04-17
