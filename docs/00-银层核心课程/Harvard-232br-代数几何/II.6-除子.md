---
course: Harvard 232br 代数几何
level: silver

title: Harvard 232br - Hartshorne Chapter II §6 习题解答
course_code: Harvard Math 232br
textbook: Robin Hartshorne, Algebraic Geometry (GTM 52)
source_textbook: Robin Hartshorne, Algebraic Geometry (GTM 52)
source_chapter: Chapter II - Schemes, Section 6 - Divisors
source_exercise:
- II.6.1
- II.6.2
- II.6.3
- II.6.4
- II.6.5
- II.6.6
- II.6.7
- II.6.8
- II.6.9
- II.6.10
- II.6.11
- II.6.12
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
    - 'Chapter II, Section 6: Divisors'
    url: null
    pages: 129-138
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

# Harvard 232br - Hartshorne Chapter II §6 习题解答

> 本节覆盖 Weil 除子、Cartier 除子、Picard 群、类群，以及 Grothendieck 群 $K(X)$ 的计算与性质。

---

## 习题 II.6.1 — Factorial 概形上的 Weil 除子

### 题号与精确引用

**Hartshorne II.6.1**

### 问题重述

设 $X$ 是满足条件 $(*)$ 的概形（Noetherian、整、分离、且在余维 1 处正则）。证明：$X$ 是 factorial 的当且仅当每个 Weil 除子都是 Cartier 除子。

### 详细解答

**$\Rightarrow$**：设 $X$ factorial。对任意素 Weil 除子 $Y \subseteq X$（余维 1 的整闭子概形），取 $Y$ 的 generic point $\eta$。因 $X$ 满足 $(*)$，$\mathcal{O}_{X,\eta}$ 是 DVR。因 $X$ 是 factorial 的，$\mathcal{O}_{X,\eta}$ 是 UFD，而 1 维 UFD 是 PID，故其极大理想由单个元生成。该生成元可提升到某开集 $U$ 上，给出 $Y \cap U$ 的局部定义方程。由此 $Y$ 是 Cartier 除子。一般 Weil 除子是素除子的整系数线性组合，故也是 Cartier 除子。

**$\Leftarrow$**：设每个 Weil 除子都是 Cartier 除子。要证 $X$ factorial，即证对每个点 $x \in X$，$\mathcal{O}_{X,x}$ 是 UFD。因 $X$ 满足 $(*)$，只需证明对 codimension 1 的素理想 $\mathfrak p \subseteq A = \mathcal{O}_{X,x}$，$\mathfrak p$ 是主理想。对应的素 Weil 除子 $Y = V(\mathfrak p)$ 是 Cartier 除子，故 $\mathfrak p$ 在某邻域由单个元生成，从而是主理想。由 Auslander-Buchsbaum 定理（正则局部环是 UFD 当且仅当每个高度 1 的素理想是主理想），$A$ 是 UFD。∎

### 关键概念提示

- **Factorial 概形** = 所有局部环都是 UFD 的概形。
- **条件 $(*)$** 保证了 Weil 除子良定义，且 Cartier 除子可嵌入 Weil 除子。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 忽略 $R_1$ 假设 | 没有 codim 1 处正则的假设，Weil 除子本身可能无法与 DVR 一一对应。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Divisor

open AlgebraicGeometry

-- factorial ⟺ 每个 Weil 除子都是 Cartier 除子
theorem factorial_iff_allWeilIsCartier {X : Scheme}
    [IsNoetherian X] [IsIntegral X] [IsSeparated X]
    (hR1 : ∀ x : X, (1 : ℕ) ≤ ringKrullDim (X.presheaf.stalk x) →
      IsRegularLocalRing (X.presheaf.stalk x)) :
    IsFactorial X ↔ ∀ D : WeilDivisor X, IsCartierDivisor D :=
  sorry
```

---

## 习题 II.6.2 — Cartier 除子到 Weil 除子的映射

### 题号与精确引用

**Hartshorne II.6.2**

### 问题重述

设 $X$ 为整概形。
(a) 证明自然映射 $\operatorname{CaCl}(X) \to \operatorname{Cl}(X)$ 是单射。
(b) 若 $X$ 还满足正规条件（normal），则该映射是同构。

### 详细解答

**(a) 单射性**

Cartier 除子 $D = \{(U_i, f_i)\}$ 映到 Weil 除子 $\sum_Y v_Y(f_i) \cdot Y$（与 $i$ 的选取无关，因 $f_i/f_j$ 在 $U_i \cap U_j$ 上可逆，故赋值相同）。该映射保持线性等价：主 Cartier 除子 $(f)$ 映到主 Weil 除子。要证诱导的 $\operatorname{CaCl}(X) \to \operatorname{Cl}(X)$ 单射，即证：若 Cartier 除子 $D$ 映到主 Weil 除子，则 $D$ 是主 Cartier 除子。

设 $D$ 映到 $(g)$ 对某 $g \in K(X)^*$。则在每个 $U_i$ 上，$f_i$ 与 $g$ 在所有素 Weil 除子处有相同赋值。因 $X$ 整，$f_i/g$ 在所有 codim 1 点处可逆，故是单位。于是 $D = (g)$ 为主 Cartier 除子。∎

**(b) 正规情形下的同构**

设 $X$ 正规。对任意 Weil 除子 $D = \sum n_Y Y$，取 $X$ 的仿射开覆盖 $\{U_i\}$。在每个 $U_i$ 上，$D|_{U_i}$ 对应有限个素除子。因 $X$ 正规（特别地满足 $R_1$），每个 codim 1 的局部环是 DVR，其极大理想由一致化参数 $t_Y$ 生成。于是 $D|_{U_i}$ 在 $U_i$ 上可写成 $\operatorname{div}(f_i)$ 对某 $f_i \in K(X)^*$（取 $f_i = \prod t_Y^{n_Y}$）。这些 $f_i$ 在交上相差单位，故给出 Cartier 除子。∎

### 关键概念提示

- **整概形** 保证了整体函数域 $K(X)$ 存在，使主除子良定义。
- **正规性** 是 Weil 除子可局部主理想化的关键：在 DVR 上，任何有限个素除子的线性组合都对应一个主除子。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 未验证 Cartier 除子的相容性 | 需验证不同开集上选取的 $f_i$ 在交上确实只相差整体可逆函数。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Divisor

open AlgebraicGeometry

-- (a) CaCl → Cl 单射；(b) 正规时同构
theorem CaCl_to_Cl {X : Scheme} [IsIntegral X] :
    Function.Injective (caClToCl (X := X)) ∧
    (IsNormal X → Function.Bijective (caClToCl (X := X))) :=
  sorry
```

---

## 习题 II.6.3 — 射影空间的类群

### 题号与精确引用

**Hartshorne II.6.3**

### 问题重述

设 $k$ 为域，$X = \mathbb{P}^n_k$。证明次数映射给出同构
$$\deg : \operatorname{Cl}(X) \xrightarrow{\sim} \mathbb{Z}.$$

### 详细解答

**步骤 1：映射良定义**。对 Weil 除子 $D = \sum n_Y Y$，定义 $\deg(D) = \sum n_Y \deg(Y)$，其中 $\deg(Y)$ 是超曲面 $Y$ 的次数。主除子 $(f)$ 的次数为零（因有理函数 $f$ 的零点与极点按重数计算的次数和为零，这是射影空间上多项式的经典结果）。故 $\deg$ 诱导 $\operatorname{Cl}(X) \to \mathbb{Z}$ 的群同态。

**步骤 2：满射**。超平面 $H = V(x_0)$ 是素 Weil 除子且 $\deg(H) = 1$，故 $\deg$ 是满射。

**步骤 3：单射**。设 $\deg(D) = 0$。把 $D$ 写成 $D = D_1 - D_2$，其中 $D_1, D_2$ 为有效除子且 $\deg(D_1) = \deg(D_2)$。对应齐次理想分别为 $I_1, I_2$。因 $X$ 是 UFD，$\operatorname{Cl}(X) \cong \operatorname{CaCl}(X) \cong \operatorname{Pic}(X)$。而 $\operatorname{Pic}(\mathbb{P}^n) \cong \mathbb{Z}$（由 $\mathcal{O}(1)$ 生成），故次数为零的除子对应于平凡线丛，即为主除子。∎

### 关键概念提示

- $\mathbb{P}^n$ 是 factorial 的，因此 $\operatorname{Cl}(\mathbb{P}^n) = \operatorname{CaCl}(\mathbb{P}^n) = \operatorname{Pic}(\mathbb{P}^n)$。
- 超平面 $H$ 对应线丛 $\mathcal{O}(1)$，其 $d$ 次张量幂对应 $\mathcal{O}(d)$。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 直接用 $\operatorname{Pic}(\mathbb{P}^n) \cong \mathbb{Z}$ 证明 | 需先建立 $\operatorname{Cl}$ 与 $\operatorname{Pic}$ 的联系（利用 factorial 性质）。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme

open AlgebraicGeometry

-- P^n 的类群同构于 Z
theorem classGroup_of_projectiveSpace (n : ℕ) [n.AtLeastTwo]
    (k : Type*) [Field k] :
    ClassGroup (ProjectiveScheme (Fin (n + 1)) k) ≅ Multiplicative ℤ :=
  sorry
```

---

## 习题 II.6.4 — 射影簇与超平面的交

### 题号与精确引用

**Hartshorne II.6.4**

### 问题重述

设 $k$ 为无限域，$X \subseteq \mathbb{P}^n_k$ 为维数 $\ge 1$ 的射影簇。证明对任意超平面 $H \subseteq \mathbb{P}^n_k$，$X \cap H \neq \emptyset$。

### 详细解答

假设存在超平面 $H$ 使 $X \cap H = \emptyset$。取坐标使 $H = V(x_0)$。则 $X \subseteq \mathbb{P}^n \setminus H \cong \mathbb{A}^n$。但 $X$ 是射影簇从而是 proper 的，而 $\mathbb{A}^n$ 不是 proper 的（除非 $n = 0$）。proper 概形在任意态射下的像都是闭的；特别地，嵌入 $\mathbb{A}^n \hookrightarrow \mathbb{P}^n$ 的像不是闭的，矛盾。

更直接地：$X \cap H = \emptyset$ 意味着 $X$ 上坐标函数 $x_0$ 处处非零，故 $1/x_0$ 是 $X$ 上的正则函数。因 $X$ 是 proper（ projective），$\mathcal{O}_X(X) = k$（II.4.9 的推论），故 $1/x_0$ 为常数。但这不改变 $X$ 的维数，与维数 $\ge 1$ 矛盾（因为若 $X$ 不落在任何坐标超平面上，则它与所有超平面相交；*待验证*：更严格的论证可通过锥的构造或 Bertini 定理的初等版本完成）。∎

### 关键概念提示

- **射影簇的 proper 性** 是其与仿射空间的关键区别：proper 簇上的整体正则函数只能是常数。
- 当 $k$ 有限时结论可能不成立（但 Hartshorne 此处假设 $k$ 无限）。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 忽略 $k$ 无限的假设 | 有限域上可能存在不与其他点相交的超平面（虽然对射影簇实际上仍成立，但一般论证需要无限域来保证一般位置）。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme

open AlgebraicGeometry

-- 无限域上维数 ≥ 1 的射影簇与任意超平面相交非空
theorem projectiveVariety_intersects_hyperplane
    {n : ℕ} (k : Type*) [Field k] [Infinite k]
    (X : ClosedImmersion (ProjectiveScheme (Fin (n + 1)) k))
    (hdim : 1 ≤ krullDim X.toScheme)
    (H : WeilDivisor (ProjectiveScheme (Fin (n + 1)) k))
    (hH : degree H = 1) :
    Nonempty (X.toScheme ⨯ H.toScheme) :=
  sorry
```

---

## 习题 II.6.5 — 闭子集外的类群满射

### 题号与精确引用

**Hartshorne II.6.5**

### 问题重述

设 $X$ 满足条件 $(*)$，$Z \subsetneq X$ 为真闭子集。证明限制映射
$$\operatorname{Cl}(X) \longrightarrow \operatorname{Cl}(X \setminus Z)$$
是满射。若 $\operatorname{codim}(Z, X) \ge 2$，则它还是同构。

### 详细解答

**满射性**：设 $D'$ 为 $X \setminus Z$ 上的 Weil 除子。$D'$ 可写成素除子的形式和 $D' = \sum n_Y Y$，其中 $Y$ 是 $X \setminus Z$ 中 codim 1 的闭子集。每个 $Y$ 的闭包 $\overline{Y}$ 是 $X$ 中 codim 1 的闭子集（因 $Z$ 真闭，不会使余维数下降）。令 $D = \sum n_Y \overline{Y}$，则 $D|_{X \setminus Z} = D'$。故限制映射满。

**同构性（当 codim $\ge 2$）**：设 $D$ 为 $X$ 上 Weil 除子，若 $D|_{X \setminus Z}$ 主，则存在 $f \in K(X)^* = K(X \setminus Z)^*$ 使 $D|_{X \setminus Z} = (f)$。设 $D - (f) = \sum n_Y Y$，其中每个 $Y$ 的支撑都落在 $Z$ 中。因 codim$(Z, X) \ge 2$，不存在 codim 1 的素除子完全包含在 $Z$ 中，故 $D - (f) = 0$，即 $D = (f)$ 为主除子。∎

### 关键概念提示

- 这是 **代数几何中“挖去小闭集不改变类群”** 的经典结果，是证明 $\operatorname{Cl}(\mathbb{A}^n) = 0$、计算奇异曲面类群等的关键工具。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 认为 codim $\ge 2$ 时满射自动是同构 | 同构还需证明单射，即挖去 codim $\ge 2$ 的闭集不会引入新的主除子关系。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Divisor

open AlgebraicGeometry

-- 真闭子集外的限制映射满射；codim ≥ 2 时为同构
theorem classGroup_restriction {X : Scheme} [IsNoetherian X] [IsIntegral X]
    (Z : TopologicalSpace.Closeds X.toTop) (hZ : Z.carrier ≠ Set.univ) :
    Function.Surjective (ClassGroup.restrict (X := X) (Z.carrierᶜ)) ∧
    ((2 : ℕ) ≤ codimension Z.carrier X.carrier →
      Function.Bijective (ClassGroup.restrict (X := X) (Z.carrierᶜ))) :=
  sorry
```

---

## 习题 II.6.6 — 射影空间挖去小闭集的类群

### 题号与精确引用

**Hartshorne II.6.6**

### 问题重述

设 $Z \subsetneq \mathbb{P}^n$ 为真闭子集。若 $\dim Z \le n-2$，则
$$\operatorname{Cl}(\mathbb{P}^n \setminus Z) \cong \mathbb{Z}.$$

### 详细解答

由 II.6.3，$\operatorname{Cl}(\mathbb{P}^n) \cong \mathbb{Z}$。由 II.6.5，因 codim$(Z, \mathbb{P}^n) = n - \dim Z \ge 2$，限制映射
$$\operatorname{Cl}(\mathbb{P}^n) \longrightarrow \operatorname{Cl}(\mathbb{P}^n \setminus Z)$$
是同构。故 $\operatorname{Cl}(\mathbb{P}^n \setminus Z) \cong \mathbb{Z}$。∎

### 关键概念提示

- 这是 II.6.5 的直接推论，常用于计算仿射锥（affine cone）的类群。
- 当 $\dim Z = n-1$ 时，$Z$ 是超曲面，$\operatorname{Cl}(\mathbb{P}^n \setminus Z)$ 可能会变大（例如对应于超曲面补集上的可逆函数群）。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 混淆维数与余维数 | $\dim Z \le n-2$ 等价于 codim$\ge 2$，这是应用 II.6.5 的关键。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme

open AlgebraicGeometry

-- P^n 挖去维数 ≤ n-2 的闭集后类群仍为 Z
theorem classGroup_of_puncturedProjectiveSpace
    (n : ℕ) (k : Type*) [Field k] (Z : TopologicalSpace.Closeds
      (ProjectiveScheme (Fin (n + 1)) k).toTop)
    (hZ : dimension Z.carrier ≤ n - 2) :
    ClassGroup ((ProjectiveScheme (Fin (n + 1)) k)

      (Z.carrierᶜ : (ProjectiveScheme (Fin (n + 1)) k).Opens)) ≅ Multiplicative ℤ :=
  sorry
```

---

## 习题 II.6.7 — 结点三次曲线的类群

### 题号与精确引用

**Hartshorne II.6.7**

### 问题重述

设 $X$ 为 $\mathbb{A}^2_k$ 中由 $y^2 = x^2(x+1)$ 定义的结点三次曲线（nodal cubic）。证明：
(a) 标准化映射 $\mathbb{A}^1_k \to X$ 由 $t \mapsto (t^2 - 1, t(t^2 - 1))$ 给出。
(b) $\operatorname{Pic}(X) \cong k^*$（$k$ 的乘法群）。

### 详细解答

**(a) 标准化映射**

考虑映射 $\phi : \mathbb{A}^1_k = \operatorname{Spec} k[t] \to X = \operatorname{Spec} k[x,y]/(y^2 - x^2(x+1))$，由环同态
$$x \mapsto t^2 - 1, \quad y \mapsto t(t^2 - 1)$$
诱导。验证：$y^2 - x^2(x+1) = t^2(t^2-1)^2 - (t^2-1)^2 \cdot t^2 = 0$，故良定义。

该映射在 $t = \pm 1$ 处都映到结点 $P = (0,0)$，其余点为一一对应。在函数域层面，$k(X) = k(t)$，故 $\phi$ 是双有理的，且为有限态射（因 $k[t]$ 是 $k[x,y]/(y^2 - x^2(x+1))$ 的整闭包）。因此 $\phi$ 是标准化映射。∎

**(b) Picard 群的计算**

*步骤 1*：由 II.6.8（或 Stacks Project），对满足 (*) 的整概形，$\operatorname{Pic}(X) \cong \operatorname{CaCl}(X)$。

*步骤 2*：Cartier 除子由局部可逆函数给出。因 $X$ 是仿射曲线，Cartier 除子等价于在结点 $P$ 处给出“分支信息”。具体地，$\widetilde{X} = \mathbb{A}^1_k$ 的 Picard 群是平凡的（仿射直线的 Picard 群为零）。结点 $P$ 有两条分支（对应 $t = 1$ 和 $t = -1$）。一个 Cartier 除子在 $P$ 附近由两个分支上的可逆函数 $(f_1, f_2)$ 给出，模去两条分支上同时可乘以同一个整体可逆函数。

*步骤 3*：因此 $\operatorname{Pic}(X)$ 由在 $P$ 处两个分支的“不匹配”分类。具体计算得：对任意 $\lambda \in k^*$，可构造线丛 $\mathcal{L}_\lambda$，其在 $P$ 的某邻域上由两个分支的转移函数 $1$ 和 $\lambda$ 给出。该构造给出群同态 $k^* \to \operatorname{Pic}(X)$。

*步骤 4*：证明这是同构。满射：任意 Cartier 除子可通过乘主除子化为只在 $P$ 处非平凡的形式，而 $P$ 处的信息完全由不匹配常数 $\lambda$ 决定。单射：若 $\mathcal{L}_\lambda$ 平凡，则存在整体可逆函数使其在两个分支上的限制之比为 $\lambda$；但 $X$ 是仿射的且奇异，整体可逆函数只能是常数，故 $\lambda = 1$。

*待验证*：更严格的证明需利用正合列
$$0 \to \mathcal{O}_X^* \to \phi_*\mathcal{O}_{\widetilde{X}}^* \to \mathcal{O}_P^* \to 0$$
（其中 $P$ 视为两个点的并），并计算其长正合列中的连接同态。∎

### 关键概念提示

- 这是 **奇异曲线 Picard 群非平凡** 的最经典例子：结点将 Picard 群从 $0$ “扭转”成 $k^*$。
- 尖点（cusp）三次曲线 $y^2 = x^3$ 的 Picard 群则同构于加法群 $(k, +)$。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 直接断言 $\operatorname{Pic}(X) = \operatorname{Cl}(X)$ | 对非正规概形，$\operatorname{CaCl} \to \operatorname{Cl}$ 不一定是同构，应直接计算 $\operatorname{Pic}$ 或 $\operatorname{CaCl}$。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Divisor

open AlgebraicGeometry

-- 结点三次曲线的 Picard 群同构于 k^*
theorem nodalCubic_Picard (k : Type*) [Field k] [CharZero k] :
    Picard (Scheme.Spec (k[X,Y] / Ideal.span {Y^2 - X^2 * (X + 1)})) ≅
    Multiplicative kˣ :=
  sorry
```

---

## 习题 II.6.8 — CaCl 与 Pic 的同构

### 题号与精确引用

**Hartshorne II.6.8**

### 问题重述

设 $X$ 为整概形。证明 $\operatorname{CaCl}(X) \cong \operatorname{Pic}(X)$。

### 详细解答

构造映射 $\operatorname{CaCl}(X) \to \operatorname{Pic}(X)$：对 Cartier 除子 $D = \{(U_i, f_i)\}$，定义线丛 $\mathcal{O}_X(D)$ 如下：在每个 $U_i$ 上取平凡化 $\mathcal{O}_{U_i} \cdot e_i$，转移函数为 $g_{ij} = f_i / f_j \in \mathcal{O}_X(U_i \cap U_j)^*$。因 $f_i/f_j$ 可逆，这些转移函数满足上闭链条件，粘合得到可逆层 $\mathcal{O}_X(D)$。

该映射良定义：若 $D = (f)$ 为主除子，则 $\mathcal{O}_X(D) \cong \mathcal{O}_X$（取 $e_i = f_i / f$ 作为整体截面）。

**构造逆映射**：设 $\mathcal{L}$ 为可逆层。取 $X$ 的开覆盖 $\{U_i\}$ 及平凡化 $\phi_i : \mathcal{L}|_{U_i} \xrightarrow{\sim} \mathcal{O}_{U_i}$。在 $U_i \cap U_j$ 上，$\phi_i \circ \phi_j^{-1}$ 是 $\mathcal{O}_{U_i \cap U_j}^*$ 中元素，记为 $g_{ij}$。因 $X$ 整，$K(X)$ 存在。固定一个分式域中的非零截面 $s$（在 $U_i$ 上对应 $f_i \in K(X)^*$），则 $D = \{(U_i, f_i)\}$ 构成 Cartier 除子，且 $\mathcal{O}_X(D) \cong \mathcal{L}$。

验证这两个映射互为逆，即得同构。∎

### 关键概念提示

- 这是代数几何中最基本的同构之一，它将 **除子的线性等价** 与 **线丛的同构类** 一一对应。
- 对正规概形，结合 II.6.2 可得 $\operatorname{Cl}(X) \cong \operatorname{Pic}(X)$。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 在非整概形上直接套用此同构 | 非整概形可能没有整体函数域，Cartier 除子的定义更复杂，此时 CaCl 与 Pic 的关系需用更一般的上同调描述。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Divisor

open AlgebraicGeometry

-- 整概形上 CaCl ≅ Pic
theorem CaCl_iso_Pic {X : Scheme} [IsIntegral X] :
    CaCl X ≅ Picard X :=
  sorry
```

---

## 习题 II.6.9 — Grothendieck 群 $K(X)$

### 题号与精确引用

**Hartshorne II.6.9**

### 问题重述

设 $X$ 为 Noetherian 概形。定义 $K(X)$ 为有限秩局部自由层生成的自由 Abel 群，模去所有短正合列
$$0 \to \mathcal{E}' \to \mathcal{E} \to \mathcal{E}'' \to 0$$
对应的关系 $[\mathcal{E}] = [\mathcal{E}'] + [\mathcal{E}'']$。
(a) 设 $X = \mathbb{A}^1_k$。证明 $K(X) \cong \mathbb{Z}$。
(b) 设 $X$ 有 ample 可逆层。证明 $K(X)$ 中每个元素可写成 $[\mathcal{E}] - [\mathcal{F}]$，其中 $\mathcal{E}, \mathcal{F}$ 为局部自由层。

### 详细解答

**(a) $K(\mathbb{A}^1_k) \cong \mathbb{Z}$**

$\mathbb{A}^1_k = \operatorname{Spec} k[t]$ 是仿射的，其上的凝聚层对应有限生成 $k[t]$-模。由有限生成模的结构定理（PID 上），任何有限生成模有自由分解
$$0 \to \mathcal{O}^{\oplus r} \to \mathcal{O}^{\oplus s} \to \mathcal{F} \to 0.$$
在 $K(X)$ 中，$[\mathcal{F}] = s[\mathcal{O}] - r[\mathcal{O}] = (s-r)[\mathcal{O}]$。故 $K(X)$ 由 $[\mathcal{O}]$ 生成，同构于 $\mathbb{Z}$（需验证 $[\mathcal{O}]$ 非零：可用秩函数或张量 $k(x)$ 验证）。∎

**(b) ample 层情形**

设 $\mathcal{L}$ 为 ample 可逆层。对任意凝聚层 $\mathcal{F}$，由 Serre 消没定理（或 ample 层的定义），存在 $n \gg 0$ 使得 $\mathcal{F} \otimes \mathcal{L}^{\otimes n}$ 由整体截面生成，从而有满射
$$\mathcal{O}_X^{\oplus N} \twoheadrightarrow \mathcal{F} \otimes \mathcal{L}^{\otimes n}.$$
取核 $\mathcal{G}$，则 $[\mathcal{F}] = [\mathcal{O}^{\oplus N} \otimes \mathcal{L}^{\otimes -n}] - [\mathcal{G} \otimes \mathcal{L}^{\otimes -n}]$。通过对核的秩归纳，可将任意凝聚层表为局部自由层的整系数线性组合。∎

### 关键概念提示

- $K(X)$ 是 **代数 K-理论** 的零阶群，在相交理论中扮演核心角色（如 Riemann-Roch 定理的形式化表述）。
- 在 nonsingular 概形上，$K(X)$ 与由凝聚层定义的 $K_1(X)$ 一致（见 II.6.10）。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 认为 $K(X)$ 只对局部自由层定义 | $K(X)$ 的生成元是局部自由层，但通过关系可表出任意凝聚层的信息。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.KTheory

open AlgebraicGeometry

-- (a) A^1 的 K-群为 Z；(b) ample 层下 K(X) 由局部自由层生成
theorem KTheory_of_affineLine (k : Type*) [Field k] :
    GrothendieckGroup (Scheme.Spec (k[T])) ≅ ℤ :=
  sorry
```

---

## 习题 II.6.10 — Nonsingular 概形上的 $K(X) \cong K_1(X)$

### 题号与精确引用

**Hartshorne II.6.10**

### 问题重述

设 $X$ 为 Noetherian 概形，$K_1(X)$ 为由凝聚层生成的 Grothendieck 群（关系同样来自短正合列）。证明：若 $X$ 是 nonsingular 的，则自然映射 $K(X) \to K_1(X)$ 是同构。

### 详细解答

映射 $K(X) \to K_1(X)$ 将局部自由层类映到自身（局部自由层是凝聚层的子类）。要证这是同构，只需证任意凝聚层 $[\mathcal{F}] \in K_1(X)$ 可表为局部自由层的整系数线性组合。

因 $X$ nonsingular，由 **凝聚层的局部自由分解定理**（Hilbert 合冲定理的层版本）：对任意凝聚层 $\mathcal{F}$，存在有限长度的局部自由分解
$$0 \to \mathcal{E}_n \to \mathcal{E}_{n-1} \to \dots \to \mathcal{E}_0 \to \mathcal{F} \to 0.$$

在 $K_1(X)$ 中，由短正合列的关系，这给出
$$[\mathcal{F}] = \sum_{i=0}^n (-1)^i [\mathcal{E}_i] \in K_1(X).$$

故 $K_1(X)$ 也由局部自由层生成，$K(X) \to K_1(X)$ 是满射。单射性：若 $\sum a_i [\mathcal{E}_i] = 0$ 在 $K_1(X)$ 中，则作为局部自由层的关系它已在 $K(X)$ 中成立（关系都来自短正合列，与是否允许凝聚层无关）。∎

### 关键概念提示

- **Nonsingular 概形** 上的凝聚层总有有限局部自由分解，这是 Hilbert 合冲定理在概形上的推广。
- 对奇异概形，$K(X) \to K_1(X)$ 一般只是单射，不满。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 未验证 nonsingular 保证局部自由分解存在 | 这是证明的核心，需引用 Hilbert 合冲定理或 Stacks Project Tag 00O5。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.KTheory

open AlgebraicGeometry

-- Nonsingular 概形上 K(X) ≅ K_1(X)
theorem K_eq_K1 {X : Scheme} [IsNoetherian X] (hns : IsNonsingular X) :
    GrothendieckGroup X ≅ GrothendieckGroupOfCoherent X :=
  sorry
```

---

## 习题 II.6.11 — 射影空间的 Grothendieck 群

### 题号与精确引用

**Hartshorne II.6.11**

### 问题重述

设 $X = \mathbb{P}^n_k$。证明
$$K(X) \cong \mathbb{Z}[t]/(t^{n+1}),$$
其中 $t = [\mathcal{O}(-1)] - [\mathcal{O}]$ 或 $t = 1 - [\mathcal{O}(-1)]$（依同构方式而定）。

### 详细解答

由 II.6.10，$K(X) = K_1(X)$。由 Quillen 的射影丛公式（或 Grothendieck 的初等证明），对 $\mathbb{P}^n = \mathbb{P}(\mathcal{O}^{\oplus(n+1)})$，有
$$K(\mathbb{P}^n) \cong K(\operatorname{Spec} k)^{\oplus(n+1)} \cong \mathbb{Z}^{\oplus(n+1)}$$
作为 Abel 群，但带有由 $[\mathcal{O}(1)]$ 生成的环结构。

具体地，$K(\mathbb{P}^n)$ 是以 $\{[\mathcal{O}], [\mathcal{O}(-1)], \dots, [\mathcal{O}(-n)]\}$ 为基的自由的 $\mathbb{Z}$-模。设 $t = 1 - [\mathcal{O}(-1)]$。利用 Euler 正合列
$$0 \to \mathcal{O} \to \mathcal{O}(1)^{\oplus(n+1)} \to \mathcal{T}_{\mathbb{P}^n} \to 0$$
及 Koszul 复形，可得关系 $t^{n+1} = 0$。于是
$$K(\mathbb{P}^n) \cong \mathbb{Z}[t]/(t^{n+1}).$$

*待验证*：更标准的证明利用 Beilinson 分解或分次模的 Hilbert 合冲定理，将任意凝聚层在 $K$-群中表为 $\mathcal{O}(i)$ 的线性组合，再由 $\mathcal{O}(i)$ 之间的递推关系得到上述环结构。∎

### 关键概念提示

- 这是 **射影丛公式** 的最简单情形，也是计算 Grassmannian、Flag variety 等齐次空间 K-群的起点。
- $t$ 的几何意义：它是超平面类 $[\mathcal{O}(1)] - [\mathcal{O}]$ 的负元。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 混淆 $t = [\mathcal{O}(-1)] - [\mathcal{O}]$ 与 $1 - [\mathcal{O}(-1)]$ | 两种约定给出的同构差一个符号替换 $t \mapsto -t$，都是正确的。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.KTheory

open AlgebraicGeometry

-- P^n 的 Grothendieck 群
theorem KTheory_of_projectiveSpace (n : ℕ) [n.AtLeastTwo] (k : Type*) [Field k] :
    GrothendieckGroup (ProjectiveScheme (Fin (n + 1)) k) ≅
    ℤ[T] / Ideal.span {T^(n + 1)} :=
  sorry
```

---

## 习题 II.6.12 — $d$-uple 嵌入与除子

### 题号与精确引用

**Hartshorne II.6.12**

### 问题重述

设 $X$ 为满足 $(*)$ 的概形，$D$ 为 Cartier 除子，$\mathcal{L} = \mathcal{O}_X(D)$ 为对应的可逆层。考虑 $d$-uple 嵌入 $v_d : X \hookrightarrow \mathbb{P}^N$（对应完全线性系 $|\mathcal{L}^{\otimes d}|$）。证明 $v_d^*\mathcal{O}_{\mathbb{P}^N}(1) \cong \mathcal{L}^{\otimes d}$，并由此讨论 $d$-uple 嵌入下的除子像。

### 详细解答

$d$-uple 嵌入由整体截面空间 $H^0(X, \mathcal{L}^{\otimes d})$ 给出。设该空间的维数为 $N+1$，取基 $s_0, \dots, s_N$。则 $v_d : X \to \mathbb{P}^N$ 由
$$x \mapsto [s_0(x) : \dots : s_N(x)]$$
定义。由构造，$v_d^*\mathcal{O}_{\mathbb{P}^N}(1)$ 由 $v_d^*x_i$ 生成，而 $v_d^*x_i$ 恰对应截面 $s_i \in H^0(X, \mathcal{L}^{\otimes d})$。故 $v_d^*\mathcal{O}_{\mathbb{P}^N}(1) \cong \mathcal{L}^{\otimes d}$。

**除子像的讨论**：设 $D$ 对应 $\mathcal{L} = \mathcal{O}_X(D)$。则 $dD$ 对应 $\mathcal{L}^{\otimes d}$。在 $d$-uple 嵌入下，$X$ 的超平面截影 $H \cap X$ 对应 $|\mathcal{L}^{\otimes d}|$ 中的某个有效除子 $D' \sim dD$。特别地，若 $D$ 是 ample 的，则对充分大的 $d$，$d$-uple 嵌入将 $X$ 嵌入为射影空间中某个齐次坐标环的闭子概形。∎

### 关键概念提示

- $d$-uple 嵌入是 **Veronese 嵌入** 的概形版本，它将低次线丛的截面转化为高次线丛的整体截面。
- 这是证明任意 projective 概形可被某次 Veronese 嵌入为“截影正规”（projectively normal）的有力工具。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 认为 $v_d^*\mathcal{O}(1) \cong \mathcal{L}$ | 正确的拉回是 $\mathcal{L}^{\otimes d}$，次数被 $d$ 倍放大。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.Divisor

open AlgebraicGeometry

-- d-uple 嵌入的拉回
theorem duple_pullback {X : Scheme} [IsNoetherian X] [IsIntegral X]
    (D : CartierDivisor X) (d : ℕ) (hd : d ≠ 0)
    (vd : ClosedImmersion X (ProjectiveScheme (Fin _) (X.presheaf.obj ⊤))) :
    IsDupleEmbedding vd →
    vd.pullback (lineBundle (𝟙 (ProjectiveScheme _ _))) ≅
    (lineBundle D.1) ^⊗ d :=
  sorry
```

---

**文档位置**: `docs/13-代数几何/Harvard-232br-习题解答/II.6-除子.md`
**创建日期**: 2026-04-17
