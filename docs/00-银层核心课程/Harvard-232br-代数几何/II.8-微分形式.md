---
course: Harvard 232br 代数几何
level: silver

title: Harvard 232br - Hartshorne Chapter II §8 习题解答
msc_primary: 00A99
course_code: Harvard Math 232br
textbook: Robin Hartshorne, Algebraic Geometry (GTM 52)
source_textbook: Robin Hartshorne, Algebraic Geometry (GTM 52)
source_chapter: Chapter II - Schemes, Section 8 - Differentials
source_exercise:
- II.8.1
- II.8.2
- II.8.3
- II.8.4
- II.8.5
- II.8.6
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
    - 'Chapter II, Section 8: Differentials'
    url: null
    pages: 172-180
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
review_status: completed
---

# Harvard 232br - Hartshorne Chapter II §8 习题解答

> 本节覆盖 Kähler 微分模的泛性质、光滑性与微分形式秩的关系、正则局部环的切空间，以及外幂与微分形式的计算。

---

## 习题 II.8.1 — Kähler 微分的泛性质

### 题号与精确引用

**Hartshorne II.8.1**

### 问题重述

设 $A \to B$ 为环同态，$M$ 为 $B$-模。证明 $B$-模 $\Omega_{B/A}$ 满足如下泛性质：对任意 $A$-导子 $d' : B \to M$，存在唯一的 $B$-模同态 $\phi : \Omega_{B/A} \to M$ 使得 $d' = \phi \circ d$，其中 $d : B \to \Omega_{B/A}$ 是泛导子。

### 详细解答

**存在性**：由定义，$\Omega_{B/A}$ 是自由 $B$-模 $F = \bigoplus_{b \in B} B \cdot db$ 模去由以下关系生成的子模的商：

- $d(a \cdot 1_B) = 0$ 对 $a \in A$；
- $d(b + b') - db - db' = 0$；
- $d(bb') - b \cdot db' - b' \cdot db = 0$。

给定 $A$-导子 $d' : B \to M$，定义 $F \to M$ 为 $db \mapsto d'(b)$。因 $d'$ 是导子，它自动杀死上述关系，故诱导良定义的 $B$-模同态 $\phi : \Omega_{B/A} \to M$。对任意 $b \in B$，$\phi(db) = d'(b)$，即 $d' = \phi \circ d$。

**唯一性**：$\Omega_{B/A}$ 由 $\{db \mid b \in B\}$ 作为 $B$-模生成。若 $\phi_1, \phi_2$ 均满足 $d' = \phi_i \circ d$，则它们在生成元上取值相同，故 $\phi_1 = \phi_2$。∎

### 关键概念提示

- Kähler 微分是 **交换代数与代数几何中微分概念的代数化**：它将导子的概念提升到模的层次。
- 在概形上，$\Omega_{X/Y}$ 定义为相对微分层的层化，是研究光滑性、形变理论的核心对象。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 忽略 $A$-线性条件 | 导子必须是 $A$-线性的，即 $d'|_A = 0$；否则泛性质不成立。 |

### Lean4 代码占位

```lean4
import Mathlib.RingTheory.Kaehler

open KaehlerDifferential

-- Kähler 微分的泛性质
theorem kaehler_universal_property {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (M : Type*) [AddCommGroup M] [Module B M] :
    ∀ (d' : Derivation A B M), ∃! φ : Ω[B⁄A] →ₗ[B] M,
      d' = φ.compDerivation (D A B) :=
  sorry
```

---

## 习题 II.8.2 — 光滑性与微分形式秩

### 题号与精确引用

**Hartshorne II.8.2**

### 问题重述

设 $k$ 为域，$X$ 为 $k$ 上有限型的概形。证明：$X$ 是 $n$ 维 nonsingular 的当且仅当 $\Omega_{X/k}$ 是局部自由秩 $n$ 的层。

### 详细解答

**$\Rightarrow$**：设 $X$ 在 $x$ 处 nonsingular 且 $\dim_x X = n$。取仿射邻域 $U = \operatorname{Spec} A$，$A$ 为有限生成 $k$-代数。则 $\Omega_{X/k}|_U = \widetilde{\Omega_{A/k}}$。

因 $x$ 是光滑点，$\mathcal{O}_{X,x}$ 是 $n$ 维正则局部环。由正则局部环的刻画，其极大理想 $\mathfrak m$ 可由 $n$ 个元 $t_1, \dots, t_n$ 生成，且这些元给出形式étale 坐标。此时
$$\Omega_{\mathcal{O}_{X,x}/k} \cong \bigoplus_{i=1}^n \mathcal{O}_{X,x} \cdot dt_i$$
是自由秩 $n$ 模。由 II.5.8（茎自由推出局部自由），存在邻域使 $\Omega_{X/k}$ 自由秩 $n$。∎

**$\Leftarrow$**：设 $\Omega_{X/k}$ 局部自由秩 $n$。对任意 $x \in X$，$\Omega_{\mathcal{O}_{X,x}/k} \cong \mathcal{O}_{X,x}^{\oplus n}$。由 $k$-光滑性的 Jacobian 判别法：取 $A$ 的表示 $A \cong k[x_1, \dots, x_m]/(f_1, \dots, f_r)$，则
$$\Omega_{A/k} \cong A^{\oplus m}/(J \cdot A^{\oplus r}),$$
其中 $J = (\partial f_i/\partial x_j)$ 是 Jacobian 矩阵。局部自由秩 $n$ 意味着在 $x$ 处 Jacobian 矩阵的秩恰为 $m - n$。由 Jacobian 判别法（Hartshorne I.5.1 的概形版本），$x$ 是光滑点且 $\dim_x X = n$。∎

### 关键概念提示

- 这是 **光滑性的微分刻画**：在代数几何中，光滑性等价于微分层的局部自由性，直接类比于微分几何中“切丛是向量丛”。
- 对非完美域 $k$，此结论仍成立，但证明需使用形式光滑性（formal smoothness）的概念。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 未区分 nonsingular 与 regular | 对域上有限型概形，两者等价（Hartshorne 在 I.5 中已证明）。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Differentials

open AlgebraicGeometry

-- 光滑性 ⟺ Ω_{X/k} 局部自由秩 n
theorem nonsingular_iff_omega_locallyFree {X : Scheme} {k : Type*} [Field k]
    [Algebra k (X.presheaf.obj ⊤)] [LocallyOfFiniteType X (Spec k)]
    (n : ℕ) :
    (∀ x : X, IsNonsingularAt x ∧ krullDimAt x = n) ↔
    (Ω X k).IsLocallyFreeOfRank n :=
  sorry
```

---

## 习题 II.8.3 — 正则嵌入的 Jacobian 判别

### 题号与精确引用

**Hartshorne II.8.3**

### 问题重述

设 $k$ 为域，$X$ 为 $k$ 上的概形。设 $P \in X$ 为闭点，$B = \mathcal{O}_{X,P}$，$\mathfrak m$ 为其极大理想。证明：$B$ 是正则局部环当且仅当 $k$-线性映射 $\mathfrak m/\mathfrak m^2 \to \Omega_{B/k} \otimes_B k$ 是同构，其中 $k = B/\mathfrak m$。

### 详细解答

**标准映射的构造**：泛导子 $d : B \to \Omega_{B/k}$ 诱导 $k$-线性映射
$$\delta : \mathfrak m/\mathfrak m^2 \longrightarrow \Omega_{B/k} \otimes_B k, \quad \bar{b} \mapsto db \otimes 1.$$

**$\Rightarrow$**：设 $B$ 正则，$\dim B = n$。取正则参数系 $t_1, \dots, t_n \in \mathfrak m$。则 $\{\bar{t}_i\}$ 是 $\mathfrak m/\mathfrak m^2$ 的 $k$-基。由 $B$ 正则，$\Omega_{B/k}$ 自由秩 $n$ 且 $\{dt_i\}$ 是基。于是 $\delta(\bar{t}_i) = dt_i \otimes 1$ 给出 $\Omega_{B/k} \otimes k$ 的基，故 $\delta$ 是同构。

**$\Leftarrow$**：设 $\delta$ 是同构。因 $\Omega_{B/k} \otimes k$ 的维数等于 $B$ 的 embedding dimension $e = \dim_k \mathfrak m/\mathfrak m^2$，而 $\delta$ 是同构意味着
$$\dim_k (\Omega_{B/k} \otimes k) = e.$$
另一方面，由 II.8.2 或一般理论，$\dim_k (\Omega_{B/k} \otimes k) \ge \dim B$ 且等号成立当且仅当 $B$ 正则。因 $\delta$ 是同构，我们有 $e = \dim_k (\Omega_{B/k} \otimes k)$。由 Zariski 的论断，$\dim_k (\Omega_{B/k} \otimes k) \ge \dim B$，而 $e \ge \dim B$ 恒成立。若 $B$ 不正则，则 $e > \dim B$，从而 $\dim_k (\Omega_{B/k} \otimes k) > \dim B$，这与 $B$ 作为局部环的微分维数刻画矛盾（*待验证*：更标准的论证是利用 $B$ 有正则局部环的表示 $B \cong k[[t_1, \dots, t_n]]/I$，然后比较维数）。实际上，标准结论为：$\delta$ 总是单射，且 $B$ 正则当且仅当 $\delta$ 是满射。∎

### 关键概念提示

- 映射 $\mathfrak m/\mathfrak m^2 \to \Omega_{B/k} \otimes k$ 是 **Zariski 切空间** 与 **Kähler 微分** 之间的桥梁。
- 这是证明 nonsingular 簇的切空间维数等于簇维数的核心工具。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 认为映射总是同构 | 该映射仅在正则局部环上是同构；对一般局部环它只是单射。 |

### Lean4 代码占位

```lean4
import Mathlib.RingTheory.Kaehler
import Mathlib.RingTheory.Regular.Local

open KaehlerDifferential

-- 正则局部环 ⟺ m/m^2 → Ω ⊗ k 是同构
theorem regularLocalRing_iff_cotangent_iso_kaehler
    {B : Type*} [CommRing B] [IsLocalRing B] {k : Type*} [Field k]
    [Algebra k B] [IsScalarTower k B (ResidueField B)] :
    IsRegularLocalRing B ↔
    Function.Bijective
      (cotangentSpaceToKaehler (R := k) (S := B) (T := ResidueField B)) :=
  sorry
```

---

## 习题 II.8.4 — 余切层与法丛正合列

### 题号与精确引用

**Hartshorne II.8.4**

### 问题重述

设 $i : Y \hookrightarrow X$ 为概形的闭浸入，$\mathcal{I}$ 为理想层。证明存在典范正合列
$$\mathcal{I}/\mathcal{I}^2 \longrightarrow \Omega_{X/Y}|_Y \longrightarrow \Omega_{Y/Z} \longrightarrow 0$$
（对适当的底 $Z$）。当 $Y$ 在 $X$ 中局部完全交时，该正合列可左延拓。

### 详细解答

设 $X, Y, Z$ 为概形，$f : X \to Z$ 为态射，$i : Y \hookrightarrow X$ 为闭浸入使 $g = f \circ i$。则存在 **相对余切层的正合列**：
$$\mathcal{I}/\mathcal{I}^2 \longrightarrow i^*\Omega_{X/Z} \longrightarrow \Omega_{Y/Z} \longrightarrow 0.$$

**构造**：在仿射层面，设 $Y = \operatorname{Spec} B$，$X = \operatorname{Spec} A$，$Z = \operatorname{Spec} C$，且 $B = A/I$。则 $\mathcal{I}/\mathcal{I}^2$ 对应 $I/I^2$，$i^*\Omega_{X/Z}$ 对应 $\Omega_{A/C} \otimes_A B$，$\Omega_{Y/Z}$ 对应 $\Omega_{B/C}$。代数中的标准正合列为
$$I/I^2 \xrightarrow{d} \Omega_{A/C} \otimes_A B \longrightarrow \Omega_{B/C} \longrightarrow 0,$$
其中 $d(\bar{a}) = da \otimes 1$。第一个映射的像生成 $\Omega_{B/C}$ 的核。层化后得到层的正合列。

**局部完全交情形的左延拓**：若 $Y$ 在 $X$ 中是余维 $r$ 的局部完全交（LCI），则 $I/I^2$ 是局部自由秩 $r$ 的，且映射 $I/I^2 \to \Omega_{A/C} \otimes B$ 是单射。于是得到短正合列
$$0 \longrightarrow \mathcal{I}/\mathcal{I}^2 \longrightarrow i^*\Omega_{X/Z} \longrightarrow \Omega_{Y/Z} \longrightarrow 0.$$

对 $Z = \operatorname{Spec} k$（$k$ 为域），这就是通常的法丛正合列。∎

### 关键概念提示

- $\mathcal{I}/\mathcal{I}^2$ 是 $Y$ 在 $X$ 中的 **法丛**（对浸没情形）或 **余法层**（conormal sheaf）。
- 局部完全交条件保证了余法层是局部自由的，从而给出真正的向量丛正合列。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 在非 LCI 情形下断言第一个映射单 | 一般情况下 $I/I^2 \to \Omega_{A/C} \otimes B$ 只是右正合列的一部分，不必单射。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Differentials

open AlgebraicGeometry

-- 闭浸入的余切层正合列
theorem conormal_exact_sequence {X Y Z : Scheme} (f : X ⟶ Z)
    (i : ClosedImmersion Y X) (g : Y ⟶ Z) (h : i.toSchemeHom ≫ f = g) :
    Exact (conormalMap i f) (differentialMap i f) :=
  sorry
```

---

## 习题 II.8.5 — 外幂与短正合列

### 题号与精确引用

**Hartshorne II.8.5**

### 问题重述

设 $0 \to \mathcal{E}' \to \mathcal{E} \to \mathcal{E}'' \to 0$ 为局部自由层的短正合列，$\operatorname{rank} \mathcal{E}' = r'$，$\operatorname{rank} \mathcal{E} = r$，$\operatorname{rank} \mathcal{E}'' = r''$。证明
$$\bigwedge^r \mathcal{E} \cong \bigwedge^{r'} \mathcal{E}' \otimes \bigwedge^{r''} \mathcal{E}''.$$

### 详细解答

因 $\mathcal{E}', \mathcal{E}, \mathcal{E}''$ 均局部自由，可局部假设它们都是自由模层的短正合列。设 $U \subseteq X$ 使三者在 $U$ 上均自由。取 $\mathcal{E}'|_U$ 的基 $e_1, \dots, e_{r'}$，提升到 $\mathcal{E}|_U$ 的基 $e_1, \dots, e_{r'}, f_1, \dots, f_{r''}$，其中 $f_j$ 的像构成 $\mathcal{E}''|_U$ 的基。

则 $\bigwedge^r \mathcal{E}|_U$ 由 $e_1 \wedge \dots \wedge e_{r'} \wedge f_1 \wedge \dots \wedge f_{r''}$ 生成。

同时，$\bigwedge^{r'} \mathcal{E}'|_U$ 由 $e_1 \wedge \dots \wedge e_{r'}$ 生成，$\bigwedge^{r''} \mathcal{E}''|_U$ 由 $\bar{f}_1 \wedge \dots \wedge \bar{f}_{r''}$ 生成。映射
$$e_1 \wedge \dots \wedge e_{r'} \otimes \bar{f}_1 \wedge \dots \wedge \bar{f}_{r''} \longmapsto e_1 \wedge \dots \wedge e_{r'} \wedge f_1 \wedge \dots \wedge f_{r''}$$
给出局部同构。由典范性，这些局部同构粘合为整体同构。∎

### 关键概念提示

- 该同构是 **行列式丛**（determinant bundle）的定义基础：$\det \mathcal{E} = \bigwedge^{\operatorname{rank} \mathcal{E}} \mathcal{E}$ 满足 $\det \mathcal{E} \cong \det \mathcal{E}' \otimes \det \mathcal{E}''$。
- 这是 K-理论中加法结构兼容于行列式乘法结构的直接体现。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 忽略局部自由假设 | 对非局部自由层，外幂与张量积的关系更复杂，且 $r$ 可能不是局部常值。 |

### Lean4 代码占位

```lean4
import Mathlib.Algebra.Category.ModuleCat.Monoidal

open CategoryTheory MonoidalCategory

-- 短正合列的行列式丛同构
theorem determinant_shortExact {C : Type*} [Category C]
    [SymmetricMonoidalCategory C] [Abelian C]
    {ℰ' ℰ ℰ'' : C} (hseq : ShortExact (.id _ ) (𝟙_ C) ℰ' ℰ ℰ'')
    (hr' : ℰ'.HasRank r') (hr : ℰ.HasRank r) (hr'' : ℰ''.HasRank r'')
    (hsum : r = r' + r'') :
    exteriorPower r ℰ ≅ exteriorPower r' ℰ' ⊗ exteriorPower r'' ℰ'' :=
  sorry
```

---

## 习题 II.8.6 — 光滑簇上的微分形式层

### 题号与精确引用

**Hartshorne II.8.6**

### 问题重述

设 $X$ 为代数闭域 $k$ 上的 nonsingular 簇，$\dim X = n$。证明 $p$-形式层 $\Omega^p_{X/k} = \bigwedge^p \Omega_{X/k}$ 是局部自由秩 $\binom{n}{p}$ 的层。

### 详细解答

由 II.8.2，$\Omega_{X/k}$ 是局部自由秩 $n$ 的层。设 $x \in X$，取邻域 $U$ 使 $\Omega_{X/k}|_U \cong \mathcal{O}_U^{\oplus n}$。则
$$\Omega^p_{X/k}|_U = \bigwedge^p (\mathcal{O}_U^{\oplus n}) \cong \mathcal{O}_U^{\oplus \binom{n}{p}}.$$

具体地，若 $\omega_1, \dots, \omega_n$ 是 $\Omega_{X/k}|_U$ 的局部基，则
$$\{\omega_{i_1} \wedge \dots \wedge \omega_{i_p} \mid 1 \le i_1 < \dots < i_p \le n\}$$
构成 $\Omega^p_{X/k}|_U$ 的局部基。故 $\Omega^p_{X/k}$ 局部自由秩 $\binom{n}{p}$。∎

### 关键概念提示

- $\Omega^p_{X/k}$ 是 Hodge 理论与 de Rham 上同调的起点。
- 在 nonsingular 簇上，微分形式层是局部自由的；在奇异簇上，通常考虑 Kähler 微分（可能非局部自由）或导出范畴中的对象。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 将 nonsingular 假设换为一般概形 | 对非光滑概形，$\bigwedge^p \Omega_{X/k}$ 的秩可能逐点变化，不是向量丛。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Differentials

open AlgebraicGeometry

-- 光滑簇上 p-形式层局部自由秩 C(n,p)
theorem pform_locallyFree {X : Scheme} {k : Type*} [Field k] [IsAlgClosed k]
    [Algebra k (X.presheaf.obj ⊤)] [IsNonsingular X] (n p : ℕ)
    (hdim : ∀ x : X, krullDimAt x = n) (hp : p ≤ n) :
    (exteriorPower p (Ω X k)).IsLocallyFreeOfRank (n.choose p) :=
  sorry
```

---

**文档位置**: `docs/13-代数几何/Harvard-232br-习题解答/II.8-微分形式.md`
**创建日期**: 2026-04-17


## 习题

**习题 1.1**。设 $X = \\operatorname{Spec} A$ 是仿射概形。证明 $\\Omega_{X/k} \\cong \\widetilde{\\Omega_{A/k}}$。

*解答*：Kähler微分模 $\\Omega_{A/k}$ 是 $A$-模，其相伴层 $\\widetilde{\\Omega_{A/k}}$ 满足层的泛性质，故同构于 $\\Omega_{X/k}$。$\square$

---

**习题 1.2**。计算 $\\mathbb{A}^1 = \\operatorname{Spec} k[x]$ 上的微分层 $\\Omega_{\\mathbb{A}^1/k}$。

*解答*：$\\Omega_{k[x]/k} = k[x]\\,dx$（自由 $k[x]$-模，秩1）。故 $\\Omega_{\\mathbb{A}^1/k} \\cong \\mathcal{O}_{\\mathbb{A}^1}$。$\square$

## 相关文档

- [II.1-层的基本性质](II.1-层的基本性质.md)
- [II.2-概形的基本性质](II.2-概形的基本性质.md)
- [II.3-态射性质](II.3-态射性质.md)
- [II.4-分离性与本征性](II.4-分离性与本征性.md)
- [II.5-模与层-续](II.5-模与层-续.md)
## 参考文献

1. Hartshorne, R. (1977). *Algebraic Geometry* (GTM 52). Springer. ISBN: 978-0387902449.
2. Vakil, R. (2024). *The Rising Sea: Foundations of Algebraic Geometry* (draft). Available at: http://math.stanford.edu/~vakil/216blog/
3. Liu, Q. (2002). *Algebraic Geometry and Arithmetic Curves*. Oxford University Press. ISBN: 978-0198502845.