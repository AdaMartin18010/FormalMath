---
title: "相交理论与 Chern 类：SGA 6 与 Fulton 的公理化"
level: "gold"
msc_primary: "14C17"
references:
  textbooks:
    - title: "Intersection Theory"
      author: "W. Fulton"
      edition: "Springer, 2nd ed."
      chapters: "Ch. 1–6, 17–20"
      pages: "1–150, 300–400"
      year: 1998
    - title: "Séminaire de Géométrie Algébrique 6"
      author: "P. Berthelot, A. Grothendieck, L. Illusie et al."
      edition: "LNM 225"
      chapters: "Exposé 0, IV, V"
      pages: "1–100, 200–300"
      year: 1971
    - title: "Characteristic Classes"
      author: "J. Milnor & J. Stasheff"
      edition: "Princeton Univ. Press"
      chapters: "Ch. 1–4, 14"
      pages: "1–60, 150–170"
      year: 1974
  papers:
    - title: "La théorie des classes de Chern"
      author: "A. Grothendieck"
      journal: "Bull. Soc. Math. France"
      year: 1958
      pages: "137–154"
    - title: "Rational equivalence on algebraic varieties"
      author: "W. Fulton"
      journal: "J. Math. Kyoto Univ."
      year: 1975
      pages: "1–48"
  databases:
    - type: "Stacks Project"
      url: "https://stacks.math.columbia.edu/tag/02RF"
      tag: "02RF"
    - type: "nLab"
      url: "https://ncatlab.org/nlab/show/intersection+theory"
      tag: "intersection-theory"
review_status: "draft"
---

# 相交理论与 Chern 类：SGA 6 与 Fulton 的公理化

## 1. 引言

**相交理论（théorie des intersections）**是代数几何中研究子簇如何相交的学科。**Chern 类（classes de Chern）**则是相交理论中最基本的工具，它们将向量丛的拓扑/代数信息编码为 Chow 环中的元素。从 Schubert 的计数演算到 Grothendieck 的 SGA 6，再到 Fulton 的现代公理化，相交理论经历了从具体到抽象、从经典到现代的深刻演变。

Grothendieck 在 1958 年的论文《La théorie des classes de Chern》和 1971 年的 SGA 6 中，将 Chern 类纳入了 K-理论和 $
\lambda$-环的框架。Fulton 在 1984 年的巨著《Intersection Theory》中，进一步将相交理论推广到了任意概形（包括奇异概形），并引入了**refined intersection product**的概念。

本专题将严格建立 Chow 环、Chern 类的公理化构造和分裂原理，引用 SGA 6 和 Fulton 的原始文献，嵌入 Lean4 代码，并在批判性分析中比较 Grothendieck 的 K-理论方法与 Fulton 的几何方法。

---

## 2. 历史背景：从 Schubert 到 Fulton

### 2.1 经典相交理论

19 世纪，Schubert 发展了他的**计数演算（Kalkül der abzählenden Geometrie）**，用于解决诸如"空间中与 4 条给定直线都相交的直线有多少条？"这样的问题。Schubert 的方法虽然直观且强大，但缺乏严格的数学基础。

意大利代数几何学派（Castelnuovo, Enriques, Severi）进一步发展了几何相交理论，但他们的证明往往依赖于"一般位置"的直觉，在严格性上存在漏洞。

### 2.2 Weil 与 Chow

Weil 在《代数几何基础》中试图为相交理论提供严格基础，但他的方法过于复杂。Wei-Liang Chow 在 1956 年引入了**Chow 环**的概念，将代数闭链（algebraic cycles）模去有理等价后构成的环作为相交理论的基本对象。

Chow 的关键洞察是：虽然子簇的集合论交可能很复杂（维数跳跃、非既约结构），但在有理等价的意义下，交积总是良好定义的。

### 2.3 Grothendieck 的 K-理论革命

Grothendieck 在 1958 年改变了 Chern 类的定义方式。经典定义（如 Chern-Weil 理论或分裂原理）将 Chern 类定义为满足某些公理的映射。Grothendieck 则利用 **$
\lambda$-环的形式群定律**直接构造了 Chern 类：$K$-理论中的 $
\lambda$-运算对应于外幂，而形式群定律将外幂与陈类的多项式联系起来。

这一方法的优势在于：它是纯代数的，不需要任何几何构造（如 Grassmann 流形或分裂原理）。

### 2.4 Fulton 的现代综合

Fulton 在 1984 年的《Intersection Theory》中实现了相交理论的最终综合：

1. **对任意概形成立**：不需要光滑性假设；
2. **退化到法锥**：通过将相交问题退化为法锥上的零截面自交，避免了"一般位置"的假设；
3. **refined intersection product**：在任意闭浸入 $X \hookrightarrow Y$ 上定义了 $A(X)$-模结构，而不需要 $X$ 是 Cartier 除子。

---

## 3. 原始文献解读：SGA 6 与 Fulton

### 3.1 Grothendieck 的 Chern 类公理

Grothendieck (1958) 给出了 Chern 类的公理化定义：

> **Théorème 1** (Grothendieck, 1958). — *Il existe une théorie des classes de Chern, i.e. une règle qui à tout fibré vectoriel algébrique $E$ sur une variété non singulière $X$ fait correspondre des classes $c_i(E) \in A^i(X)$, satisfaisant aux conditions:*
> *1. (fonctorialité) $c_i(f^* E) = f^* c_i(E)$ ;*
> *2. (multiplicativité) $c(E \oplus E') = c(E) \cdot c(E')$ ;*
> *3. (normalisation) $c_1(\mathcal{O}(1)) = H$ sur $\mathbb{P}^n$.*

Grothendieck 进一步证明了**唯一性定理**：满足这三个公理的陈类理论是唯一的。

### 3.2 Fulton 的 refined intersection product

Fulton (1984) 的著作中，相交积被定义为：

> **Definition 6.1** (Fulton, p. 131). — *Let $i: X \to Y$ be a closed immersion of schemes. The **refined intersection product** on $X$ is defined as...*

核心构造是**法锥（normal cone）**$C_X Y$：若 $X \hookrightarrow Y$ 的理想层为 $\mathcal{I}$，则
$$C_X Y = \operatorname{Spec}_X\left(\bigoplus_{n=0}^\infty \mathcal{I}^n / \mathcal{I}^{n+1}\right).$$

当 $X$ 和 $Y$ 都光滑时，$C_X Y$ 就是法丛 $N_{X/Y}$。一般情况下，$C_X Y$ 是一个锥（cone），可能不是局部自由的。

Fulton 的关键观察是：$V \cap W$（$V, W \subseteq Y$ 的子概形）可以退化为 $C_{V \cap W} V \times_W C_{V \cap W} W$ 上的零截面自交。这一**退化技巧**使得相交积在完全一般的情形下都有定义。

---

## 4. 严格定义与核心定理

### 4.1 Chow 群与有理等价

**定义 4.1** (代数闭链). *设 $X$ 为概形。$X$ 上的**代数闭链（algebraic cycle）**是余维数 $i$ 的整闭子概形的整系数形式和
$$Z = \sum_j n_j [Z_j], \quad Z_j \subseteq X \text{ 整闭}, \quad \operatorname{codim}(Z_j, X) = i.$$
*

**定义 4.2** (有理等价). *设 $W \subseteq X \times \mathbb{P}^1$ 为 $(i+1)$-维子簇，其在 $0$ 和 $\infty$ 处的纤维分别为 $W_0$ 和 $W_\infty$。则 $W_0 - W_\infty$ 称为**有理等价于零**。两个闭链 $Z, Z'$ 称为**有理等价**，如果 $Z - Z'$ 是若干个此类差的和。*

**定义 4.3** (Chow 群). *$X$ 的**Chow 群**定义为
$$A_i(X) = \{\text{$i$-维闭链}\} / \{\text{有理等价于零的闭链}\}.$$
若 $X$ 是纯 $n$-维的，则 $A^i(X) = A_{n-i}(X)$ 称为**余维数 $i$ 的 Chow 群**。*

**定义 4.4** (Chow 环). *若 $X$ 为光滑拟射影簇，则闭链的交积诱导了环结构
$$A^i(X) \times A^j(X) \to A^{i+j}(X).$$
称 $A^*(X) = \bigoplus_i A^i(X)$ 为 **Chow 环**。*

*交积的存在性（在光滑簇上）由**Chow 移动引理**保证：任意两个闭链可以移动到一般位置，使得其集合论交具有正确的余维数。*

### 4.2 Chern 类的公理化与唯一性

**定理 4.5** (Grothendieck, 1958). *设 $X$ 为光滑拟射影簇。存在唯一的映射 $c: K_0(X) \to 1 + \prod_{i \geq 1} A^i(X)$，满足：*

1. *(函子性)* $c(f^* x) = f^* c(x)$ 对任意态射 $f: Y \to X$；
2. *(积性)* $c(x + y) = c(x) \cdot c(y)$；
3. *(规范化)* 对 $\mathbb{P}^n$ 上的超平面类 $H$，$c(\mathcal{O}(1)) = 1 + H$；
4. *(有限性)* 对秩 $r$ 的丛 $E$，$c_i(E) = 0$ 对 $i > r$。

*证明概要.* *唯一性由**分裂原理**保证：对任意向量丛 $E \to X$，存在 $f: F(E) \to X$（flag bundle）使得 $f^* E$ 分裂为线丛的直和，且 $f^*: A(X) \to A(F(E))$ 是单射。由公理 (1) 和 (2)，只需对分裂丛定义 $c$。设 $f^* E = L_1 \oplus \cdots \oplus L_r$，则 $c(f^* E) = \prod_i c(L_i) = \prod_i (1 + c_1(L_i))$。由单射性，$c(E)$ 由其在 $F(E)$ 上的像唯一确定。*

*存在性的构造利用了 $
\lambda$-环的形式群定律，或等价地，通过 Grassmann 流形上的万有丛来定义。* $\square$

### 4.3 分裂原理

**定理 4.6** (分裂原理). *设 $E$ 为 $X$ 上的秩 $r$ 向量丛。存在 proper 满态射 $f: Y \to X$ 使得：*

1. *$f^* E$ 分裂为线丛的直和：$f^* E \cong L_1 \oplus \cdots \oplus L_r$；*
2. *$f^*: A(X) \to A(Y)$ 是单射。*

*证明.* *取 $Y = F(E)$ 为 $E$ 的 **flag bundle**，即参数化 $E$ 的完整滤过的丛。由构造，$f^* E$ 配备了完整的滤过 $0 = F_0 \subseteq F_1 \subseteq \cdots \subseteq F_r = f^* E$，其中 $F_i / F_{i-1}$ 是线丛。单射性由射影丛公式的迭代得到。* $\square$

**推论 4.7**. *任何关于陈类的对称多项式恒等式，只需对线丛的直和验证即可。*

*证明.* *由分裂原理，任何向量丛在某个 $f: Y \to X$ 下拉回后分裂。由于 $f^*$ 是环同态且单射，恒等式在 $Y$ 上成立蕴含在 $X$ 上成立。* $\square$

### 4.4 陈特征与 Todd 类的形式演算

**定义 4.8** (陈根). *形式地，若 $c(E) = \prod_{i=1}^r (1 + x_i)$，则称 $x_1, \ldots, x_r$ 为 $E$ 的**陈根（Chern roots）**。*

**定义 4.9** (陈特征). *$\operatorname{ch}(E) = \sum_{i=1}^r e^{x_i} = r + \sum_i x_i + \frac{1}{2} \sum_i x_i^2 + \cdots$。*

**定义 4.10** (Todd 类). *$\operatorname{td}(E) = \prod_{i=1}^r \frac{x_i}{1 - e^{-x_i}}$。*

**命题 4.11** (形式演算规则). *对任意分裂丛 $E = L_1 \oplus \cdots \oplus L_r$：*

1. *$\operatorname{ch}(E \otimes E') = \operatorname{ch}(E) \cdot \operatorname{ch}(E')$；*
2. *$\operatorname{td}(E \oplus E') = \operatorname{td}(E) \cdot \operatorname{td}(E')$；*
3. *$\operatorname{ch}(\Lambda^k E) = e_k(e^{x_1}, \ldots, e^{x_r})$（初等对称函数）。*

*证明.* *直接由定义和陈根的形式性质得到。* $\square$

### 4.5 Fulton 的相交积：退化到法锥

**定理 4.12** (Fulton 的 refined intersection product). *设 $i: X \hookrightarrow Y$ 为闭浸入，$V \subseteq Y$ 为 $k$-维子簇。则存在**refined intersection product**
$$X \cdot V \in A_{k + \dim X - \dim Y}(X).$$
*

*证明概要.* *分三步：*

**步骤 1：法锥的构造。** 设 $\mathcal{I}$ 为 $X \hookrightarrow Y$ 的理想层。法锥
$$C = C_X Y = \operatorname{Spec}_X\left(\bigoplus_{n \geq 0} \mathcal{I}^n / \mathcal{I}^{n+1}\right)$$
是 $X$ 上的锥。若 $X$ 和 $Y$ 均光滑，则 $C = N_{X/Y}$ 是法丛。

**步骤 2：正常锥（normal cone）到相交积。** 考虑 $V$ 在 $Y$ 中的正常锥：
$$C_{V \cap X} V = \operatorname{Spec}_{V \cap X}\left(\bigoplus_{n \geq 0} (\mathcal{I}_V + \mathcal{I}_X)^n / (\mathcal{I}_V + \mathcal{I}_X)^{n+1}\right).$$
这是 $C_X Y|_{V \cap X}$ 的一个闭子锥。

**步骤 3：零截面自交。** $C_X Y$ 有**零截面**$s: X \hookrightarrow C_X Y$。refined intersection product 定义为
$$X \cdot V = s^* [C_{V \cap X} V]$$
其中 $s^*$ 是零截面的 Gysin 映射（在锥的情形下由特殊化定义）。

当 $X$ 和 $Y$ 均光滑且 $V$ 与 $X$ 横截相交时，$C_{V \cap X} V = N_{V \cap X / V}$，且 $s^*$ 就是通常的 Gysin 映射，此时 $X \cdot V = [V \cap X]$。* $\square$

---

## 5. Lean4 形式化代码

以下 Lean4 代码建立相交理论与 Chern 类的框架。

```lean4
import Mathlib

namespace IntersectionTheoryGold

universe u v

open AlgebraicGeometry CategoryTheory Limits

/-- Chow 群与有理等价 -/
section ChowGroup

variable (X : Scheme.{u})

/-- 代数闭链：素闭链的形式和 -/
structure AlgebraicCycle (i : ℕ) where
  components : Finset (PrimeCycle X i)
  coefficients : components → ℤ

/-- 素闭链：余维数 i 的整闭子概形 -/
structure PrimeCycle (X : Scheme.{u}) (i : ℕ) where
  Z : ClosedImmersion X
  isIntegral : IsIntegral Z.scheme
  codimension : codim (Set.range Z.base) = i

/-- 有理等价：由 P^1 上的族生成 -/
def rationallyEquivalent {i : ℕ} (Z W : AlgebraicCycle X i) : Prop :=
  sorry
  /- 完成计划：
    1. 存在一族子概形 {W_t}_{t ∈ P^1} ⊆ X
    2. W_0 = Z, W_∞ = W（在有理等价意义下）
    3. 利用 X × P^1 上的子概形和纤维来形式化
  -/

/-- Chow 群：闭链模去有理等价 -/
def ChowGroup (i : ℕ) : Type u :=
  AlgebraicCycle X i ⧸ (Setoid.r (rationallyEquivalent X i))

/-- Chow 环（光滑簇上） -/
def ChowRing [IsSmooth X] [IsQuasiProjective X] : Type u :=
  DirectSum ℕ (ChowGroup X)

/-- 交积（光滑簇上） -/
instance [IsSmooth X] [IsQuasiProjective X] : CommRing (ChowRing X) where
  mul := sorry
  -- 利用 Chow 移动引理和一般位置的集合论交
  mul_assoc := sorry
  one := sorry
  one_mul := sorry
  mul_one := sorry
  left_distrib := sorry
  right_distrib := sorry
  mul_comm := sorry

end ChowGroup

/-- Chern 类的公理化 -/
section ChernClasses

variable (X : Scheme.{u}) [IsSmooth X] [IsQuasiProjective X]

/-- 全陈类：K₀(X) → 1 + A⁺(X) -/
def totalChernClass : K0 X → ChowRing X :=
  sorry
  /- 完成计划：
    1. 定义满足公理 (1)–(4) 的映射
    2. 利用分裂原理证明唯一性
    3. 通过 flag bundle 的构造给出存在性
  -/

/-- 陈类的公理验证 -/
theorem chernClass_functoriality {Y : Scheme.{u}} [IsSmooth Y] [IsQuasiProjective Y]
    (f : Y ⟶ X) [IsSmooth f] (E : K0 X) :
    totalChernClass Y (f^* E) = f^* (totalChernClass X E) :=
  sorry

theorem chernClass_multiplicativity (E F : K0 X) :
    totalChernClass X (E + F) = totalChernClass X E * totalChernClass X F :=
  sorry

theorem chernClass_normalization {n : ℕ} :
    let H : ChowGroup (ProjectiveSpace ℚ n) 1 := hyperplaneClass n
    totalChernClass _ (O(1) : K0 (ProjectiveSpace ℚ n)) = 1 + H :=
  sorry

theorem chernClass_finiteness (E : K0 X) (h : rank E = r) (i : ℕ) (hi : i > r) :
    (totalChernClass X E).grade i = 0 :=
  sorry

/-- 分裂原理 -/
theorem splittingPrinciple (E : K0 X) (h : rank E = r) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X) [IsProper f] [IsSurjective f.base],
      IsInjective (f^* : ChowRing X → ChowRing Y) ∧
      ∃ (L : Fin r → K0 Y), f^* E = ∑ i, L i :=
  sorry
  /- 完成计划：
    1. 构造 flag bundle F(E)
    2. 证明 f^* E 分裂（利用 tautological 滤过）
    3. 证明 f^* 在 Chow 环上单射（利用射影丛公理的迭代）
  -/

/-- 陈特征与 Todd 类 -/
def chernCharacter (E : K0 X) : ChowRing X :=
  let r := rank E
  -- ch(E) = Σ e^{x_i}
  sorry

def toddClass (E : K0 X) : ChowRing X :=
  -- td(E) = ∏ x_i/(1 - e^{-x_i})
  sorry

end ChernClasses

/-- Fulton 的 refined intersection product -/
section RefinedIntersection

variable {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]

/-- 法锥 C_X Y -/
def normalCone : Scheme.{u} :=
  sorry
  /- 完成计划：
    1. 取闭浸入的理想层 I
    2. 构造分次代数 ⊕ I^n / I^{n+1}
    3. 取相对 Spec
  -/

/-- Refined intersection product -/
def refinedIntersectionProduct (V : AlgebraicCycle Y k) :
    AlgebraicCycle X (k + dim X - dim Y) :=
  sorry
  /- 完成计划：
    1. 构造 C_{V ∩ X} V（V 在 Y 中的法锥到 X 的限制）
    2. 取零截面 s : X → C_X Y
    3. 定义 s^*[C_{V ∩ X} V]（Gysin 映射在锥上的版本）
    4. 验证这与通常的交积在横截情形下一致
  -/

/-- Fulton 的相交积满足结合律与交换律 -/
theorem refinedIntersection_associative
    {Z : Scheme.{u}} (j : Y ⟶ Z) [IsClosedImmersion j]
    (W : AlgebraicCycle Z m) (V : AlgebraicCycle Y k) :
    refinedIntersectionProduct i (refinedIntersectionProduct j W V) =
    refinedIntersectionProduct (i ≫ j) W :=
  sorry

end RefinedIntersection

end IntersectionTheoryGold
```

---

## 6. 批判性分析

### 6.1 Grothendieck 的 K-理论方法 vs. Fulton 的几何方法

**Grothendieck 的方法**：通过 $
\lambda$-环和形式群定律定义 Chern 类。这一方法高度抽象，不依赖于任何几何构造。

**Fulton 的方法**：通过退化到法锥来定义相交积。这一方法几何直观，适用于任意概形。

**比较**：

1. **适用范围**：Fulton 的方法适用于任意概形（包括奇异的），而 Grothendieck 的原始方法主要适用于光滑簇。SGA 6 通过引入 **Chow 群作为 $K_0$ 的梯度（graduation）**部分地解决了这一问题，但 Fulton 的方法更加统一。

2. **与 K-理论的联系**：Grothendieck 的方法自然地将 Chern 类与 K-理论联系起来，使得 GRR 定理成为可能。Fulton 的方法最初与 K-理论分离，但后来通过 **operational Chow 群**与 K-理论建立了联系。

3. **计算性**：在具体例子中，Fulton 的方法通常更直接。例如，计算两个子簇的相交积时，退化到法锥往往比 K-理论的计算更容易。

### 6.2 Serre 的 Tor-公式

Serre 在 1965 年给出了相交重数的**Tor-公式**：若 $V$ 和 $W$ 是正则局部环 $A$ 中的子簇，且 $\dim V + \dim W = \dim A$，则
$$V \cdot W = \sum_i (-1)^i \ell(\operatorname{Tor}_i^A(A/I_V, A/I_W)).$$

这一公式是相交理论的里程碑，因为它用同调代数的方法精确定义了相交重数。然而，Tor-公式要求 $A$ 是正则的（或至少是局部完全交的），不适用于任意概形。

Fulton 的 refined intersection product 可以看作是 Tor-公式的几何化推广：它将相交积定义为法锥上的某种"自交"，在正则情形下退化为 Serre 的公式。

### 6.3 后续发展： motivic 相交理论

Voevodsky 在 2000 年左右发展的 **motivic 上同调**为相交理论提供了新的框架。 motivic 上同调将 Chow 群作为特例（$H^{2i}_{\mathcal{M}}(X, \mathbb{Z}(i)) = A^i(X)$），并提供了更丰富的结构（如 Steenrod 运算、Atiyah-Hirzebruch 谱序列等）。

这一发展再次验证了 Grothendieck 的哲学洞察：正确的框架应当足够普遍，以包含经典理论作为特例。

### 6.4 形式化的挑战

相交理论的形式化面临着多重挑战：

1. **有理等价的定义**：有理等价涉及到 $X \times \mathbb{P}^1$ 上的族和纤维，这在类型论中需要仔细的构造；
2. **Chow 移动引理**：将闭链移动到一般位置的论证需要大量的维数理论和横截性结果；
3. **Fulton 的法锥构造**：法锥是 $X$ 上的相对概形，其定义涉及分次代数和理想幂的商；
4. **Chern 类的分裂原理**：flag bundle 的构造和射影丛公理的迭代需要大量的层论和向量丛理论。

Mathlib4 中目前缺乏系统性的相交理论基础，但 Chow 环和陈类的某些特殊情形（如射影空间上的计算）已经开始出现。

---

## 7. 参考文献与延伸阅读

### 原始文献

1. Grothendieck, A. *La théorie des classes de Chern*, *Bull. Soc. Math. France* **86** (1958), 137–154.
2. Berthelot, P. et al. *SGA 6: Théorie des intersections et théorème de Riemann-Roch*, LNM 225, Springer, 1971.
3. Fulton, W. *Intersection Theory*, 2nd ed., Springer, 1998.

### 教材与专著

1. Eisenbud, D. & Harris, J. *3264 and All That: A Second Course in Algebraic Geometry*, Cambridge Univ. Press, 2016.
2. Milnor, J. & Stasheff, J. *Characteristic Classes*, Princeton Univ. Press, 1974.
3. Vakil, R. *The Rising Sea*, 在线草稿，Ch. 20–22.

### 数据库

1. Stacks Project, Tag 02RF: *Chow groups*. https://stacks.math.columbia.edu/tag/02RF
2. nLab: *Intersection theory*. https://ncatlab.org/nlab/show/intersection+theory

---

> **审校状态**：草稿（draft）。相交理论的完整形式化需要 Chow 环、法锥和 Gysin 映射的系统开发。
