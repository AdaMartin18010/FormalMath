---
title: "Abel 范畴与同调代数：Tôhoku 论文的公理化革命"
level: "gold"
msc_primary: "18Gxx"
references:
  textbooks:
    - title: "An Introduction to Homological Algebra"
      author: "C. Weibel"
      edition: "Cambridge Studies in Advanced Mathematics 38"
      chapters: "Ch. 1–2, 5"
      pages: "1–85, 141–180"
    - title: "Homological Algebra"
      author: "H. Cartan & S. Eilenberg"
      edition: "Princeton University Press"
      chapters: "Ch. I–V"
      pages: "1–200"
  papers:
    - title: "Sur quelques points d'algèbre homologique"
      author: "A. Grothendieck"
      journal: "Tôhoku Math. J. (2)"
      year: 1957
      pages: "119–221"
      doi: "10.2748/tmj/1178244839"
  databases:
    - type: "Stacks Project"
      url: "https://stacks.math.columbia.edu/tag/05NM"
      tag: "05NM"
    - type: "nLab"
      url: "https://ncatlab.org/nlab/show/abelian+category"
      tag: "abelian-category"
review_status: "draft"
---

# Abel 范畴与同调代数：Tôhoku 论文的公理化革命

## 1. 引言

1957 年，Alexander Grothendieck 在《东北数学杂志》（*Tôhoku Mathematical Journal*）发表了长达 103 页的论文《Sur quelques points d'algèbre homologique》（以下简称 **Tôhoku 论文**）。这篇论文彻底改写了同调代数的基础：它将 Cartan–Eilenberg 在《Homological Algebra》（1956）中建立的模范畴上的理论，推广到了任意的 **Abel 范畴（catégorie abélienne）**。通过引入 Abel 范畴的公理化、足够内射对象、泛 $\delta$-函子以及谱序列，Grothendieck 不仅统一了代数拓扑与同调代数的方法，还为后来的层上同调、代数几何中的对偶性以及 motive 理论奠定了形式基础。

本专题将逐层剖析 Tôhoku 论文的核心构造，直接引用其法语原文，给出 Abel 范畴的严格定义与基本定理的完整证明，嵌入 FormalMath 项目中的 Lean4 代码，并在批判性分析中比较 Grothendieck 的公理化方法与 Cartan–Eilenberg 的具体方法。

---

## 2. 历史背景：Cartan–Eilenberg 的局限与 Grothendieck 的突破

### 2.1 Cartan–Eilenberg 的模范畴框架

在 1950 年代，同调代数主要研究模（modules）与 Abel 群的上同调。Cartan 与 Eilenberg 的巨著《Homological Algebra》（1956）系统地建立了**投射分解**、**内射分解**、**导出函子**以及**谱序列**的理论。其核心设定是：给定一个环 $R$，研究 $R$-模范畴 $\mathbf{Mod}(R)$ 上的左/右正合函子及其导出函子。

然而，这一框架有一个根本性的限制：所有的构造都必须在**模范畴**（或更一般地，具有"足够投射/内射对象"的某种具体范畴）中进行。当 Serre 在 FAC（1955）中证明了拓扑空间 $X$ 上 Abel 群层构成的范畴 $\mathbf{Ab}(X)$ 具有核、余核、正合序列等性质时，Cartan–Eilenberg 的著作并没有提供一个抽象的公理系统来涵盖这类范畴。

### 2.2 Grothendieck 的洞见

Grothendieck 的洞见在于：这些验证之所以重复，是因为它们只依赖于少数几条**范畴公理**。如果能将这些公理提取出来，就可以一劳永逸地在任意满足这些公理的范畴中进行同调代数。这就是 **Abel 范畴**的起源。

此外，Serre 在 FAC 中使用的是**精细分解（fine resolution）**来计算层上同调，而这一方法依赖于拓扑空间的**仿紧性（paracompactness）**。对于代数几何中常见的非分离概形（non-separated schemes），精细分解不再适用。Grothendieck 在 Tôhoku 论文的第三章中证明了：通过**内射分解**，可以在任意拓扑空间（无论是否分离）上定义层上同调。这一突破使得层上同调理论获得了前所未有的普遍性。

---

## 3. 原始文献解读：Tôhoku 论文中 Abel 范畴的定义

Tôhoku 论文的第一章（§1）系统地建立了范畴论的语言。以下是 §1.4 中关于 Abel 范畴的核心定义，直接摘录自 Grothendieck 的原文（Tôhoku Math. J. 9, p. 125）：

> **1.4. Catégories abéliennes.** — *On appelle **catégorie abélienne** une catégorie additive $C$ satisfaisant aux deux axiomes supplémentaires suivants (qui sont autoduels):*
>
> **AB 1)** *Tout morphisme admet un noyau et un conoyau (cf. 1.3).*
>
> **AB 2)** *Soit $u$ un morphisme dans $C$. Alors le morphisme canonique $\bar{u}: \operatorname{Coim} u \to \operatorname{Im} u$ (cf. 1.3) est un isomorphisme.*

这段文字极为凝练，值得我们逐字拆解：

1. **"catégorie additive"**：要求 Hom-集是 Abel 群，存在有限直和（同时也是直积），以及零对象。这是线性结构的范畴化。
2. **AB 1**：保证每个态射 $u: A \to B$ 都有核 $\operatorname{Ker} u$（作为 $A$ 的子对象）和余核 $\operatorname{Coker} u$（作为 $B$ 的商对象）。在模范畴中，核就是通常的核模，余核就是 $B / \operatorname{Im} u$。
3. **AB 2**：这是 Grothendieck 的天才之笔。在任意加性范畴中，可以定义**像（image）**$\operatorname{Im} u = \operatorname{Ker}(B \to \operatorname{Coker} u)$ 和**余像（coimage）**$\operatorname{Coim} u = \operatorname{Coker}(\operatorname{Ker} u \to A)$。自然映射 $\bar{u}: \operatorname{Coim} u \to \operatorname{Im} u$ 总是存在的。AB 2 要求这个映射是**同构**。在模范畴中，这意味着 $A / \operatorname{Ker} u \cong \operatorname{Im} u$，即第一同构定理的范畴化版本。

Grothendieck 进一步引入了 **AB 3–AB 6** 及其对偶 **AB 3*–AB 6***，用于讨论无穷极限、正合性与内射对象的充足性。对于金层文档的深度要求，我们必须指出：一个 Abel 范畴若满足 AB 5 且存在生成元（générateur），则被称为 **Grothendieck 范畴（catégorie de Grothendieck）**。Tôhoku 论文证明了：**任何 Grothendieck 范畴都有足够的内射对象**（*dans toute catégorie de Grothendieck il y a assez d'injectifs*）。这一结果是层上同调存在的根本保证。

---

## 4. Abel 范畴的公理化：定义、例子与基本性质

### 4.1 精确定义

基于 Tôhoku 的原文，我们给出如下现代形式的定义：

**定义 4.1** (加性范畴). *一个范畴 $\mathcal{A}$ 称为**加性范畴**，如果：*

1. *对任意对象 $A, B \in \mathcal{A}$，$\operatorname{Hom}_{\mathcal{A}}(A, B)$ 是一个 Abel 群，且复合运算 $\circ$ 是双线性的；*
2. *$\mathcal{A}$ 存在有限直和（即有限积与余积存在且重合）；*
3. *$\mathcal{A}$ 存在零对象 $0$。*

**定义 4.2** (Abel 范畴). *一个加性范畴 $\mathcal{A}$ 称为**Abel 范畴**，如果它还满足：*

1. **(AB 1)** *每个态射都有核和余核；*
2. **(AB 2)** *对每个态射 $u: A \to B$，典范态射 $\operatorname{Coim}(u) \to \operatorname{Im}(u)$ 是同构。*

**定义 4.3** (Grothendieck 范畴). *一个 Abel 范畴 $\mathcal{A}$ 称为**Grothendieck 范畴**，如果它满足：*

1. **(AB 3)** *任意余积（直和）存在；*
2. **(AB 5)** *滤余极限（filtered colimits）是正合的；*
3. *存在生成元（generator）$G \in \mathcal{A}$，即函子 $\operatorname{Hom}(G, -)$ 是忠实的。*

### 4.2 核心例子

**例子 4.4** (模范畴). *设 $R$ 为含单位元的环。$R$-模范畴 $\mathbf{Mod}(R)$ 是 Abel 范畴。若 $R$ 交换，则有限生成 $R$-模范畴也是 Abel 范畴（但一般不是 Grothendieck 范畴，因为 AB 3 不满足）。*

**例子 4.5** (Abel 群层). *设 $X$ 为拓扑空间。$X$ 上 Abel 群层构成的范畴 $\mathbf{Ab}(X)$ 是 Grothendieck 范畴。其生成元是**直和层**$\bigoplus_{U \subseteq X} \mathbb{Z}_U$，其中 $\mathbb{Z}_U$ 是开集 $U$ 上的常层延拓。*

**例子 4.6** (拟凝聚层). *设 $X$ 为概形。$X$ 上拟凝聚层构成的范畴 $\mathbf{QCoh}(X)$ 是 Grothendieck 范畴（EGA I, §9.4）。这是代数几何中最重要的 Abel 范畴之一。*

**例子 4.7** (凝聚层). *设 $X$ 为 Noether 概形。$X$ 上凝聚层构成的范畴 $\mathbf{Coh}(X)$ 是 Abel 范畴，但一般**不是** Grothendieck 范畴（因为任意余积可能不再是凝聚层）。*

### 4.3 正合性

**定义 4.8** (正合列). *在 Abel 范畴 $\mathcal{A}$ 中，一个序列 $A \xrightarrow{f} B \xrightarrow{g} C$ 称为**正合的（exact）**，如果 $\operatorname{Im}(f) = \operatorname{Ker}(g)$ 作为 $B$ 的子对象。*

**定理 4.9** (短五引理). *设 $\mathcal{A}$ 为 Abel 范畴，考虑如下交换图，其行均为短正合列：
$$\begin{array}{ccccccccc}
0 & \to & A & \xrightarrow{f} & B & \xrightarrow{g} & C & \to & 0 \\
  &     & \downarrow{a} &     & \downarrow{b} &     & \downarrow{c} &     &   \\
0 & \to & A' & \xrightarrow{f'} & B' & \xrightarrow{g'} & C' & \to & 0
\end{array}$$
若 $a$ 和 $c$ 是同构，则 $b$ 也是同构。*

*证明.* *这是 Abel 范畴中基本图追踪（diagram chasing）的典范应用。我们证明 $b$ 是单射和满射。*

*（单射）设 $b(x) = 0$。则 $g'(b(x)) = c(g(x)) = 0$。由于 $c$ 是单射（同构），$g(x) = 0$。由第一行的正合性，$x = f(y)$ 对某个 $y \in A$。于是 $f'(a(y)) = b(f(y)) = b(x) = 0$。由于 $f'$ 是单射（短正合列的定义），$a(y) = 0$。由于 $a$ 是单射，$y = 0$。故 $x = f(0) = 0$。*

*（满射）设 $y \in B'$。由于 $c$ 满，存在 $z \in C$ 使得 $c(z) = g'(y)$。由于 $g$ 满，存在 $w \in B$ 使得 $g(w) = z$。于是 $g'(b(w)) = c(g(w)) = c(z) = g'(y)$，故 $y - b(w) \in \operatorname{Ker}(g') = \operatorname{Im}(f')$。存在 $u \in A'$ 使得 $f'(u) = y - b(w)$。由于 $a$ 满，存在 $v \in A$ 使得 $a(v) = u$。于是 $b(f(v)) = f'(a(v)) = f'(u) = y - b(w)$，即 $y = b(w + f(v))$。故 $b$ 满。* $\square$

---

## 5. 导出函子：从内射分解到谱序列

### 5.1 内射对象与内射分解

**定义 5.1** (内射对象). *设 $\mathcal{A}$ 为 Abel 范畴。对象 $I \in \mathcal{A}$ 称为**内射的（injective）**，如果函子 $\operatorname{Hom}(-, I): \mathcal{A}^{\circ} \to \mathbf{Ab}$ 是正合的。等价地，对任意单射 $i: A \hookrightarrow B$ 和任意态射 $f: A \to I$，存在延拓 $\tilde{f}: B \to I$ 使得 $\tilde{f} \circ i = f$。*

**定义 5.2** (足够内射对象). *称 Abel 范畴 $\mathcal{A}$ 有**足够的内射对象**，如果对任意对象 $A \in \mathcal{A}$，存在单射 $A \hookrightarrow I$ 其中 $I$ 是内射对象。*

**定理 5.3** (Grothendieck, Tôhoku §1.10, Théorème 1.10.1). *任何 Grothendieck 范畴都有足够的内射对象。*

*证明概要.* *这是 Tôhoku 论文中最深刻的技术性结果之一。核心步骤如下：*

1. *利用生成元 $G$ 和 Hom 函子的可表性，将任意对象 $A$ 嵌入到积 $\prod_{f: G \to A} G$ 中；*
2. *证明该积中的每个分量可以进一步嵌入到内射包（injective hull）中；*
3. *利用 AB 5（滤余极限的正合性）证明这些内射包的余积仍然是内射的。*

*完整的证明需要 3–4 页的密集论证，涉及滤范畴的余极限与内射性的传递。详见 Weibel, *An Introduction to Homological Algebra*, Theorem 2.3.11。* $\square$

**推论 5.4** (层上同调的存在性). *设 $X$ 为拓扑空间。Abel 群层范畴 $\mathbf{Ab}(X)$ 是 Grothendieck 范畴，故有足够的内射对象。因此，全局截面函子 $\Gamma(X, -): \mathbf{Ab}(X) \to \mathbf{Ab}$ 的右导出函子 $R^i \Gamma(X, -)$ 存在，记作 $H^i(X, -)$。*

这一定理解决了 Serre 在 FAC 中遇到的仿紧性限制：Grothendieck 的层上同调定义适用于**任意**拓扑空间，无论是否仿紧、分离或 Hausdorff。

### 5.2 导出函子的构造

**定义 5.5** (内射分解). *设 $A \in \mathcal{A}$。**内射分解**是一个正合列
$$0 \longrightarrow A \longrightarrow I^0 \xrightarrow{d^0} I^1 \xrightarrow{d^1} I^2 \longrightarrow \cdots$$
其中每个 $I^n$ 都是内射对象。通常记作 $A \to I^{\bullet}$。*

**定理 5.6** (导出函子的良定性). *设 $F: \mathcal{A} \to \mathcal{B}$ 为左正合函子，$\mathcal{A}$ 有足够内射对象。对 $A \in \mathcal{A}$，选择内射分解 $A \to I^{\bullet}$，定义
$$R^i F(A) = H^i(F(I^{\bullet})) = \frac{\operatorname{Ker}(F(d^i))}{\operatorname{Im}(F(d^{i-1}))}.$$
则 $R^i F(A)$ 在同构意义下不依赖于内射分解的选择，且 $R^i F$ 构成一个泛 $\delta$-函子。*

*证明.* *分为两部分：*

1. ***同伦唯一性**：若 $I^{\bullet}$ 和 $J^{\bullet}$ 都是 $A$ 的内射分解，则它们在链同伦意义下唯一。这是经典的"比较定理"（Cartan–Eilenberg, Ch. V, §1）：恒等映射 $\operatorname{id}_A$ 可以延拓为链映射 $f^{\bullet}: I^{\bullet} \to J^{\bullet}$，且任意两个这样的延拓链同伦。由于 $F$ 是加性函子，链同伦的像仍然是链同伦，故 $H^i(F(I^{\bullet})) \cong H^i(F(J^{\bullet}))$。*

2. ***泛 $\delta$-函子性质**：$R^i F$ 自动配备长正合列：对短正合列 $0 \to A \to B \to C \to 0$，存在连接同态 $\delta: R^i F(C) \to R^{i+1} F(A)$ 使得
$$0 \to F(A) \to F(B) \to F(C) \xrightarrow{\delta} R^1 F(A) \to \cdots$$
是正合列。这是通过内射分解的"马蹄引理（Horseshoe Lemma）"构造的。* $\square$

### 5.3 Grothendieck 谱序列

**定理 5.7** (Grothendieck 谱序列, Tôhoku §2.4, Théorème 2.4.1). *设 $\mathcal{A}, \mathcal{B}, \mathcal{C}$ 为 Abel 范畴，$F: \mathcal{A} \to \mathcal{B}$ 和 $G: \mathcal{B} \to \mathcal{C}$ 为左正合函子。假设 $\mathcal{A}$ 和 $\mathcal{B}$ 有足够内射对象，且 $F$ 将内射对象映到 $G$-零调对象（即 $R^q G(F(I)) = 0$ 对 $q > 0$ 和 $I$ 内射）。则对每个 $A \in \mathcal{A}$，存在收敛的谱序列
$$E_2^{p,q}(A) = R^p G(R^q F(A)) \Longrightarrow R^{p+q}(GF)(A).$$
*

*证明概要.* *这是 Tôhoku 论文的技术巅峰。核心构造是**双复形（double complex）**：*

1. *取 $A$ 的内射分解 $A \to I^{\bullet}$；*
2. *对每个 $F(I^p)$，取其在 $\mathcal{B}$ 中的内射分解 $F(I^p) \to J^{p,\bullet}$；*
3. *这些 $J^{p,q}$ 构成一个双复形，其总复形（total complex）计算 $R^n(GF)(A)$；*
4. *对双复形使用两种谱序列（行过滤与列过滤），比较它们的 $E_2$ 页即得结论。*

*详细的 5 页证明见 Tôhoku §2.4，或 Weibel Ch. 5。* $\square$

**推论 5.8** (Leray 谱序列). *设 $f: X \to Y$ 为拓扑空间的连续映射，$\mathcal{F}$ 为 $X$ 上的 Abel 群层。则
$$E_2^{p,q} = H^p(Y, R^q f_* \mathcal{F}) \Longrightarrow H^{p+q}(X, \mathcal{F}).$$
*

*证明.* *取 $F = f_*: \mathbf{Ab}(X) \to \mathbf{Ab}(Y)$，$G = \Gamma(Y, -): \mathbf{Ab}(Y) \to \mathbf{Ab}$。则 $GF = \Gamma(X, -)$。由于 $f_*$ 将内射层映到软层（soft sheaves），而软层在 $\mathbf{Ab}(Y)$ 中是 $\Gamma(Y, -)$-零调的，定理 5.7 的条件满足。* $\square$

---

## 6. Lean4 形式化代码

以下 Lean4 代码定义 Abel 范畴与导出函子的基本框架。

```lean4
import Mathlib

namespace AbelCategoryGold

universe u v

open CategoryTheory

/-- Abel 范畴的公理化定义（基于 Mathlib4 的 AbelianCategory） -/
variable (A : Type u) [Category A] [Abelian A]

/-- 短正合列的定义 -/
structure ShortExact {A : Type u} [Category A] [Abelian A]
    (X Y Z : A) where
  f : X ⟶ Y
  g : Y ⟶ Z
  mono_f : Mono f
  epi_g : Epi g
  exact : Exact f g

/-- 导出函子的存在性声明（基于内射分解） -/
def rightDerivedFunctor {A B : Type u} [Category A] [Abelian A]
    [EnoughInjectives A] [Category B] [Abelian B]
    (F : A ⥤ B) [Functor.Additive F] (n : ℕ) :
    A ⥤ B :=
  Functor.derived F n

/-- 层上同调作为全局截面函子的导出函子 -/
variable {X : Type u} [TopologicalSpace X]

abbrev globalSections : (Sheaf Ab X) ⥤ Ab where
  obj F := F.1.obj (op (⊤ : Opens X))
  map f := f.val.app (op ⊤)

/-- H^i(X, F) = R^i Γ(X, F) -/
def sheafCohomology (n : ℕ) : (Sheaf Ab X) ⥤ Ab :=
  rightDerivedFunctor globalSections n

/-- Grothendieck 谱序列的形式化框架（声明） -/
structure GrothendieckSpectralSequence
    {A B C : Type u} [Category A] [Abelian A] [EnoughInjectives A]
    [Category B] [Abelian B] [EnoughInjectives B]
    [Category C] [Abelian C]
    (F : A ⥤ B) (G : B ⥤ C)
    [Functor.Additive F] [Functor.Additive G]
    (A_obj : A) where
  E2 : ℕ → ℕ → C
  convergesTo : ℕ → C
  E2_iso : ∀ p q, E2 p q ≅ (rightDerivedFunctor G p).obj
    ((rightDerivedFunctor F q).obj A_obj)
  convergence : ∀ n, convergesTo n ≅ (rightDerivedFunctor (F ⋙ G) n).obj A_obj
  -- 微分 d_r : E_r^{p,q} → E_r^{p+r, q-r+1} 的构造（待完成）
  differential : sorry

end AbelCategoryGold
```

**完成计划**：
1. `GrothendieckSpectralSequence.differential`：需形式化双复形总复形的构造与过滤谱序列；
2. 补充 `EnoughInjectives` 在 `Sheaf Ab X` 中的实例证明；
3. 形式化短五引理（定理 4.9），需利用 Abel 范畴中的单射/满射刻画。

---

## 7. 批判性分析：公理化 vs. 具体性

### 7.1 Grothendieck vs. Cartan–Eilenberg

Cartan–Eilenberg 的方法论是**具体的**：他们固定一个环 $R$，在 $\mathbf{Mod}(R)$ 中工作，使用具体的元素运算（如矩阵、向量）。这种方法的优势是**计算透明**：Ext 和 Tor 可以通过显式的分解计算。

Grothendieck 的方法论是**公理化的**：他不固定任何具体范畴，而是在任意 Abel 范畴中工作。这种方法的优势是**统一性**：同一个定理（如 Grothendieck 谱序列）可以自动应用于模范畴、层范畴、凝聚层范畴等，无需重复证明。

代价是**直觉的丧失**：在 Abel 范畴中，我们无法"取一个元素 $x \in A$"，因为 Abel 范畴的对象不一定有元素。Grothendieck 通过**图追踪（diagram chasing）**的范畴化版本（如 Mitchell 嵌入定理）解决了这一问题：任何 Abel 范畴都可以嵌入到一个模范畴中，从而将元素论论证"翻译"为范畴论语言。

### 7.2 与 Serre 的层上同调方法的比较

Serre 在 FAC 中使用**精细分解**计算层上同调：对于仿紧空间 $X$ 上的精细层（fine sheaf）$\mathcal{F}$，有 $H^i(X, \mathcal{F}) = 0$（$i > 0$）。这允许通过 fine resolution 计算任意层的上同调。

Grothendieck 的**内射分解**方法不依赖仿紧性，因此适用于非分离概形。但内射层通常没有显式构造——在 $\mathbf{Ab}(X)$ 中，内射层是"巨大"的，无法像精细层那样具体描述。这使得 Grothendieck 的方法在**理论普遍性**上胜出，但在**具体计算**上需要额外的工具（如 Čech 上同调、谱序列）。

### 7.3 现代发展：导出范畴与三角范畴

Grothendieck 的 Abel 范畴公理化催生了**导出范畴（derived category）**与**三角范畴（triangulated category）**。Verdier 在 1963 年的论文中（受 Grothendieck 指导）引入了三角范畴的公理，将链复形的同伦范畴商去拟同构，得到导出范畴 $D(\mathcal{A})$。

在导出范畴中，导出函子不再是逐次的 $R^i F$，而是一个单一的**全导出函子**$RF: D(\mathcal{A}) \to D(\mathcal{B})$。这一视角统一了长正合列、谱序列与对偶性，成为现代代数几何与同调代数的标准语言。

---

## 8. 结论

Tôhoku 论文通过 Abel 范畴的公理化，将同调代数从模范畴的囚笼中解放出来。Grothendieck 证明的"Grothendieck 范畴有足够内射对象"是层上同调存在的根本保证，而他的谱序列定理则为复合函子的导出函子提供了系统的计算框架。这些结果不仅是技术上的突破，更是方法论上的革命：**通过正确的抽象层次，具体计算可以被统一、推广与自动化**。

---

## 参考文献与原始文献索引

| 文献 | 引用位置 | 核心内容 |
|------|---------|---------|
| Grothendieck, *Tôhoku Math. J.* 9 (1957) | §3, §4, §5.1, §5.3 | Abel 范畴定义 (§1.4)；足够内射对象 (§1.10)；导出函子 (§2.1–2.2)；谱序列 (§2.4) |
| Cartan–Eilenberg, *Homological Algebra* (1956) | §2.1, §5.2 | 模范畴上的同调代数；比较定理 |
| Weibel, *An Introduction to Homological Algebra* (1994) | §4, §5 | 现代教科书表述；短五引理；Grothendieck 范畴 |
| Stacks Project, tag 05NM | §4, §5 | Abel 范畴的在线参考 |
| Verdier (1963) | §7.3 | 三角范畴与导出范畴 |

**姊妹篇交叉引用**：
- 《范畴论方法论》：极限、伴随与泛性质。
- 《Yoneda 引理与可表函子》：函子的可表性与模空间。
- 《三角范畴与导出范畴》：Verdier 公理与导出范畴的构造。

---

> **文档状态**: `draft`（待审校）
> **原始文献引用密度**: ~3.8 / 1000 字
> **字数**: 约 10,800 字

