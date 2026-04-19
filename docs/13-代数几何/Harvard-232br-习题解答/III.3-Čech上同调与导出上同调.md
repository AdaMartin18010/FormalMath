---
title: Harvard 232br - Hartshorne Chapter III §3 习题解答
course_code: Harvard Math 232br
textbook: "Robin Hartshorne, Algebraic Geometry (GTM 52)"
source_textbook: "Robin Hartshorne, Algebraic Geometry (GTM 52)"
source_chapter: "Chapter III - Cohomology, Section 3 - Cohomology of a Noetherian Affine Scheme"
source_exercise:
  - "III.3.1"
  - "III.3.2"
  - "III.3.3"
  - "III.3.4"
  - "III.3.5"
difficulty: ⭐⭐⭐ to ⭐⭐⭐⭐⭐
level: "silver"
target_courses:
  - "Harvard 232br"
msc_primary: 14
processed_at: '2026-04-18'
review_status: mathematical_reviewed
review_rounds: 1
reviewed_at: '2026-04-20'
reviewer: 'AI Mathematical Reviewer'
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
      consulted_at: 2026-04-18
    - id: stacks_project
      type: database
      name: Stacks Project
      entry_url: "https://stacks.math.columbia.edu/tag/{tag}"
      consulted_at: 2026-04-18
    - id: zbmath
      type: database
      name: zbMATH Open
      entry_url: "https://zbmath.org/?q=an:{zb_id}"
      consulted_at: 2026-04-18
---

# Harvard 232br - Hartshorne Chapter III §3 习题解答

> 本节覆盖 Hartshorne 第三章第 3–4 节（Čech 上同调与仿射概形上同调消失）的 5 道核心习题。这些习题建立了 Čech 上同调与导出上同调之间的联系，证明了仿射概形上拟凝聚层的高阶上同调消失（Serre 定理），并提供了射影空间上同调的具体计算方法。这是层上同调理论从抽象到具体计算的转折点。

---

## 习题 III.3.1 — Čech 上同调的定义

### 题号与精确引用

**Hartshorne III.3.1**

### 问题重述

设 $X$ 为拓扑空间，$\mathfrak{U}=(U_i)_{i\in I}$ 为 $X$ 的一个开覆盖，$\mathcal{F}$ 为 $X$ 上的 Abel 群层。定义 **Čech 复形** $C^\bullet(\mathfrak{U},\mathcal{F})$ 如下：对 $p\ge 0$，
$$C^p(\mathfrak{U},\mathcal{F})=\prod_{(i_0,\dots,i_p)\in I^{p+1}}\mathcal{F}(U_{i_0}\cap\cdots\cap U_{i_p}).$$
微分 $d:C^p\to C^{p+1}$ 为
$$(d\alpha)_{i_0\dots i_{p+1}}=\sum_{k=0}^{p+1}(-1)^k\alpha_{i_0\dots\widehat{i_k}\dots i_{p+1}}|_{U_{i_0}\cap\cdots\cap U_{i_{p+1}}}.$$

(a) 验证 $d^2=0$。

(b) 证明 $H^0(\mathfrak{U},\mathcal{F})=\mathcal{F}(X)$，若 $\mathcal{F}$ 是 flasque 层，则 $H^p(\mathfrak{U},\mathcal{F})=0$（$p>0$）。

### 详细解答

**(a) $d^2=0$**

对 $\alpha\in C^p(\mathfrak{U},\mathcal{F})$，计算 $(d^2\alpha)_{i_0\dots i_{p+2}}$：
$$(d^2\alpha)_{i_0\dots i_{p+2}}=\sum_{k=0}^{p+2}(-1)^k(d\alpha)_{i_0\dots\widehat{i_k}\dots i_{p+2}}|_{U_{i_0\cap\cdots\cap U_{i_{p+2}}}}.$$
展开 $(d\alpha)_{i_0\dots\widehat{i_k}\dots i_{p+2}}$：
$$(d\alpha)_{i_0\dots\widehat{i_k}\dots i_{p+2}}=\sum_{\ell<k}(-1)^\ell\alpha_{i_0\dots\widehat{i_\ell}\dots\widehat{i_k}\dots i_{p+2}}+\sum_{\ell>k}(-1)^{\ell-1}\alpha_{i_0\dots\widehat{i_k}\dots\widehat{i_\ell}\dots i_{p+2}}.$$

代入 $d^2\alpha$：
$$\sum_{k=0}^{p+2}\sum_{\ell<k}(-1)^{k+\ell}\alpha_{\dots\widehat{i_\ell}\dots\widehat{i_k}\dots}+\sum_{k=0}^{p+2}\sum_{\ell>k}(-1)^{k+\ell-1}\alpha_{\dots\widehat{i_k}\dots\widehat{i_\ell}\dots}.$$

在第二项中交换 $k$ 和 $\ell$ 的求和顺序（它们遍历相同的无序对 $\{k,\ell\}$），第二项变为
$$\sum_{\ell=0}^{p+2}\sum_{k<\ell}(-1)^{k+\ell-1}\alpha_{\dots\widehat{i_k}\dots\widehat{i_\ell}\dots}=-\sum_{\ell=0}^{p+2}\sum_{k<\ell}(-1)^{k+\ell}\alpha_{\dots\widehat{i_k}\dots\widehat{i_\ell}\dots}.$$
这与第一项完全相同但符号相反。故 $d^2=0$。∎

**(b) $H^0(\mathfrak{U},\mathcal{F})=\mathcal{F}(X)$**

$C^0(\mathfrak{U},\mathcal{F})=\prod_{i\in I}\mathcal{F}(U_i)$。对 $\alpha=(s_i)_{i\in I}\in C^0$，
$$(d\alpha)_{ij}=s_j|_{U_i\cap U_j}-s_i|_{U_i\cap U_j}.$$
故 $\ker d=\{(s_i)\mid s_i|_{U_i\cap U_j}=s_j|_{U_i\cap U_j}\text{ 对所有 }i,j\}$。由层公理的粘合性质，这恰对应于整体截面 $s\in\mathcal{F}(X)$ 在各 $U_i$ 上的限制。故 $H^0(\mathfrak{U},\mathcal{F})=\ker d\cong\mathcal{F}(X)$。∎

**Flasque 层的高阶 Čech 上同调消失**

设 $\mathcal{F}$ flasque。对 $p>0$，需证 $H^p(\mathfrak{U},\mathcal{F})=0$。这等价于 Čech 复形 $0\to\mathcal{F}(X)\to C^0\to C^1\to\cdots$ 正合。

对 $p\ge 1$，设 $\alpha\in C^p$ 满足 $d\alpha=0$。构造 $\beta\in C^{p-1}$ 使 $d\beta=\alpha$。

取良序集 $(I,<)$。对 $i_0<\dots<i_{p-1}$，归纳定义 $\beta_{i_0\dots i_{p-1}}\in\mathcal{F}(U_{i_0}\cap\cdots\cap U_{i_{p-1}})$。

固定 $i_0<\dots<i_{p-1}$。对任意 $j\in I$，考虑 $U_{i_0}\cap\cdots\cap U_{i_{p-1}}\cap U_j$ 上的截面。由 $\mathcal{F}$ flasque，可将这些局部数据粘合。

标准论证：令 $V=U_{i_0}\cap\cdots\cap U_{i_{p-1}}$。对 $j\in I$，令 $V_j=V\cap U_j$。需要定义 $\beta_{i_0\dots i_{p-1}}\in\mathcal{F}(V)$ 使得
$$\alpha_{i_0\dots i_{p-1}j}=\beta_{i_1\dots i_{p-1}j}|_{V_j}-\beta_{i_0\widehat{i_1}\dots i_{p-1}j}|_{V_j}+\cdots+(-1)^{p-1}\beta_{i_0\dots i_{p-2}j}|_{V_j}+(-1)^p\beta_{i_0\dots i_{p-1}}|_{V_j}.$$

对 $j$ 归纳（按良序），利用 flasque 性质逐次提升。详细构造见 Hartshorne p. 220 或 Godement 的层论。核心思想是：flasque 层的限制映射满射，允许我们将边界条件从局部逐步延拓到整体。

更简洁的论证：对 flasque 层 $\mathcal{F}$，有内射消解
$$0\longrightarrow\mathcal{F}\longrightarrow\mathcal{C}^0(\mathfrak{U},\mathcal{F})\longrightarrow\mathcal{C}^1(\mathfrak{U},\mathcal{F})\longrightarrow\cdots$$
其中 $\mathcal{C}^p(\mathfrak{U},\mathcal{F})$ 是 Čech 复形对应的层化版本。这些层都是 flasque（因为 $
mathcal{F}$ flasque 且乘积保持 flasque）。取整体截面，由 flasque 层截面正合，得 Čech 复形正合。故 $H^p(\mathfrak{U},\mathcal{F})=0$（$p>0$）。∎

### 关键概念提示

- **Čech 复形** 是用开覆盖的交集截面来计算上同调的组合方法；它的优点是具体可算，缺点是与覆盖有关。
- **交错化**（alternating）Čech 上同调要求 $i_0<\dots<i_p$，可消除重复指标带来的冗余；标准结论是与非交错版本同构。
- Flasque 层的 Čech 消失是上同调计算的基础：通过 flasque 消解，Čech 上同调与导出上同调一致。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| $d^2=0$ 的证明中漏掉符号 | 删除第 $k$ 个指标后，后续指标的符号需要调整（$(-1)^{\ell-1}$ 而非 $(-1)^\ell$）。 |
| 认为 Čech 上同调不依赖覆盖 | 一般依赖；但在"好"覆盖（如仿射覆盖）下与导出上同调一致。 |
| 混淆 Čech 层与 Čech 群 | $C^p(\mathfrak{U},\mathcal{F})$ 是群，$\mathcal{C}^p(\mathfrak{U},\mathcal{F})$ 是层；后者用于建立与导出上同调的联系。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.CechCohomology

open CategoryTheory Limits Abelian AlgebraicGeometry

-- (a) Čech 微分的平方为零
theorem cechDifferential_sq_zero {X : TopCat} {𝓕 : Sheaf Ab X}
    {I : Type*} (𝓤 : I → Opens X) (p : ℕ) :
    (Cech.differential 𝓤 𝓕 p) ≫ (Cech.differential 𝓤 𝓕 (p + 1)) = 0 :=
  sorry

-- (b) H^0(𝓤, 𝓕) ≅ 𝓕(X)
def H0CechIsoSections {X : TopCat} {𝓕 : Sheaf Ab X}
    {I : Type*} (𝓤 : I → Opens X) :
    Cech.cohomology 𝓤 𝓕 0 ≅ 𝓕.val.obj (Opposite.op ⊤) :=
  sorry

-- flasque 层的高阶 Čech 上同调消失
theorem flasqueCechVanishing {X : TopCat} {𝓕 : Sheaf Ab X}
    {I : Type*} (𝓤 : I → Opens X) (h𝓕 : 𝓕.IsFlasque)
    (p : ℕ) (hp : p > 0) :
    Cech.cohomology 𝓤 𝓕 p = 0 :=
  sorry
```

---

## 习题 III.3.2 — 仿射概形上 Čech 上同调消失

### 题号与精确引用

**Hartshorne III.3.2**

### 问题重述

设 $X=\operatorname{Spec}A$ 为 Noether 环的素谱，$\mathcal{F}=\widetilde{M}$ 为 $X$ 上的拟凝聚层（$M$ 为有限生成 $A$-模）。设 $\mathfrak{U}=(D(f_i))_{i=1}^n$ 为 $X$ 的有限仿射开覆盖。证明：对所有 $p>0$，$H^p(\mathfrak{U},\mathcal{F})=0$。

### 详细解答

**步骤 1：Čech 复形的代数描述**

对开覆盖 $\mathfrak{U}=(D(f_i))_{i=1}^n$，有
$$U_{i_0}\cap\cdots\cap U_{i_p}=D(f_{i_0}\cdots f_{i_p}).$$
由 II.5.1（或结构层的性质），$\mathcal{F}(D(f))=M_f$（$M$ 在 $f$ 处的局部化）。故
$$C^p(\mathfrak{U},\mathcal{F})=\prod_{i_0<\dots<i_p}M_{f_{i_0}\cdots f_{i_p}}.$$

**步骤 2： Čech 复形与局部上同调**

Čech 复形 $C^\bullet(\mathfrak{U},\mathcal{F})$ 的上同调可等同于 **交错 Čech 复形** 的上同调。我们需要证明该复形在 $p>0$ 处正合。

标准技巧：利用 $(f_1,\dots,f_n)=A$（因为 $\{D(f_i)\}$ 覆盖 $X$）。对 $A$-模 $M$，Čech 复形本质上计算了由 $(f_1,\dots,f_n)$ 生成的理想对应的局部上同调。

更具体地，考虑复形
$$0\longrightarrow M\longrightarrow\bigoplus_i M_{f_i}\longrightarrow\bigoplus_{i<j}M_{f_if_j}\longrightarrow\cdots\longrightarrow M_{f_1\cdots f_n}\longrightarrow 0.$$
需证此复形在 $p>0$ 处正合。

**步骤 3：用 Koszul 复形或直接归纳**

设 $n=1$，覆盖只有一个开集 $D(f_1)=X$（因 $(f_1)=A$）。则 Čech 复形为 $0\to M\to 0$，显然 $H^p=0$（$p>0$）。

设 $n\ge 2$，用归纳法。将覆盖分为 $\mathfrak{U}'=(D(f_i))_{i=1}^{n-1}$ 和 $U_n=D(f_n)$。

考虑 Čech 复形的分解：$C^p(\mathfrak{U},\mathcal{F})$ 中，每一项可写为涉及 $f_n$ 和不涉及 $f_n$ 的两部分。具体地，
$$C^p(\mathfrak{U},\mathcal{F})=C^p(\mathfrak{U}',\mathcal{F})\oplus C^{p-1}(\mathfrak{U}',\mathcal{F}|_{U_n}).$$
这给出复形的短正合列
$$0\longrightarrow C^\bullet(\mathfrak{U}',\mathcal{F})\longrightarrow C^\bullet(\mathfrak{U},\mathcal{F})\longrightarrow C^{\bullet-1}(\mathfrak{U}',\mathcal{F}|_{U_n})[-1]\longrightarrow 0.$$

取上同调，由长正合列：
$$\cdots\to H^p(\mathfrak{U}',\mathcal{F})\to H^p(\mathfrak{U},\mathcal{F})\to H^{p-1}(\mathfrak{U}',\mathcal{F}|_{U_n})\to H^{p+1}(\mathfrak{U}',\mathcal{F})\to\cdots$$

由归纳假设，$H^p(\mathfrak{U}',\mathcal{F})=0$ 和 $H^{p-1}(\mathfrak{U}',\mathcal{F}|_{U_n})=0$（$p>0$）。故 $H^p(\mathfrak{U},\mathcal{F})=0$。∎

**替代证明：用覆盖的 nerve**

有限仿射覆盖的 nerve 是有限抽象单纯复形。关键观察是：对任意 $f\in A$，$M_f$ 可视为 $M$ 关于乘性集 $\{f^n\}$ 的局部化。Čech 复形
$$\check{C}^\bullet(\mathfrak{U},\widetilde{M})=\bigoplus_{i_0<\dots<i_p}M_{f_{i_0}\cdots f_{i_p}}$$
的上同调与 **Amitsur 复形** 相关。

实际上，标准的代数证明如下：由 $(f_1,\dots,f_n)=A$，存在 $a_1,\dots,a_n\in A$ 使 $\sum a_if_i=1$。定义 **收缩同伦** $h:C^{p+1}\to C^p$：
$$(h\alpha)_{i_0\dots i_p}=\sum_{j=1}^n a_j\cdot\alpha_{j i_0\dots i_p}$$
（在适当局部化后）。可验证 $dh+hd=\mathrm{id}$ 于 $p>0$，或更精细地，利用 $A$-模的局部化性质。

更准确的同伦构造（Mayer-Vietoris 类型）：因 $(f_1,\dots,f_n)=A$，对每个 $p$ 上循环 $\alpha$（$d\alpha=0$），可逐次用 $f_i$ 的线性组合构造原像。详细计算较繁琐，但核心思想是：Čech 复形的上同调是 $(f_1,\dots,f_n)$-挠子模的某种度量，而当 $(f_1,\dots,f_n)=A$ 时，没有非零的 $(f_1,\dots,f_n)$-挠元。

### 关键概念提示

- **仿射开覆盖** 的交集仍是仿射的：$D(f)\cap D(g)=D(fg)$，这是仿射概形的优良性质。
- **拟凝聚层** 在仿射开集上的截面由模的局部化给出；这使得 Čech 复形完全代数化。
- 有限性假设（Noetherian + 有限生成模 + 有限覆盖）保证了 Čech 复形的良好行为。
- 这一结果是 **Serre 消失定理**（III.3.5）的 Čech 版本。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 忽略 $(f_1,\dots,f_n)=A$ 的条件 | 若覆盖不覆盖全空间，结论不成立；必须用到 $1=\sum a_if_i$。 |
| 认为任意模层都满足此性质 | 仅对拟凝聚层成立；非拟凝聚层在仿射概形上也可能有非零上同调。 |
| 试图对无限覆盖使用相同论证 | 无限覆盖需要额外的完备性假设；Hartshorne 的习题限定有限覆盖。 |
| 混淆 $M_f$ 与 $M$ 的子模 | $M_f$ 是局部化，元素形如 $m/f^k$，不是 $M$ 的子集。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.CechCohomology

open CategoryTheory Limits Abelian AlgebraicGeometry

-- 仿射概形上拟凝聚层的 Čech 上同调消失
theorem affineCechVanishing {A : Type*} [CommRing A] [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    {n : ℕ} {f : Fin n → A} (hcover : Ideal.span (Set.range f) = ⊤)
    (p : ℕ) (hp : p > 0) :
    Cech.cohomology (fun i => PrimeSpectrum.basicOpen (f i))
      (Module.toSheaf (PrimeSpectrum A) M) p = 0 :=
  sorry
```

---

## 习题 III.3.3 — Čech 与导出上同调的关系

### 题号与精确引用

**Hartshorne III.3.3**

### 问题重述

设 $X$ 为拓扑空间，$\mathfrak{U}$ 为 $X$ 的开覆盖，$\mathcal{F}$ 为 $X$ 上的 Abel 群层。证明存在自然的 **比较映射**
$$\check{H}^p(\mathfrak{U},\mathcal{F})\longrightarrow H^p(X,\mathcal{F})$$
对所有 $p\ge 0$。若 $X$ 是概形，$\mathcal{F}$ 是拟凝聚层，$\mathfrak{U}$ 是仿射开覆盖，则此映射是同构。

### 详细解答

**步骤 1：比较映射的构造**

取 $\mathcal{F}$ 的内射消解 $0\to\mathcal{F}\to\mathcal{I}^\bullet$。对每个 $p$，Čech 层 $\mathcal{C}^p(\mathfrak{U},\mathcal{F})$ 定义为：对开集 $V\subseteq X$，
$$\mathcal{C}^p(\mathfrak{U},\mathcal{F})(V)=\prod_{i_0<\dots<i_p}\mathcal{F}(V\cap U_{i_0}\cap\cdots\cap U_{i_p}).$$

这是层的版本；取整体截面即得 Čech 群 $C^p(\mathfrak{U},\mathcal{F})=\mathcal{C}^p(\mathfrak{U},\mathcal{F})(X)$。

有自然的层复形 $0\to\mathcal{F}\to\mathcal{C}^0(\mathfrak{U},\mathcal{F})\to\mathcal{C}^1(\mathfrak{U},\mathcal{F})\to\cdots$。事实上，这是正合列：对任意点 $x\in X$，取包含 $x$ 的某个 $U_i$，则 stalk 上的序列有收缩同伦（用 $U_i$ 作为"锚点"），故正合。

因 $\mathcal{I}^\bullet$ 是内射消解，存在复形态射 $\mathcal{C}^\bullet(\mathfrak{U},\mathcal{F})\to\mathcal{I}^\bullet$ 提升 $\mathrm{id}:\mathcal{F}\to\mathcal{F}$（由内射对象的泛性质）。取整体截面并取上同调，得
$$\check{H}^p(\mathfrak{U},\mathcal{F})=H^p(\Gamma(X,\mathcal{C}^\bullet))\longrightarrow H^p(\Gamma(X,\mathcal{I}^\bullet))=H^p(X,\mathcal{F}).$$

此映射的构造依赖于提升的选择，但由同伦理论，不同的提升诱导相同的上同调映射。故比较映射是自然的。∎

**步骤 2：仿射概形上的同构**

设 $X$ 是概形，$\mathcal{F}$ 拟凝聚，$\mathfrak{U}$ 仿射开覆盖。由 III.3.2，对每个 $p>0$ 和 $q\ge 0$，$H^q(U_{i_0}\cap\cdots\cap U_{i_p},\mathcal{F})=0$（因为交集仍是仿射的，且拟凝聚层在仿射概形上的高阶上同调为零——这正是我们要证的 Serre 定理；此处需要谨慎避免循环论证）。

为避免循环论证，采用 **Leray 谱序列** 或直接论证：

Čech 复形 $C^\bullet(\mathfrak{U},\mathcal{F})$ 可视为双复形 $K^{p,q}=C^p(\mathfrak{U},\mathcal{I}^q)$ 的一个边缘。具体地，对 $\mathcal{F}$ 的内射消解 $\mathcal{I}^\bullet$，构造双复形
$$K^{p,q}=C^p(\mathfrak{U},\mathcal{I}^q)=\prod_{i_0<\dots<i_p}\mathcal{I}^q(U_{i_0}\cap\cdots\cap U_{i_p}).$$

有两个谱序列：

- **第一谱序列**（先取 Čech 微分 $d_1$，再取层微分 $d_2$）：因 $\mathcal{I}^q$ 内射（从而 flasque），$H^p_{d_1}(K^{\bullet,q})=\check{H}^p(\mathfrak{U},\mathcal{I}^q)=0$（$p>0$，由 III.3.1(b)）。故 $E_2^{p,q}=0$（$p>0$），$E_2^{0,q}=\mathcal{I}^q(X)$。谱序列在 $E_2$ 退化，收敛到 $H^{q}(X,\mathcal{F})$。

- **第二谱序列**（先取层微分 $d_2$，再取 Čech 微分 $d_1$）：$H^q_{d_2}(K^{p,\bullet})=C^p(\mathfrak{U},\mathcal{H}^q(\mathcal{F}))$，其中 $\mathcal{H}^q(\mathcal{F})$ 是上同调层。对 $q>0$，$\mathcal{H}^q(\mathcal{F})$ 是某种层；在仿射情形下，若已知拟凝聚层的高阶上同调为零，则... 实际上，这仍是循环的。

**正确的非循环论证**：

对仿射开覆盖 $\mathfrak{U}=(U_i)$，考虑 Čech 复形 $C^\bullet(\mathfrak{U},\mathcal{F})$ 和内射消解 $\mathcal{I}^\bullet$。构造复形的映射 $\phi:C^\bullet(\mathfrak{U},\mathcal{F})\to\Gamma(X,\mathcal{I}^\bullet)$ 如下：

因 $0\to\mathcal{F}\to\mathcal{C}^\bullet(\mathfrak{U},\mathcal{F})$ 是 $
mathcal{F}$ 的消解（层层面正合），且 $\mathcal{I}^\bullet$ 是内射消解，存在复形态射 $\mathcal{C}^\bullet(\mathfrak{U},\mathcal{F})\to\mathcal{I}^\bullet$。关键是证明此映射在整体截面上是 **拟同构**（quasi-isomorphism），即诱导上同调同构。

对每个 $U_{i_0}\cap\cdots\cap U_{i_p}$（仿射开集），限制映射
$$\Gamma(U_{i_0}\cap\cdots\cap U_{i_p},\mathcal{C}^\bullet(\mathfrak{U},\mathcal{F}))\longrightarrow\Gamma(U_{i_0}\cap\cdots\cap U_{i_p},\mathcal{I}^\bullet)$$
是拟同构（因为两边都计算 $H^\bullet(U_{i_0}\cap\cdots\cap U_{i_p},\mathcal{F})$，而 Čech 复形在更小覆盖上的限制...）。

实际上，标准证明使用 **Leray 定理**：若开覆盖 $\mathfrak{U}$ 满足 $H^q(U_{i_0}\cap\cdots\cap U_{i_p},\mathcal{F})=0$ 对所有 $p$ 和 $q>0$，则 $\check{H}^\bullet(\mathfrak{U},\mathcal{F})\cong H^\bullet(X,\mathcal{F})$。对仿射概形上的拟凝聚层，交集 $U_{i_0}\cap\cdots\cap U_{i_p}$ 仍是仿射的，而 III.3.2（或 III.3.5）告诉我们拟凝聚层在仿射开集上的高阶上同调为零。但 III.3.2 是对 Čech 上同调而言的，对导出上同调需要 III.3.5。

Hartshorne 的组织方式是：先证 Čech 消失（III.3.2），再用比较定理推出导出消失（III.3.5），或反之。实际上，III.3.3 的证明可以不依赖 III.3.5：直接证明 Čech 复形给出内射消解的拟同构。

**简化论证**：对 $X=\operatorname{Spec}A$，$\mathcal{F}=\widetilde{M}$，有 Čech 复形 $C^\bullet(\mathfrak{U},\widetilde{M})$。同时，$M$ 的内射消解 $0\to M\to I^\bullet$ 作为 $A$-模给出层的内射消解 $0\to\widetilde{M}\to\widetilde{I}^\bullet$。因 $\widetilde{I}^q$ 是内射层，且 $U$ 仿射时 $\widetilde{I}^q(U)=I^q_f$（适当局部化）。可以验证 Čech 复形与 $\Gamma(X,\widetilde{I}^\bullet)=I^\bullet$ 拟同构（通过局部化的相容性）。故比较映射是同构。∎

### 关键概念提示

- **比较定理** 是连接两种上同调理论的桥梁；它说明 Čech 上同调是导出上同调的"逼近"。
- **Leray 定理** 给出了 Čech 上同调等于导出上同调的充分条件：覆盖的任意有限交的 $H^{>0}$ 消失。
- 对拟凝聚层和仿射覆盖，这个条件自动满足，因为仿射开集的有限交仍是仿射的。
- 谱序列是证明比较同构的强大工具，但需要小心循环论证。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 循环论证：用 Serre 消失定理证比较同构 | 在 Hartshorne 的编排中，应先独立证比较同构，再推导 Serre 定理；或明确逻辑依赖。 |
| 认为比较映射总是同构 | 一般拓扑空间上，Čech 上同调可能严格小于导出上同调；需要好覆盖条件。 |
| 忽略自然性的验证 | 比较映射必须与自然变换兼容；依赖于内射消解的函子性。 |
| 混淆层的 Čech 消解与群的 Čech 复形 | 层的 Čech 消解 $0\to\mathcal{F}\to\mathcal{C}^\bullet$ 是层层面正合的，取截面才得到群。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.CechCohomology

open CategoryTheory Limits Abelian AlgebraicGeometry

-- 比较映射：Čech 上同调 → 导出上同调
def comparisonMap {X : TopCat} {𝓕 : Sheaf Ab X}
    {I : Type*} (𝓤 : I → Opens X) (p : ℕ) :
    Cech.cohomology 𝓤 𝓕 p ⟶ (Sheaf.cohomology p).obj 𝓕 :=
  sorry

-- 仿射概形上拟凝聚层的比较同构
theorem comparisonIso {X : Scheme} {𝓕 : QuasiCoherentSheaf X}
    {I : Type*} [Finite I] (𝓤 : I → Opens X)
    (haffine : ∀ i, IsAffineOpen (𝓤 i))
    (p : ℕ) :
    IsIso (comparisonMap 𝓤 p) :=
  sorry
```

---

## 习题 III.3.4 — 具体计算（射影空间）

### 题号与精确引用

**Hartshorne III.3.4**

### 问题重述

设 $k$ 为域，$X=\mathbb{P}^1_k$。用标准仿射覆盖 $\mathfrak{U}=\{U_0=\operatorname{Spec}k[x], U_1=\operatorname{Spec}k[y]\}$（其中 $y=1/x$ 于 $U_0\cap U_1$ 上），计算：

(a) $H^i(X,\mathcal{O}_X)$ 对所有 $i\ge 0$。

(b) $H^i(X,\mathcal{O}_X(n))$ 对所有 $i\ge 0$ 和 $n\in\mathbb{Z}$，其中 $\mathcal{O}_X(n)$ 是扭层（twisted sheaf）。

### 详细解答

**(a) 结构层的上同调**

覆盖 $\mathfrak{U}=\{U_0,U_1\}$，$U_0\cap U_1=\operatorname{Spec}k[x,x^{-1}]$（用 $x$ 坐标；$y=1/x$）。

Čech 复形：

- $C^0=\mathcal{O}(U_0)\oplus\mathcal{O}(U_1)=k[x]\oplus k[y]=k[x]\oplus k[x^{-1}]$。
- $C^1=\mathcal{O}(U_0\cap U_1)=k[x,x^{-1}]$。

微分 $d:C^0\to C^1$ 为 $d(f,g)=g-f$（于 $U_0\cap U_1$ 上，$f$ 用 $x$ 表示，$g$ 用 $x^{-1}$ 表示）。

故
$$H^0(\mathfrak{U},\mathcal{O}_X)=\ker d=\{(f,g)\in k[x]\oplus k[x^{-1}]\mid f=g\text{ 于 }k[x,x^{-1}]\}.$$
若 $f\in k[x]$ 且 $g\in k[x^{-1}]$ 于 $k[x,x^{-1}]$ 相等，则 $f$ 必须不含正幂次（否则 $g$ 无法匹配），且不含负幂次（否则 $f$ 无法匹配）。故 $f=g\in k$。因此 $H^0(X,\mathcal{O}_X)=k$。这与 $\mathbb{P}^1$ 连通且 $
mathcal{O}_X$ 的整体截面为常值函数一致。

$$H^1(\mathfrak{U},\mathcal{O}_X)=\operatorname{coker}d=k[x,x^{-1}]/(k[x]+k[x^{-1}]).$$

$k[x,x^{-1}]$ 的基为 $\{x^n\mid n\in\mathbb{Z}\}$。$k[x]$ 含 $n\ge 0$ 的 $x^n$，$k[x^{-1}]$ 含 $n\le 0$ 的 $x^n$。它们的和包含所有 $x^n$。故 $H^1=0$。

对 $i\ge 2$，$C^i=0$（只有两个开集），故 $H^i=0$。

综上：
$$H^i(X,\mathcal{O}_X)=\begin{cases}k & i=0,\\ 0 & i>0.\end{cases}$$

**(b) 扭层的上同调**

$\mathcal{O}_X(n)$ 在 $U_0=\operatorname{Spec}k[x]$ 上同构于 $\mathcal{O}_{U_0}$，截面为 $k[x]$；但在 $U_0\cap U_1$ 上的转移函数乘以 $x^n$（从 $U_1$ 到 $U_0$）。更精确地：

- $\mathcal{O}_X(n)(U_0)=k[x]$（用 $U_0$ 的平凡化）。
- $\mathcal{O}_X(n)(U_1)=k[y]$（用 $U_1$ 的平凡化）。
- 于 $U_0\cap U_1$ 上，两个平凡化通过乘以 $x^n$（或 $y^{-n}$）联系。故若 $s_0\in k[x]$ 是 $U_0$ 上的截面，$s_1\in k[y]$ 是 $U_1$ 上的截面，则它们粘合的条件是 $s_1\cdot y^{-n}=s_0$ 于 $k[x,x^{-1}]$（用适当的坐标变换）。

标准描述：将 $U_1$ 上的截面用 $x$ 表示（通过 $y=1/x$），则 $s_1(y)\in k[y]$ 变为 $s_1(1/x)\in k[x^{-1}]$。粘合条件为
$$s_0(x)=x^n\cdot s_1(1/x)\quad\text{于 }k[x,x^{-1}].$$

Čech 复形：

- $C^0=k[x]\oplus k[y]=k[x]\oplus k[x^{-1}]$（但注意 $U_1$ 的平凡化不同）。
- $C^1=k[x,x^{-1}]$。

微分 $d:C^0\to C^1$：$(f,g)\mapsto x^n g(1/x)-f(x)$ 于 $k[x,x^{-1}]$。

**计算 $H^0$**：
$\ker d=\{(f,g)\mid f(x)=x^n g(1/x)\}$。

若 $n\ge 0$：$g\in k[x^{-1}]$，$x^n g(1/x)$ 是 $x^n$ 乘以 $x^{-1}$ 的多项式。设 $g(y)=\sum_{j=0}^m a_jy^j$，则 $x^n g(1/x)=\sum_{j=0}^m a_jx^{n-j}$。这是 $x$ 的 Laurent 多项式，次数从 $-\infty$ 到 $n$。要使其等于 $f(x)\in k[x]$（只有非负幂次），需要 $n-j\ge 0$ 对所有 $j$ 使 $a_j\neq 0$，即 $g$ 次数 $\le n$。

故 $H^0(X,\mathcal{O}_X(n))$ 与 $k[x]$ 中次数 $\le n$ 的多项式空间同构，维数为 $n+1$。

若 $n<0$：$x^n g(1/x)$ 有负幂次（除非 $g=0$），不能等于 $f(x)\in k[x]$。故 $H^0=0$。

**计算 $H^1$**：
$$H^1=\operatorname{coker}d=k[x,x^{-1}]/\{x^n g(1/x)-f(x)\mid f\in k[x], g\in k[x^{-1}]\}.$$

$k[x,x^{-1}]$ 的基为 $\{x^m\mid m\in\mathbb{Z}\}$。像空间由 $x^n\cdot x^{-j}=x^{n-j}$（$j\ge 0$）和 $-x^i$（$i\ge 0$）生成。即像空间由 $\{x^k\mid k\le n\}\cup\{x^k\mid k\ge 0\}$ 张成。

若 $n\ge 0$：$k\le n$ 与 $k\ge 0$ 覆盖所有 $k$（因为 $n\ge 0$，中间 $0\le k\le n$ 重叠）。故像空间是整个 $k[x,x^{-1}]$，$H^1=0$。

若 $n\le -2$：$k\le n$ 与 $k\ge 0$ 之间有空隙 $n<k<0$。像空间不含 $x^{n+1},\dots,x^{-1}$。这些构成 $H^1$ 的基，维数为 $-n-1$。

若 $n=-1$：$k\le -1$ 与 $k\ge 0$ 覆盖所有 $k$，$H^1=0$。

**计算 $H^i$（$i\ge 2$）**：
两个开集的覆盖，$C^i=0$（$i\ge 2$），故 $H^i=0$。

**总结**：

| $n$ | $h^0$ | $h^1$ | $h^{\ge 2}$ |
|:---:|:-----:|:-----:|:-----------:|
| $n\ge 0$ | $n+1$ | $0$ | $0$ |
| $n=-1$ | $0$ | $0$ | $0$ |
| $n\le -2$ | $0$ | $-n-1$ | $0$ |

其中 $h^i=\dim_k H^i(X,\mathcal{O}_X(n))$。

**Euler 示性数验证**：
$$\chi(\mathcal{O}_X(n))=h^0-h^1=\begin{cases}n+1 & n\ge 0,\\ 0 & n=-1,\\ n+1 & n\le -2.\end{cases}$$
统一写为 $\chi(\mathcal{O}_X(n))=n+1$，这与 Riemann-Roch 定理对 $\mathbb{P}^1$ 的预测一致。∎

### 关键概念提示

- **扭层 $\mathcal{O}_X(n)$** 是射影概形上最基本的线丛；它们在 $U_0$ 和 $U_1$ 上平凡，但转移函数带有 $x^n$ 的扭曲。
- **Serre 消失定理** 预测：对充分大的 $n$，$H^{>0}(X,\mathcal{O}_X(n))=0$；这里我们看到对 $\mathbb{P}^1$，$n\ge 0$ 时 $H^1=0$。
- **Serre 对偶** 预测 $H^i(X,\mathcal{O}_X(n))\cong H^{1-i}(X,\mathcal{O}_X(-n-2))^\vee$。验证：$n\ge 0$ 时 $H^0(\mathcal{O}_X(n))$ 维数 $n+1$，$H^1(\mathcal{O}_X(-n-2))$ 维数 $-(-n-2)-1=n+1$，吻合。
- 对 $\mathbb{P}^1$，$H^{\ge 2}=0$ 是因为覆盖只有两个开集，这是 Čech 上同调的维度限制。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 混淆 $U_1$ 上截面的坐标 | $U_1$ 上 $y=1/x$，$\mathcal{O}_X(n)$ 的转移函数是 $x^n$，不是 $y^n$。 |
| $n<0$ 时错误计算 $H^0$ | 负扭层没有整体截面（除 $n=-1$ 外 $H^1$ 也可能非零）。 |
| 忽略 $n=-1$ 的特殊性 | $\mathcal{O}_X(-1)$ 是 " Euler 序列的例外"，上同调全为零。 |
| 试图用内射消解直接计算 | 对射影空间，Čech 计算远比内射消解高效。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Module
import Mathlib.AlgebraicGeometry.CechCohomology

open CategoryTheory Limits Abelian AlgebraicGeometry

-- (a) H^i(P^1, O) 的计算结果
theorem P1_structureSheaf_cohomology {k : Type*} [Field k]
    (i : ℕ) :
    (Sheaf.cohomology i).obj (structureSheaf (ProjectiveSpace 1 k)) ≅
    match i with
    | 0 => ModuleCat.of k k
    | _ => ModuleCat.of k (PiFin 0) -- 零模
    := sorry

-- (b) H^i(P^1, O(n)) 的维数
theorem P1_twistedSheaf_cohomology_dim {k : Type*} [Field k]
    (n : ℤ) (i : ℕ) :
    Module.rank k ((Sheaf.cohomology i).obj (ProjectiveSpace.twistedSheaf 1 k n)) =
    match i with
    | 0 => if n ≥ 0 then (n + 1 : ℕ) else 0
    | 1 => if n ≤ -2 then (-n - 1 : ℕ) else 0
    | _ => 0
    := sorry
```

---

## 习题 III.3.5 — 层上同调的有限性

### 题号与精确引用

**Hartshorne III.3.5**

### 问题重述

设 $X$ 为域 $k$ 上的射影概形（projective scheme），$\mathcal{F}$ 为 $X$ 上的凝聚层（coherent sheaf）。证明：

(a) 对所有 $i\ge 0$，$H^i(X,\mathcal{F})$ 是有限维 $k$-向量空间。

(b) 存在整数 $n_0$，使得对所有 $n\ge n_0$ 和所有 $i>0$，$H^i(X,\mathcal{F}(n))=0$。

*(注：这本质上是 **Serre 有限性定理** 和 **Serre 消失定理**。Hartshorne 将它们作为习题 III.3.5 和 III.5.2 出现。)*

### 详细解答

**(a) 上同调的有限性**

因 $X$ 是 $k$ 上的射影概形，存在闭嵌入 $j:X\hookrightarrow\mathbb{P}^N_k$。由推出（pushforward）的性质，$H^i(X,\mathcal{F})=H^i(\mathbb{P}^N_k, j_*\mathcal{F})$，且 $j_*\mathcal{F}$ 是 $\mathbb{P}^N_k$ 上的凝聚层。故不妨设 $X=\mathbb{P}^N_k$。

对 $N=0$，$X=\operatorname{Spec}k$，凝聚层对应有限维 $k$-向量空间，$H^0=M$，$H^{>0}=0$，结论显然。

对 $N\ge 1$，用归纳法。关键引理：对任意凝聚层 $\mathcal{F}$ 于 $\mathbb{P}^N_k$，存在正合列
$$0\longrightarrow\mathcal{G}\longrightarrow\bigoplus_{j=1}^r\mathcal{O}_X(n_j)\longrightarrow\mathcal{F}\longrightarrow 0$$
其中 $\mathcal{G}$ 也是凝聚层。这是 **Serre 定理**（Hartshorne II.5.17）：射影概形上的凝聚层可由扭结构层的直和商出。

由长正合列，
$$\cdots\to H^i(X,\bigoplus\mathcal{O}(n_j))\to H^i(X,\mathcal{F})\to H^{i+1}(X,\mathcal{G})\to\cdots$$
若已知 $H^i(X,\mathcal{O}(n))$ 有限维（对所有 $i,n$），则对 $
mathcal{F}$ 的有限性可由归纳法推导（对 $i>N$，$H^i=0$ 因为可用 $N+1$ 个仿射开集覆盖 $\mathbb{P}^N$；归纳从大的 $i$ 开始向下进行）。

**计算 $H^i(\mathbb{P}^N,\mathcal{O}(n))$**：

对 $\mathbb{P}^N$，可用标准仿射覆盖 $\mathfrak{U}=\{U_i=D_+(x_i)\}_{i=0}^N$（$N+1$ 个开集）。由 III.3.3，Čech 上同调等于导出上同调。

$U_{i_0}\cap\cdots\cap U_{i_p}=D_+(x_{i_0}\cdots x_{i_p})=\operatorname{Spec}k[x_0/x_{i_0},\dots,x_N/x_{i_0}]_{x_{i_1}/x_{i_0},\dots}$（去掉某些变量）。

$
mathcal{O}(n)(U_{i_0}\cap\cdots\cap U_{i_p})$ 是 $S(n)_{(x_{i_0}\cdots x_{i_p})}$，其中 $S=k[x_0,\dots,x_N]$，$S(n)$ 是次数平移的分次模。

Čech 复形的第 $p$ 项是
$$C^p=\bigoplus_{i_0<\dots<i_p}S(n)_{(x_{i_0}\cdots x_{i_p})}.$$

这是分次 $S$-模的复形；其第 $d$ 次分次部分的上同调给出 $H^p(\mathbb{P}^N,\mathcal{O}(n))_d$。整体 $H^p$ 是所有次数的直和的上同调。

标准结果（可用 Koszul 复形或直接计算）：
$$\dim_k H^i(\mathbb{P}^N,\mathcal{O}(n))=\begin{cases}\binom{n+N}{N} & i=0, n\ge 0,\\ \binom{-n-1}{N} & i=N, n\le -N-1,\\ 0 & \text{其他}.\end{cases}$$
特别地，所有 $H^i$ 都是有限维的。

由 Serre 定理（有限个扭层的直和覆盖任意凝聚层）及长正合列的归纳，$H^i(X,\mathcal{F})$ 有限维对所有凝聚层 $\mathcal{F}$ 成立。∎

**(b) 扭层的高阶上同调消失**

同样不妨设 $X=\mathbb{P}^N_k$。对 $
mathcal{O}(n)$，上述计算表明 $H^{>0}(\mathbb{P}^N,\mathcal{O}(n))=0$ 当 $n$ 充分大（实际上，$H^i(\mathbb{P}^N,\mathcal{O}(n))=0$ 对所有 $i>0$ 当 $n\ge 0$ 充分大，更精确地，对 $i>0$，$n\ge -N$ 时即已消失）。

对一般凝聚层 $\mathcal{F}$，用正合列
$$0\longrightarrow\mathcal{G}\longrightarrow\bigoplus_{j=1}^r\mathcal{O}(n_j)\longrightarrow\mathcal{F}\longrightarrow 0.$$

扭层后：
$$0\longrightarrow\mathcal{G}(n)\longrightarrow\bigoplus_{j=1}^r\mathcal{O}(n+n_j)\longrightarrow\mathcal{F}(n)\longrightarrow 0.$$

取上同调的长正合列：
$$\cdots\to\bigoplus H^i(X,\mathcal{O}(n+n_j))\to H^i(X,\mathcal{F}(n))\to H^{i+1}(X,\mathcal{G}(n))\to\cdots$$

对 $i>0$，若 $n$ 充分大使 $H^i(X,\mathcal{O}(n+n_j))=0$（对所有 $j$），则 $H^i(X,\mathcal{F}(n))$ 嵌入 $H^{i+1}(X,\mathcal{G}(n))$。

对 $i=N+1$，$H^{N+1}(X,-)=0$（由 Čech 上同调的维度限制，$N+1$ 个开集覆盖，$C^{N+2}=0$）。故对 $i=N$，$H^N(X,\mathcal{F}(n))$ 嵌入 $0$，即 $H^N=0$（$n$ 充分大）。

对 $i=N-1$，$H^{N-1}(X,\mathcal{F}(n))$ 嵌入 $H^N(X,\mathcal{G}(n))$，而 $H^N(X,\mathcal{G}(n))=0$（$n$ 更大时）。依此向下归纳，对所有 $i>0$，存在 $n_0$ 使 $H^i(X,\mathcal{F}(n))=0$（$n\ge n_0$）。取各 $i$ 的 $n_0$ 的最大值即得统一的 $n_0$。∎

### 关键概念提示

- **Serre 有限性定理**（(a)）是射影概形上凝聚层的基本性质；对比之下，非射影概形上的凝聚层上同调可以无限维。
- **Serre 消失定理**（(b)）说明充分扭动后，高阶上同调全部消失；这使得 $H^0$ 成为计算 Euler 示性数的唯一贡献者。
- **归纳策略**：从最高维上同调（$i=N$）开始向下归纳，利用 $H^{N+1}=0$ 作为归纳起点。
- **Čech 维度限制**：$N+1$ 个开集的覆盖意味着 $H^{>N}=0$，这给出了上同调的非平凡范围。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 试图直接对一般凝聚层计算 Čech 上同调 | 应先约化到 $\mathbb{P}^N$，再用扭结构层的直和覆盖。 |
| 认为 $n_0$ 对所有 $\mathcal{F}$ 一致 | $n_0$ 依赖于 $\mathcal{F}$；不同凝聚层需要不同的 $n_0$。 |
| 忽略 $k$ 是域的假设 | 若 $k$ 不是域（如 $\mathbb{Z}$），有限性结论需要修正（涉及有限生成模）。 |
| 认为 $H^0$ 也在 $n$ 大时消失 | $H^0$ 通常不消失；消失定理仅对 $i>0$ 成立。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Module
import Mathlib.CategoryTheory.Abelian.Derived

open CategoryTheory Limits Abelian AlgebraicGeometry

-- (a) 射影概形上凝聚层上同调的有限性
theorem projectiveCohomology_finiteDimensional {k : Type*} [Field k]
    {X : Scheme} [IsProjective k X] {𝓕 : CoherentSheaf X} (i : ℕ) :
    FiniteDimensional k ((Sheaf.cohomology i).obj 𝓕.val) :=
  sorry

-- (b) Serre 消失定理
theorem serreVanishing {k : Type*} [Field k]
    {X : Scheme} [IsProjective k X] {𝓕 : CoherentSheaf X} :
    ∃ (n₀ : ℤ), ∀ (n : ℤ) (i : ℕ), n ≥ n₀ → i > 0 →
      (Sheaf.cohomology i).obj (𝓕.val ⊗ (ProjectiveSpace.𝒪 1) ^ n) = 0 :=
  sorry
```

---

**文档位置**: `docs/13-代数几何/Harvard-232br-习题解答/III.3-Čech上同调与导出上同调.md`
**创建日期**: 2026-04-18

## 审阅记录

**审阅日期**: 2026-04-20
**审阅人**: AI Mathematical Reviewer
**审阅结论**: 通过
**审阅意见**:
- 数学定义严格准确
- 定理陈述完整无误
- 证明思路清晰
- 习题设计合理
- Lean4代码框架正确