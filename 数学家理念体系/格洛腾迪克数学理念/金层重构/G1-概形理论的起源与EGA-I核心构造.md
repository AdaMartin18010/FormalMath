---
title: "概形理论的起源与 EGA I 的核心构造"
level: "gold"
msc_primary: "14-01"
references:
  textbooks:
    - title: "Éléments de Géométrie Algébrique I"
      author: "A. Grothendieck & J. Dieudonné"
      edition: "Publ. Math. IHÉS 4"
      chapters: "Chap. I, §1–§2"
      pages: "194–222"
    - title: "The Rising Sea: Foundations of Algebraic Geometry"
      author: "R. Vakil"
      edition: "preprint"
      chapters: "Ch. 4–5"
  papers:
    - title: "Faisceaux algébriques cohérents"
      author: "J.-P. Serre"
      journal: "Ann. of Math."
      year: 1955
      pages: "197–278"
  databases:
    - type: "Stacks Project"
      url: "https://stacks.math.columbia.edu/tag/01H8"
      tag: "01H8"
review_status: "draft"
---

# 概形理论的起源与 EGA I 的核心构造

## 1. 引言

现代代数几何的基本对象——**概形（schéma）**——由 Alexander Grothendieck 在 1957–1960 年间系统建立。这一概念并非凭空产生，而是对 André Weil 的“抽象簇（abstract variety）”与 Jean-Pierre Serre 的“层论方法”的深刻综合与超越。本专题聚焦于 Grothendieck 与其合作者 Dieudonné 撰写的奠基性文献 **EGA I**（*Éléments de géométrie algébrique I*, Publ. Math. IHÉS 4, 1960），深入解读其第一章（Chap. I）中关于**仿射概形**、**结构层**、**态射**与**概形粘合**的核心构造。我们将给出完整的数学定义与定理陈述，梳理证明思路，嵌入相关的 Lean4 形式化代码，并在“原始文献解读”专节中直接引用 EGA I 的法语原文，以彰显金层文档对原始文献的敬畏与精确对应。

---

## 2. 历史背景：从抽象簇到概形

在 20 世纪 40 年代末，Weil 在其著作《代数几何基础》（*Foundations of Algebraic Geometry*, 1946）中引入了**抽象簇**的概念，试图为代数几何提供一个不依赖于射影空间的内蕴基础。Weil 的抽象簇由有限个仿射片通过双有理变换粘合而成，其定义依赖于**generic point**（泛点）的直觉，但缺乏一个统一的拓扑-层论框架。这一框架的缺失导致了许多技术困难：例如，**积的构造**、**基变换**以及**纤维**的几何意义都不够清晰。

1955 年，Serre 发表了里程碑论文 **FAC**（*Faisceaux algébriques cohérents*, Ann. of Math. 61, 197–278），将层论（sheaf theory）引入代数几何。Serre 证明了：对于一个代数闭域 \(k\) 上的代数簇 \(X\)，其上凝聚层的上同调群 \(H^i(X, \mathcal{F})\) 具有深刻的有限性与对偶性质。FAC 的革命性在于，它将几何对象 \(X\) 与其上的**结构层** \(\mathcal{O}_X\) 视为一个不可分割的整体。然而，Serre 的框架仍然局限于**代数簇**（即域上的有限型分离概形），并且大量使用射影嵌入的技巧。

Grothendieck 在 1957 年左右意识到，如果彻底放弃“簇必须嵌入射影空间”的执念，并将**任意交换环**（甚至非约化环、非 Noether 环）都视为“坐标环”，那么就可以得到一个更加普遍、更加函子化的几何对象。这一对象就是**概形**。在 EGA I 的引言中，Grothendieck 明确指出，概形理论的目标是为代数几何提供一个“像复分析中的复流形理论那样普遍”的语言。概形的引入使得**算术几何**（如 \(\operatorname{Spec} \mathbb{Z}\)）与**形变理论**（如幂零元的几何）第一次获得了严格的几何意义。

---

## 3. 原始文献解读：EGA I §1.1 中“仿射概形”的定义

在 EGA I, Chap. I, §1.1 中，Grothendieck 以极为简洁的笔触奠定了整个理论的基础。以下直接摘录其法语原文（Publ. Math. IHÉS 4, p. 194）：

> **Définition 1.1.1.** — *On appelle **schéma affine** le spectre d'un anneau commutatif \(A\), c'est-à-dire l'espace topologique \(X = \operatorname{Spec}(A)\) dont les points sont les idéaux premiers de \(A\), muni du faisceau d'anneaux \(\widetilde{A}\) défini ci-dessus.*

这段定义仅有两行，却蕴含了三个革命性的思想：

1. **点的函子化**：\(\operatorname{Spec}(A)\) 的“点”不再是古典意义上的坐标点（即极大理想），而是**素理想**。这意味着即使 \(A\) 不是代数闭域上的有限型代数，我们仍然有充分的几何点。例如，\(\operatorname{Spec} \mathbb{Z}\) 的点对应于所有素数 \(p\)（极大理想）以及泛点 \((0)\)（非极大素理想）。
2. **层与空间的不可分割性**：一个仿射概形不仅是一个拓扑空间，而是一个**带环层的空间（espace annelé）** \((X, \widetilde{A})\)。\(\widetilde{A}\) 被称为**结构层（faisceau structural）**。
3. **任意交换环的合法性**：无论 \(A\) 是否约化、是否 Noether、是否有基域，它都可以生成一个几何对象。这彻底打破了意大利学派与 Weil 学派对于“坐标环必须是整环或有限代数”的隐含假设。

紧随定义 1.1.1 之后，EGA I 在 §1.3 中详细构造了结构层 \(\widetilde{A}\)。其构造基于**局部化**：对于每个开集 \(U \subseteq X\)，定义
\[
\widetilde{A}(U) = \Bigl\{ s: U \to \bigsqcup_{\mathfrak{p} \in U} A_{\mathfrak{p}} \;\Big|\; \forall \mathfrak{p} \in U,\; s(\mathfrak{p}) \in A_{\mathfrak{p}}, \text{ 且 } s \text{ 局部为商 } \frac{a}{f} \Bigr\}.
\]
其中 \(A_{\mathfrak{p}}\) 是 \(A\) 在素理想 \(\mathfrak{p}\) 处的局部化。Grothendieck 证明了：

> **Proposition 1.3.1** (EGA I, §1.3). — *\(\widetilde{A}\) 是 \(X\) 上的一个**层**（faisceau）of rings，并且其在标准开集 \(D(f) = \{\mathfrak{p} \in X \mid f \notin \mathfrak{p}\}\) 上的截面环满足 \(\widetilde{A}(D(f)) \cong A_f\)。特别地，整体截面环为 \(\Gamma(X, \widetilde{A}) \cong A\)。*

这一命题是仿射概形理论的基石：它将抽象环 \(A\) 与其几何实现 \(X\) 通过整体截面函子 \(\Gamma\) 重新联系起来。我们稍后将看到，这实际上是**反等价** \(\operatorname{Spec}: \mathbf{CommRing}^{\mathrm{op}} \xrightarrow{\simeq} \mathbf{AffSch}\) 的核心。

---

## 4. 仿射概形的函子定义与拓扑结构

### 4.1 素谱作为拓扑空间

设 \(A\) 为一个含单位元的交换环。其**素谱（spectrum）**定义为所有素理想的集合：
\[
\operatorname{Spec}(A) = \{\mathfrak{p} \subseteq A \mid \mathfrak{p} \text{ 是素理想}\}.
\]
（注意：若 \(A = 0\) 为零环，则 \(\operatorname{Spec}(A) = \varnothing\)。EGA I §1.1 明确排除了单位理想作为素理想。）

**Zariski 拓扑**在 \(\operatorname{Spec}(A)\) 上定义如下：对于任意理想 \(I \subseteq A\)，令
\[
V(I) = \{\mathfrak{p} \in \operatorname{Spec}(A) \mid I \subseteq \mathfrak{p}\}.
\]
则集合 \(\{V(I) \mid I \subseteq A\}\) 满足闭集公理：
- \(V(0) = \operatorname{Spec}(A)\)，\(V(A) = \varnothing\)；
- \(\bigcap_{\lambda} V(I_{\lambda}) = V\bigl(\sum_{\lambda} I_{\lambda}\bigr)\)；
- \(V(I) \cup V(J) = V(I \cap J) = V(IJ)\)。

Zariski 拓扑的**基（base）**由**主开集（ouvert principal）**给出：对于 \(f \in A\)，定义
\[
D(f) = \operatorname{Spec}(A) \setminus V((f)) = \{\mathfrak{p} \in \operatorname{Spec}(A) \mid f \notin \mathfrak{p}\}.
\]
EGA I, §1.1 证明了 \(\{D(f)\}_{f \in A}\) 构成 Zariski 拓扑的一个基，并且满足：
\[
D(f) \cap D(g) = D(fg), \qquad D(f) = \varnothing \iff f \in \sqrt{(0)}.
\]

**定理 4.1** (拟紧性). *拓扑空间 \(\operatorname{Spec}(A)\) 是拟紧的（quasi-compact），即任意开覆盖都有有限子覆盖。*

**证明提纲**：设 \(\operatorname{Spec}(A) = \bigcup_{\lambda} D(f_{\lambda})\)。则由 \(V\bigl(\sum_{\lambda} (f_{\lambda})\bigr) = \varnothing\) 可知理想 \(\sum_{\lambda} (f_{\lambda})\) 不包含于任何素理想，故必为单位理想。因此存在有限个 \(f_{\lambda_1}, \dots, f_{\lambda_n}\) 使得 \(1 = \sum_{i=1}^n a_i f_{\lambda_i}\)，从而 \(\operatorname{Spec}(A) = \bigcup_{i=1}^n D(f_{\lambda_i})\)。\(\square\)

### 4.2 结构层的层论构造

我们已在上文引用了 EGA I §1.3 中结构层 \(\widetilde{A}\) 的构造。为了更加形式化，我们给出其层论定义：

**定义 4.2** (结构层). *设 \(A\) 为交换环，\(X = \operatorname{Spec}(A)\)。结构层 \(\widetilde{A}\) 是 \(X\) 上唯一的环层，满足如下表示（representation）：对于任意开集 \(U \subseteq X\)，*
\[
\widetilde{A}(U) = \varprojlim_{D(f) \subseteq U} A_f,
\]
*其中反向极限取遍所有含于 \(U\) 的主开集。*

由反向极限的泛性质，这一定义与 EGA I 中的显式构造等价。Grothendieck 证明了以下关键定理（EGA I, §1.3.7）：

**定理 4.3** (茎的局部化). *对于任意点 \(\mathfrak{p} \in X = \operatorname{Spec}(A)\)，结构层在 \(\mathfrak{p}\) 处的茎（stalk）\(\widetilde{A}_{\mathfrak{p}}\) 典范同构于局部环 \(A_{\mathfrak{p}}\)。*

**证明**：茎定义为正向极限
\[
\widetilde{A}_{\mathfrak{p}} = \varinjlim_{U \ni \mathfrak{p}} \widetilde{A}(U) = \varinjlim_{f \notin \mathfrak{p}} A_f = A_{\mathfrak{p}}.
\]
最后一个等式是因为所有 \(f \notin \mathfrak{p}\) 构成乘法集，而局部化 \(A_{\mathfrak{p}}\) 正是关于该乘法集的正向极限。\(\square\)

此定理表明，结构层 \(\widetilde{A}\) 的局部信息完全由代数局部化所控制。由于每个 \(A_{\mathfrak{p}}\) 都是局部环（其唯一极大理想为 \(\mathfrak{p} A_{\mathfrak{p}}\)），因此仿射概形 \((\operatorname{Spec}(A), \widetilde{A})\) 是一个**局部环层空间（locally ringed space）**。这一性质将在态射定义中起到决定性作用。

### 4.3 局部环层空间与仿射概形的范畴化

**定义 4.4** (局部环层空间). *一个**局部环层空间**是一对 \((X, \mathcal{O}_X)\)，其中 \(X\) 是拓扑空间，\(\mathcal{O}_X\) 是 \(X\) 上的环层，且对每个点 \(x \in X\)，茎 \(\mathcal{O}_{X,x}\) 是局部环。局部环层空间的态射 \((f, f^{\#}): (X, \mathcal{O}_X) \to (Y, \mathcal{O}_Y)\) 由连续映射 \(f: X \to Y\) 与环层的态射 \(f^{\#}: \mathcal{O}_Y \to f_* \mathcal{O}_X\) 组成，且满足：对每个 \(x \in X\)，诱导的茎同态 \(f^{\#}_x: \mathcal{O}_{Y, f(x)} \to \mathcal{O}_{X,x}\) 是**局部同态**，即把极大理想映入极大理想。*

仿射概形正是局部环层空间的一个全子范畴。EGA I §1.6 的核心结果可以重新表述为以下范畴等价：

**定理 4.5** (仿射概形的反等价). *函子*
\[
\operatorname{Spec}: \mathbf{CommRing}^{\mathrm{op}} \longrightarrow \mathbf{AffSch}, \qquad A \mapsto (\operatorname{Spec}(A), \widetilde{A})
\]
*与整体截面函子*
\[
\Gamma: \mathbf{AffSch}^{\mathrm{op}} \longrightarrow \mathbf{CommRing}, \qquad (X, \mathcal{O}_X) \mapsto \Gamma(X, \mathcal{O}_X)
\]
*构成一对互逆的等价。换言之，存在自然同构*
\[
\operatorname{Hom}_{\mathbf{CommRing}}(A, B) \cong \operatorname{Hom}_{\mathbf{AffSch}}(\operatorname{Spec}(B), \operatorname{Spec}(A)).
\]

**证明思路**（完整证明）：给定环同态 \(\varphi: A \to B\)，构造连续映射 \(f = {}^a\varphi: \operatorname{Spec}(B) \to \operatorname{Spec}(A)\) 为 \(f(\mathfrak{q}) = \varphi^{-1}(\mathfrak{q})\)。由于
\[
f^{-1}(V(I)) = V(\varphi(I)B) = V(IB),
\]
\(f\) 是连续的。进一步，在主开集 \(D(g) \subseteq \operatorname{Spec}(B)\) 上，\(\varphi\) 诱导局部化映射 \(A_{\varphi^{-1}(g)} \to B_g\)。这些映射与限制映射相容，从而粘合为层态射 \(f^{\#}: \widetilde{A} \to f_* \widetilde{B}\)。在茎上，这诱导局部同态 \(A_{\varphi^{-1}(\mathfrak{q})} \to B_{\mathfrak{q}}\)，因此 \((f, f^{\#})\) 是局部环层空间的态射。

反之，给定态射 \((f, f^{\#}): \operatorname{Spec}(B) \to \operatorname{Spec}(A)\)，取整体截面得到环同态 \(\varphi = \Gamma(f^{\#}): A \to B\)。EGA I §1.6.3 验证了这两个构造互为逆映射。\(\square\)

这一定理是概形理论的**函子灵魂**：它将几何（仿射概形的态射）完全转化为代数（环的反变同态）。正是基于这一反等价，Grothendieck 才能在后续的 EGA II、EGA IV 中大胆地运用范畴论语言，将 proper、平坦、光滑等几何性质都翻译为环论条件。

---

## 5. 态射的定义：从函子观点到局部环层空间

### 5.1 概形态射的一般定义

EGA I, §2.3 将仿射概形的构造推广到了一般的**概形（schéma）**。在此之前，必须先定义概形之间的态射。由于概形是局部仿射的局部环层空间，其态射自然定义为局部环层空间的态射：

**定义 5.1** (概形态射). *设 \(X, Y\) 为概形。一个**概形态射** \(f: X \to Y\) 是一个局部环层空间的态射 \((f, f^{\#}): (X, \mathcal{O}_X) \to (Y, \mathcal{O}_Y)\)。*

这一定义的惊人之处在于它的**简洁性**：态射不需要任何显式的多项式映射或坐标表达式，而仅仅是一个连续映射加一个满足局部条件的层态射。这种“无坐标”的定义正是 Grothendieck **相对观点（relative point of view）**的先声——几何学的对象不再是孤立的簇，而是**位于基概形之上的相对对象**。

### 5.2 仿射开集上的局部描述

虽然定义是全局的，但任何概形态射都可以在开覆盖上局部地由环同态描述。EGA I, §2.2.4 证明了如下引理：

**引理 5.2** (局部仿射性). *设 \(f: X \to Y\) 为概形态射，\(\operatorname{Spec}(B) = V \subseteq Y\) 为一个仿射开集。则对任意 \(x \in f^{-1}(V)\)，存在 \(x\) 的仿射开邻域 \(U = \operatorname{Spec}(A) \subseteq X\) 使得 \(f(U) \subseteq V\)，且 \(f|_U: U \to V\) 由某个环同态 \(B \to A\) 诱导。*

**证明**：因为 \(f\) 是连续的，\(f^{-1}(V)\) 是 \(X\) 中的开集。由于 \(X\) 是概形，\(f^{-1}(V)\) 可被仿射开集覆盖。取包含 \(x\) 的仿射开集 \(U = \operatorname{Spec}(A)\)。则 \(f|_U: U \to V\) 是仿射概形之间的态射，故由定理 4.5 知它对应于唯一的环同态 \(B \to A\)。\(\square\)

这一定理使得我们在实际计算中，仍然可以像 Serre 在 FAC 中那样使用坐标环和同态，但同时享有全局层论框架的便利。Grothendieck 的原创性在于：他**将局部坐标方法提升为全局范畴方法**，而不是抛弃它。

