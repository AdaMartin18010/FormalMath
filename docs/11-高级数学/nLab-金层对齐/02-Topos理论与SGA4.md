---
title: "Topos 理论与 SGA 4"
level: "gold"
msc_primary: 18

  - 18B25
  - 18F10
  - 03G30
target_courses:
  - "nLab: topos"
  - "nLab: sheaf topos"
nlab_urls:
  - "https://ncatlab.org/nlab/show/topos"
  - "https://ncatlab.org/nlab/show/sheaf+topos"
  - "https://ncatlab.org/nlab/show/geometric+morphism"
references:
  textbooks:
    - title: "Théorie des Topos et Cohomologie Étale des Schémas"
      author: "M. Artin, A. Grothendieck, J.-L. Verdier"
      edition: "SGA 4, Lecture Notes in Mathematics 269-271"
      publisher: "Springer"
      year: 1972
      chapters: ["Exposé IV: Topos"]
    - title: "Sheaves in Geometry and Logic"
      author: "Saunders Mac Lane, Ieke Moerdijk"
      edition: "Universitext"
      publisher: "Springer"
      year: 1992
      chapters: ["Ch. I: Categories of Functors", "Ch. II: Sheaves of Sets", "Ch. III: Grothendieck Topologies and Sheaves"]
    - title: "Higher Topos Theory"
      author: "Jacob Lurie"
      edition: "Annals of Mathematics Studies 170"
      publisher: "Princeton University Press"
      year: 2009
      chapters: ["Ch. 6: ∞-Topoi"]
  papers:
    - title: "Catégories fibrées et descente"
      author: "A. Grothendieck"
      journal: "Séminaire Bourbaki"
      year: 1959
      volume: "12"
      pages: "Exp. No. 190"
  databases:
    - type: "nLab"
      url: "https://ncatlab.org/nlab/show/topos"
    - type: "Stacks Project"
      url: "https://stacks.math.columbia.edu/tag/00VH"
review_status: "mathematical_reviewed"
---

# Topos 理论与 SGA 4

> **对标 nLab 页面**：topos, sheaf topos, geometric morphism  
> **核心文献**：SGA 4, Exposé IV; Mac Lane–Moerdijk; Lurie HTT Ch. 6

---

## 1. 引言：从层到 Topos 的跃迁

Grothendieck 在 1960 年代初研究韦伊猜想时，需要一个比拓扑空间更灵活、更代数化的"空间"概念。他发现：

> **真正重要的不是空间本身的点，而是空间上层的范畴。**

这一洞见导致了 **Grothendieck topos** 的诞生——一个具有足够好的范畴论性质（特别是具备"层的行为"）的范畴。SGA 4（1963–1964）将这一理论系统化，并为现代代数几何、数理逻辑和数学物理奠定了基石。

---

## 2. Grothendieck Topos 的等价定义

### 2.1 定义 A：层范畴

**定义 2.1**（SGA 4, Exposé IV, 1.1; Mac Lane–Moerdijk, Ch. III, §2; nLab: sheaf topos）。
设 $\mathcal{C}$ 为一个 small 范畴，$J$ 为 $\mathcal{C}$ 上的一个 **Grothendieck 拓扑**（或 **覆盖结构**）。则 **Topos** 定义为层范畴（category of sheaves）：
$$\operatorname{Sh}(\mathcal{C}, J) := \left\{F: \mathcal{C}^{\mathrm{op}} \to \mathbf{Set} \;\middle|\; F \text{ 是关于 } J \text{ 的层}\right\}.$$

**层的条件**：对任意覆盖筛（sieve）$S \in J(c)$，自然映射
$$F(c) \longrightarrow \operatorname{Hom}_{\mathbf{PSh}(\mathcal{C})}(S, F)$$
是双射。等价地，$F$ 将覆盖变为 $\mathbf{Set}$ 中的等化子（equalizer）。

### 2.2 定义 B：左正合反射子范畴

**定义 2.2**（SGA 4, Exposé IV, 1.2; Mac Lane–Moerdijk, Ch. III, §5, Thm 1）。
一个范畴 $\mathcal{E}$ 称为 **Grothendieck topos**，如果它等价于某个预层范畴 $\mathbf{PSh}(\mathcal{C}) = [\mathcal{C}^{\mathrm{op}}, \mathbf{Set}]$ 的**左正合反射子范畴**（left exact reflective subcategory）。

即：存在全忠实嵌入 $i: \mathcal{E} \hookrightarrow \mathbf{PSh}(\mathcal{C})$ 和左伴随 $a: \mathbf{PSh}(\mathcal{C}) \to \mathcal{E}$，使得 $a \dashv i$ 且 $a$ 保持有限极限（left exact）。这里的 $a$ 就是 **层化函子**（sheafification）。

### 2.3 定义 C：Giraud 公理

**定理 2.3**（Giraud 公理; SGA 4, Exposé IV, Thm 1.2; Mac Lane–Moerdijk, Appendix）。
一个范畴 $\mathcal{E}$ 是 Grothendieck topos 当且仅当它满足以下 Giraud 公理：
1. $\mathcal{E}$ 具有所有小极限和小余极限；
2. 小余极限与拉回交换（universality of colimits）；
3. $\mathcal{E}$ 中的等价关系是有效的（effective equivalence relations）；
4. $\mathcal{E}$ 具有一个小生成子集（small set of generators）。

**证明概要**。
$(\Rightarrow)$ 若 $\mathcal{E} = \operatorname{Sh}(\mathcal{C}, J)$，则作为 $\mathbf{Set}$-值函子范畴的反射子范畴，$\mathcal{E}$ 继承极限和余极限（层化保持有限极限），且预层范畴 $[\mathcal{C}^{\mathrm{op}}, \mathbf{Set}]$ 显然有小生成子（可表函子 $y(c)$ 的层化）。

$(\Leftarrow)$ 若 $\mathcal{E}$ 满足 Giraud 公理，取小生成子集 $\{G_i\}$，令 $\mathcal{C}$ 为 $\{G_i\}$ 生成的满子范畴。则嵌入 $y: \mathcal{C} \to \mathcal{E}$ 诱导几何态射 $(f^*, f_*): \mathcal{E} \to \mathbf{PSh}(\mathcal{C})$，可以证明 $f^*$ 是 fully faithful 且 $f_*$ 是其左伴随，从而 $\mathcal{E}$ 等价于某个层范畴。 ∎

---

## 3. 几何态射：Topos 之间的映射

### 3.1 基本定义

**定义 3.1**（SGA 4, Exposé IV, 3.1; Mac Lane–Moerdijk, Ch. VII, §1; nLab: geometric morphism）。
设 $\mathcal{E}, \mathcal{F}$ 为两个 topos。一个 **几何态射**（geometric morphism）$f: \mathcal{E} \to \mathcal{F}$ 是一个伴随对
$$f^*: \mathcal{F} \rightleftarrows \mathcal{E} : f_*$$
使得 $f^*$ 保持有限极限（left exact）。$f_*$ 称为 **直像函子**（direct image），$f^*$ 称为 **逆像函子**（inverse image）。

**注记 3.2**。几何态射的命名来源于拓扑空间的连续映射诱导的层态射：若 $f: X \to Y$ 是拓扑空间的连续映射，则 pullback $f^*: \operatorname{Sh}(Y) \to \operatorname{Sh}(X)$ 保持有限极限（因为拉回在 $\mathbf{Set}$ 中保持），从而诱导几何态射 $(f^*, f_*): \operatorname{Sh}(X) \to \operatorname{Sh}(Y)$。

### 3.2 点的概念

**定义 3.3**（SGA 4, Exposé IV, 6.1; nLab: point of a topos）。
一个 topos $\mathcal{E}$ 的 **点**（point）是一个几何态射
$$p: \mathbf{Set} \longrightarrow \mathcal{E}.$$

若 $\mathcal{E} = \operatorname{Sh}(X)$ 对某个拓扑空间 $X$，则 $X$ 的每一点 $x \in X$ 给出一个点 $p_x: \mathbf{Set} \to \operatorname{Sh}(X)$，其逆像函子 $p_x^*$ 就是茎函子（stalk functor）：
$$p_x^*(F) = F_x = \varinjlim_{U \ni x} F(U).$$

**重要现象**：存在具有"足够多点"的 topos，但它们不来自任何拓扑空间。这是 topos 理论比传统拓扑更一般的核心原因之一。

---

## 4. Topos 与逻辑：直觉主义的高阶模型

### 4.1 内部语言

**定理 4.1**（SGA 4, Exposé IV, 5; Mac Lane–Moerdijk, Ch. VI, §5）。
每个 Grothendieck topos $\mathcal{E}$ 都是一个 **初等 topos**（elementary topos），即它具有：
1. 所有有限极限和余极限；
2. 指数对象（exponentials）；
3. 子对象分类子（subobject classifier）$\Omega$。

**子对象分类子** $\Omega$ 在 $\mathcal{E} = \operatorname{Sh}(X)$ 中的具体形式为：对开集 $U \subset X$，
$$\Omega(U) = \{\text{开子集 } V \subset U\} = \mathcal{O}_X(U)^{\mathrm{op}}.$$
这恰好是 $X$ 上层的"真值对象"：子层 $F' \subset F$ 对应于态射 $F \to \Omega$。

### 4.2 直觉主义逻辑的语义

**定理 4.2**（Kripke-Joyal 语义; Mac Lane–Moerdijk, Ch. VI, §6）。
Topos $\mathcal{E}$ 中的语句可以用 **Kripke-Joyal 语义** 来解释，这是一种强制（forcing）语义：
- 对对象 $E \in \mathcal{E}$ 和公式 $\phi$，$E \Vdash \phi$ 表示 "$\phi$ 在 $E$ 上被强制为真"。
- 排中律 $E \Vdash \phi \lor \neg\phi$ 一般不成立，除非 $\mathcal{E}$ 是布尔 topos。

这使得 topos 成为 **直觉主义高阶逻辑** 的自然模型。

---

## 5. 与格洛腾迪克几何的联系

### 5.1 Étale Topos 与韦伊猜想

Grothendieck 引入 topos 的最原始动机是为代数簇 $X$ 定义 **étale 上同调**。关键构造是：

**定义 5.1**（SGA 4, Exposé VII）。
设 $X$ 为概形。其 **étale topos** $X_{\text{ét}}$ 定义为 $X$ 的 étale site 上的层范畴：
$$X_{\text{ét}} := \operatorname{Sh}(X_{\text{étale}}).$$

这里的对象是 $X$ 的 étale 态射 $U \to X$，覆盖由满族的 étale 态射给出。通过 topos 的抽象框架，可以定义 $l$-进上同调 $H^i_{\text{ét}}(X, \mathbb{Q}_l)$，并最终证明韦伊猜想（Deligne, 1974）。

### 5.2 基本群与 Galois 理论

**定理 5.2**（Grothendieck Galois 理论; SGA 1）。
设 $X$ 为连通概形，$\bar{x}$ 为几何点。则 étale topos $X_{\text{ét}}$ 的"基本群"就是代数基本群 $\pi_1^{\text{alg}}(X, \bar{x})$，它是拓扑基本群的 profinite 完备化。

更精确地说，有限 étale 覆盖范畴 $\mathbf{FEt}(X)$ 等价于有限连续 $\pi_1^{\text{alg}}(X, \bar{x})$-集范畴。这是 topos 理论在算术几何中最深刻的应用之一。

---

## 6. Lean4 形式化片段

Mathlib4 的 `CategoryTheory.Sites` 模块已实现了 Grothendieck 拓扑和层范畴的基础。以下是概念性代码：

```lean
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Grothendieck

universe u v

namespace ToposTheory

open CategoryTheory

-- Grothendieck 拓扑的定义
#check GrothendieckTopology

-- 层范畴
#check Sheaf

-- 层化函子（左正合左伴随）
#check sheafify

-- 可表函子的层化 = 层上的 Yoneda 嵌入
#check CategoryTheory.Sites.sheafYoneda

-- 子对象分类子的概念性定义（在 Set 值层范畴中）
structure SubobjectClassifier (C : Type u) [Category.{v} C]
    (J : GrothendieckTopology C) where
  Omega : Sheaf J (Type v)
  trueSub : Subsingleton (Sheaf J (Type v)) -- ⊤ : 1 → Ω
  classifies : ∀ (F : Sheaf J (Type v)) (S : Subobject F),
    ∃! χ : F ⟶ Omega, S.arrow = pullback trueSub.hom χ

end ToposTheory
```

**说明**：Mathlib4 对 topos 理论的实现目前集中在 sites 和 sheaves 层面。完整的初等 topos 公理（子对象分类子、指数对象、自然数对象）仍在逐步建设中。这与同伦类型论模块的发展并行进行。

---

## 7. 习题

**习题 7.1**（Mac Lane–Moerdijk, Ch. III, Ex. 3）。设 $X$ 为拓扑空间，$\mathcal{O}(X)$ 为其开集范畴。证明：预层 $F: \mathcal{O}(X)^{\mathrm{op}} \to \mathbf{Set}$ 是关于通常覆盖拓扑的层，当且仅当对任意开集 $U$ 和开覆盖 $\{U_i\}_{i \in I}$，序列
$$F(U) \longrightarrow \prod_i F(U_i) \rightrightarrows \prod_{i,j} F(U_i \cap U_j)$$
是等化子。

**习题 7.2**（SGA 4, Exposé IV, 4.9）。设 $f: X \to Y$ 为拓扑空间的连续映射。验证 $f$ 诱导的几何态射 $(f^*, f_*): \operatorname{Sh}(X) \to \operatorname{Sh}(Y)$ 确实满足 $f^* \dashv f_*$ 且 $f^*$ 保持有限极限。

**习题 7.3**（Giraud 公理的验证）。证明：预层范畴 $\mathbf{PSh}(\mathcal{C})$ 满足 Giraud 公理 1–4。进一步证明：若 $a: \mathbf{PSh}(\mathcal{C}) \to \mathcal{E}$ 是左正合反射（层化），则反射子范畴 $\mathcal{E}$ 也满足这些公理。

**习题 7.4**（综合）。设 $k$ 为代数闭域，$X = \mathbb{A}^1_k$ 为仿射直线。描述 étale site $X_{\text{étale}}$ 中的对象（即哪些态射 $U \to X$ 是 étale 的），并解释为什么 $X_{\text{ét}}$ 的点对应于 $X$ 的（几何）点。

---

## 8. 总结

本节从三个等价视角建立了 Grothendieck topos 的核心理论：

1. **层范畴视角**：$\operatorname{Sh}(\mathcal{C}, J)$ 是 topos 最直接的几何来源；
2. **范畴论视角**：左正合反射子范畴给出了 topos 的抽象特征；
3. **Giraud 公理视角**：四条公理完全刻画了 topos 的内蕴结构。

在此基础上，我们引入了：
- **几何态射** $f: \mathcal{E} \to \mathcal{F}$，作为 topos 之间的"连续映射"；
- **点的概念**，将茎函子推广到抽象的 topos 框架；
- **内部逻辑与子对象分类子**，揭示了 topos 与直觉主义逻辑的深刻联系；
- **étale topos**，展示了这一理论在代数几何和韦伊猜想证明中的核心作用。

这些内容是 SGA 4 的精髓，也是 nLab 上关于 topos 讨论的理论基础。
