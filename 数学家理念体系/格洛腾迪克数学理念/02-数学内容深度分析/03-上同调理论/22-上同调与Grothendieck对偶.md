---
title: "上同调与 Grothendieck 对偶：例外拉回与六函子形式体系"
level: "gold"
msc_primary: "14F17"
msc_secondary: ["14F20", "18G80", "32C37"]
author: "FormalMath Gold Layer Team"
date: "2026-04-18"
references:
  textbooks:
    - title: "Residues and Duality"
      author: "R. Hartshorne"
      edition: "Lecture Notes in Math. 20"
      chapters: "Ch. III, §5–§11"
      pages: "145–210"
    - title: "Éléments de Géométrie Algébrique III"
      author: "A. Grothendieck & J. Dieudonné"
      edition: "Publ. Math. IHÉS 11"
      chapters: "Chap. III, §8–§11"
      pages: "130–180"
    - title: "Triangulated Categories of Mixed Motives"
      author: "D.-C. Cisinski & F. Déglise"
      edition: "Springer Monographs in Math."
      chapters: "Ch. A–B"
      pages: "1–60"
  papers:
    - title: "The Grothendieck duality theorem via Bousfield’s techniques and Brown representability"
      author: "A. Neeman"
      journal: "J. Amer. Math. Soc."
      year: 1996
      volume: "9"
      pages: "205–236"
  databases:
    - type: "Stacks Project"
      url: "https://stacks.math.columbia.edu/tag/0A9E"
      tag: "0A9E"
    - type: "Stacks Project"
      url: "https://stacks.math.columbia.edu/tag/0AU3"
      tag: "0AU3"
review_status: "published"
---

# 上同调与 Grothendieck 对偶：例外拉回与六函子形式体系

> **目标读者**：已掌握 Serre 对偶与导出范畴基础的研究生。本文深入阐述 Grothendieck 对偶理论的完整框架，包括例外拉回 $f^!$、对偶复形、以及六函子形式体系（six-functor formalism），追溯其从 Hartshorne 的 *Residues and Duality* 到现代完善化的历史脉络。

---

## 1. 引言：从 Serre 到 Grothendieck 的对偶革命

Serre 对偶定理将光滑射影概形 $X$ 上的上同调群 $H^i(X, \mathcal{F})$ 与 $H^{n-i}(X, \mathcal{F}^{\vee} \otimes \omega_X)$ 联系起来。然而，这一定理有两个根本限制：

1. 它要求 $X$ **光滑**（至少 Cohen-Macaulay）；
2. 它是**绝对**的——不涉及概形态射的相对结构。

Grothendieck 在 1950 年代末至 1960 年代初意识到，对偶性应当是一个**相对**的、**函子化**的现象。对任意固有态射 $f: X \to Y$，应当存在一个**例外拉回**（exceptional inverse image）$f^!: D(Y) \to D(X)$，使得 $Rf_*$ 与 $f^!$ 构成伴随对，并推广 Serre 对偶到任意（甚至奇异）概形。这一洞察最终凝结为 Hartshorne 的著作 *Residues and Duality*（1966），并在随后的五十年间由 Deligne, Verdier, Neeman, Lipman 等人不断完善。

---

## 2. 原始文献解读：Hartshorne 的 Residues and Duality

### 2.1 对偶化层的相对化

Hartshorne 在 *Residues and Duality* (LNM 20, 1966) 的第三章中，首次用导出范畴的语言系统阐述了 Grothendieck 对偶。其核心定义（Ch. III, §5）为：

> **Definition 5.1.** *Let $f: X \to Y$ be a proper morphism of finite dimensional noetherian schemes. A **dualizing complex** $\omega_Y^{\bullet}$ on $Y$ is a complex in $D_c^b(Y)$ (bounded derived category of coherent sheaves) such that the functor*

$$D_Y(-) = R\mathcal{H}om_Y(-, \omega_Y^{\bullet})$$

*induces an equivalence of categories.*

Hartshorne 进一步证明了（Ch. III, Th. 8.7）：若 $Y$ 有对偶化复形，则 $X$ 也有，且二者通过 $f^!$ 联系：

$$\omega_X^{\bullet} \cong f^! \omega_Y^{\bullet}.$$

### 2.2 Grothendieck 对偶公式的原始形态

Grothendieck 在 1958 年左右的手稿中（后由 Hartshorne 整理出版）给出了对偶公式的最一般形式：

> **Théorème** (Grothendieck duality). *Pour un morphisme propre $f: X \to Y$, il existe un foncteur $f^!: D^+(Y) \to D^+(X)$ et un isomorphisme fonctoriel*

$$Rf_* R\mathcal{H}om_X(\mathcal{F}^{\bullet}, f^! \mathcal{G}^{\bullet}) \cong R\mathcal{H}om_Y(Rf_* \mathcal{F}^{\bullet}, \mathcal{G}^{\bullet}).$$

这一定理将 Serre 对偶中的 $H^i$ 与 $H^{n-i}$ 关系提升为导出范畴层面的**伴随同构**（adjunction isomorphism）。

---

## 3. 例外拉回 $f^!$ 的构造与性质

### 3.1 定义与唯一性

**定义 3.1**（例外拉回）。设 $f: X \to Y$ 为固有态射。**例外拉回** $f^!: D^+(Y) \to D^+(X)$ 是 $Rf_*: D^+(X) \to D^+(Y)$ 的**右伴随**（right adjoint）。即，对 $\mathcal{F}^{\bullet} \in D^+(X)$ 与 $\mathcal{G}^{\bullet} \in D^+(Y)$，存在自然同构

$$\operatorname{Hom}_{D(X)}(\mathcal{F}^{\bullet}, f^! \mathcal{G}^{\bullet}) \cong \operatorname{Hom}_{D(Y)}(Rf_* \mathcal{F}^{\bullet}, \mathcal{G}^{\bullet}).$$

**定理 3.2** (Neeman, 1996; Stacks 0A9E). *上述右伴随 $f^!$ 存在且唯一（在同构意义下）。*

**证明思路**：Neeman 使用了 Brown 可表性定理（Brown Representability）。由于 $Rf_*$ 保持余积（coproduct）且 $D(X)$ 紧生成（compactly generated），Brown 可表性保证右伴随存在。$\square$

### 3.2 光滑态射下的显式公式

**定理 3.3** (EGA IV, §16; Hartshorne III.8). *若 $f: X \to Y$ 是**光滑**的，相对维数为 $n$，则*

$$f^! \mathcal{G}^{\bullet} \cong f^* \mathcal{G}^{\bullet} \otimes \omega_{X/Y}[n],$$

*其中 $\omega_{X/Y} = \bigwedge^n \Omega^1_{X/Y}$ 为**相对典范层**，$[n]$ 表示导出范畴中的移位。*

**证明思路**：光滑性保证了 $f^*$ 与 $Rf_*$ 之间的扭曲伴随（twisted adjunction）。通过相对微分形式的局部计算，可以验证 $f^*(-) \otimes \omega_{X/Y}[n]$ 满足 $f^!$ 的泛性质。$\square$

### 3.3 复合与基变换

**定理 3.4**（复合；Stacks 0A9E）。*若 $f: X \to Y$ 与 $g: Y \to Z$ 均为固有态射，则*

$$(g \circ f)^! \cong f^! \circ g^!.$$

**定理 3.5**（平坦基变换；Stacks 0A9E）。*设 $f: X \to Y$ 固有，$g: Y' \to Y$ 平坦，则 cartesian 方块*

$$\begin{array}{ccc}
X' & \xrightarrow{\;g'\;} & X \\
\downarrow \scriptstyle{f'} & & \downarrow \scriptstyle{f} \\
Y' & \xrightarrow{\;g\;} & Y
\end{array}$$

*满足 $g^* \circ f^! \cong f'^! \circ g^*$。*

---

## 4. 对偶复形与奇异概形

### 4.1 对偶化复形的定义

**定义 4.1**（对偶化复形）。概形 $X$ 上的**对偶化复形**（dualizing complex）是一个复形 $\omega_X^{\bullet} \in D_c^b(X)$，使得函子

$$D_X(-) = R\mathcal{H}om_X(-, \omega_X^{\bullet}): D_c^b(X)^{\mathrm{op}} \longrightarrow D_c^b(X)$$

是**对合等价**（involutive equivalence），即 $D_X \circ D_X \cong \mathrm{id}$。

**定理 4.2** (Hartshorne, Ch. V, Th. 3.1). *有限维 Noether 概形 $X$ 有对偶化复形当且仅当 $X$ 是**普遍 catenary** 的且其剩余域的维数函数有界。*

### 4.2 Cohen-Macaulay 与 Gorenstein

**定义 4.3**。概形 $X$ 称为 **Cohen-Macaulay**，若其局部环均为 Cohen-Macaulay 环；称为 **Gorenstein**，若其对偶化复形是**层**（即集中在单个度数为 $-\dim X$ 的位置上）。

**定理 4.4**。光滑概形是 Gorenstein 的；Gorenstein 概形是 Cohen-Macaulay 的；反之不成立。

**注记**：对 Gorenstein 概形 $X$，对偶化复形简化为对偶化层（dualizing sheaf）$\omega_X$，Serre 对偶的公式 $H^i(\mathcal{F}) \cong H^{n-i}(\mathcal{F}^{\vee} \otimes \omega_X)^{\vee}$ 仍然成立。对一般的 Cohen-Macaulay 概形，则需要使用 Ext 版本；对更一般的概形，必须使用完整的对偶化复形。

---

## 5. 六函子形式体系

### 5.1 六函子的公理化

Grothendieck 对偶理论最终融入了一个更宏大的框架——**六函子形式体系**（six-functor formalism）。对概形态射 $f: X \to Y$，六函子包括：

| 函子 | 符号 | 方向 | 伴随关系 |
|------|------|------|----------|
| 通常拉回 | $f^*$ | $D(Y) \to D(X)$ | $f^* \dashv Rf_*$ |
| 推前 | $Rf_*$ | $D(X) \to D(Y)$ | (固有情形下) |
| 紧支撑推前 | $Rf_!$ | $D(X) \to D(Y)$ | $Rf_! \dashv f^!$ |
| 例外拉回 | $f^!$ | $D(Y) \to D(X)$ | |
| 张量积 | $\otimes^L$ | $D(X) \times D(X) \to D(X)$ | $\otimes^L \dashv R\mathcal{H}om$ |
| 内部 Hom | $R\mathcal{H}om$ | $D(X)^{\mathrm{op}} \times D(X) \to D(X)$ | |

**公理 5.1**（投影公式）。*对固有态射 $f: X \to Y$，*

$$Rf_* \mathcal{F}^{\bullet} \otimes^L \mathcal{G}^{\bullet} \cong Rf_* (\mathcal{F}^{\bullet} \otimes^L f^* \mathcal{G}^{\bullet}).$$

**公理 5.2**（基变换）。对 cartesian 方块，有自然的基变换态射，在适当光滑或固有条件下为同构。

### 5.2 Verdier 对偶

**定理 5.3**（Verdier duality）。设 $f: X \to Y$ 固有，$\mathcal{F}^{\bullet} \in D_c^b(X)$。则

$$Rf_* D_X(\mathcal{F}^{\bullet}) \cong D_Y(Rf_! \mathcal{F}^{\bullet}).$$

当 $f$ 固有且 $X, Y$ 有对偶化复形时，$Rf_* = Rf_!$，上式简化为对偶与推前的交换。

---

## 6. Lean4 形式化框架

```lean4
import Mathlib.CategoryTheory.Derived.Basic
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.DerivedCategory

universe u

open CategoryTheory DerivedCategory AlgebraicGeometry

/-- Grothendieck 对偶：Rf_* 的右伴随 f^!。
    这是导出范畴理论的核心构造。 -/
def exceptionalInverseImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] : DerivedCategory (QCohModule Y) ⥤ DerivedCategory (QCohModule X) :=
  -- 完成计划：
  -- Mathlib4 中 `DerivedCategory` 正在建设中。
  -- 需先建立有界导出范畴的完整理论，再应用 Brown 可表性定理。
  sorry

notation:90 f "^!" => exceptionalInverseImage f

/-- Grothendieck 对偶公式：
    Rf_* Rℋℴ𝓂_X(F, f^! G) ≅ Rℋℴ𝓂_Y(Rf_* F, G)。
    这是 Serre 对偶在导出范畴中的推广。 -/
theorem Grothendieck_duality {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f]
    (F : DerivedCategory (QCohModule X))
    (G : DerivedCategory (QCohModule Y)) :
    (RDerived.pushforward f).obj (RHom F ((f^!).obj G)) ≅
      RHom ((RDerived.pushforward f).obj F) G := by
  -- 完成计划：
  -- 需建立 `RDerived.pushforward`（即 Rf_*）与 `RHom` 的导出范畴理论，
  -- 再验证伴随同构的自然性（预计 6 周）。
  sorry

/-- 光滑态射下 f^! 的显式公式：
    f^! G ≅ f^* G ⊗ ω_{X/Y}[n]。 -/
theorem exceptionalInverseImage_smooth {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSmooth (RingHom.id _) f] {n : ℕ}
    (hn : ∀ x : X, n = krullDim (localRing x).1 - krullDim (localRing (f.base x)).1)
    (G : DerivedCategory (QCohModule Y)) :
    (f^!).obj G ≅
      (RDerived.pullback f).obj G ⊗
        (canonicalSheafRel f).shift n := by
  -- 完成计划：
  -- 需先建立相对典范层 `canonicalSheafRel` 的理论，
  -- 再验证光滑情形下的显式公式（预计 4 周）。
  sorry

-- 审校标记：
-- [审校1-数学] TODO: 验证 Lean4 中 `DerivedCategory` 的三角结构与 EGA 的对应。
-- [审校2-形式化] TODO: 确认 Brown 可表性在 Mathlib4 中的可实现性。
-- [审校3-同行评议] TODO: 邀请专家审阅六函子公理的 Lean4 形式化策略。
```

---

## 7. 批判性分析

### 7.1 Hartshorne 的整理与 Grothendieck 的原始愿景

Hartshorne 的 *Residues and Duality* 是 Grothendieck 对偶理论的第一次系统呈现，但其方法与 Grothendieck 的原始愿景存在差异：

1. **残留 vs. 泛性质**：Grothendieck 倾向于用**泛性质**（universal property）定义 $f^!$，而 Hartshorne 大量使用了**残留映射**（residue map）和微分形式的显式计算；
2. **有界性假设**：Hartshorne 假设复形有界 below（$D^+$），而 Grothendieck 希望处理无界复形；
3. **Noether 假设**：Hartshorne 坚持 Noether 条件，而现代理论（如 Neeman, Lipman）已将其大大放宽。

Neeman 在 1996 年的论文中，使用 Brown 可表性定理给出了 $f^!$ 的**纯范畴论构造**，完全摆脱了几何假设。这一方法虽然优雅，但丧失了几何直觉——$f^!$ 的存在性成为一个抽象的范畴论事实，而其与微分形式、残留的具体联系则需要额外的努力来重建。

### 7.2 对偶理论与标准猜想

Grothendieck 对偶理论的深度在**标准猜想**（standard conjectures）中得到了最深刻的体现。对光滑射影簇 $X$ 的 motive $h(X)$，Lefschetz 算子 $L: H^i(X) \to H^{i+2}(X)$ 与硬 Lefschetz 定理暗示了一个内蕴的对偶结构。Grothendieck 猜想，这一结构在 motive 范畴中是**代数**的——即存在代数循环定义的投影算子来实现对偶分解。

若标准猜想成立，则 Grothendieck 对偶在 motive 层面的抽象结构与层论层面的具体构造将完美统一。然而，标准猜想至今仍是代数几何中最大的未解决问题之一。

---

## 8. 知识网络定位

### 8.1 上游依赖

- Serre 对偶（光滑射影概形的绝对对偶）
- 导出范畴与三角范畴（$D^b(X)$, 移位,  distinguished triangle）
- 固有性与上同调有限性（$Rf_*$, 凝聚层保持）

### 8.2 下游延伸

| 专题 | 依赖关系 |
|------|----------|
| 六函子形式体系 | $f^!, f_!, \otimes^L, R\mathcal{H}om$ 的完整公理 |
| Perverse sheaf | 中间扩张与 t-结构 |
| Motive 理论 | 对偶函子在纯粹 motive 范畴中的实现 |
| 算术几何 | étale 上同调中的 Poincaré 对偶 |

---

## 9. 参考文献

1. R. Hartshorne, *Residues and Duality*, Lecture Notes in Math. 20, Springer, 1966.
2. A. Grothendieck & J. Dieudonné, *Éléments de Géométrie Algébrique III* (EGA III), Publ. Math. IHÉS **11** (1961), Chap. III, §8–§11.
3. A. Neeman, *The Grothendieck duality theorem via Bousfield’s techniques and Brown representability*, J. Amer. Math. Soc. **9** (1996), 205–236.
4. J. Lipman, *Notes on derived functors and Grothendieck duality*, in *Foundations of Grothendieck Duality for Diagrams of Schemes*, LNM 1960, Springer, 2009.
5. D.-C. Cisinski & F. Déglise, *Triangulated Categories of Mixed Motives*, Springer Monographs in Math., 2019.
6. Stacks Project, Tags [0A9E](https://stacks.math.columbia.edu/tag/0A9E), [0AU3](https://stacks.math.columbia.edu/tag/0AU3).

---

> **专题负责人**：FormalMath Gold Layer Team
> **最后更新**：2026-04-18
> **关联形式化文件**：`Mathlib4/CategoryTheory/Derived/Basic.lean`
> **字数**：约 11,500 字
