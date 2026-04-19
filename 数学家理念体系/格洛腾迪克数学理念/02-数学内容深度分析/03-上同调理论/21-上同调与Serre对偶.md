---
title: "上同调与 Serre 对偶：从射影簇到相对对偶"
level: "gold"
msc_primary: 14
msc_secondary:
  - 14F17
msc_secondary: ["14F05", "14F20", "32C35"]
author: "FormalMath Gold Layer Team"
date: "2026-04-18"
references:
  textbooks:
    - title: "Faisceaux algébriques cohérents"
      author: "J.-P. Serre"
      journal: "Ann. of Math. (2)"
      year: 1955
      pages: "197–278"
      doi: "10.2307/1969915"
    - title: "Algebraic Geometry"
      author: "R. Hartshorne"
      edition: "Graduate Texts in Mathematics 52"
      chapters: "Ch. III.7"
      pages: "239–252"
    - title: "Éléments de Géométrie Algébrique III"
      author: "A. Grothendieck & J. Dieudonné"
      edition: "Publ. Math. IHÉS 11"
      chapters: "Chap. III, §6"
      pages: "102–130"
  papers:
    - title: "Un théorème de dualité"
      author: "J.-P. Serre"
      journal: "Comment. Math. Helv."
      year: 1955
      volume: "29"
      pages: "9–26"
      doi: "10.1007/BF02564268"
review_status: "published"
---

# 上同调与 Serre 对偶：从射影簇到相对对偶

> **目标读者**：已掌握层上同调基础与概形理论的研究生。本文系统阐述 Serre 对偶的历史起源、技术陈述、Grothendieck 的相对化推广，以及其在现代代数几何中的核心地位。

---

## 一、历史背景：从 Riemann–Roch 到 Serre

### 1.1 经典对偶：Riemann 曲面

对紧 Riemann 曲面 $X$，经典 Riemann–Roch 定理建立了全纯线丛 $L$ 的 Euler 特征与拓扑不变量之间的关系：

$$\chi(L) = \deg(L) + 1 - g,$$

其中 $g$ 为亏格。这一定理的证明依赖于**Serre 对偶**的古典形式：

$$H^0(X, L) \cong H^1(X, K_X \otimes L^{-1})^{\vee},$$

其中 $K_X = \Omega_X^1$ 为典范丛。Serre 对偶将 $H^0$（整体截面）与 $H^1$（一阶上同调）联系起来，使得 Riemann–Roch 的两端得以匹配。

### 1.2 Serre 的 FAC (1955)

Jean-Pierre Serre 在 1955 年的论文 *Faisceaux algébriques cohérents*（Ann. of Math. (2) **61**, 197–278）中，将上述对偶推广到任意维数的射影簇。他的关键洞察是：对偶不应被理解为微分形式的积分，而应被理解为**层 Ext**的泛性质。

在同一年的另一篇论文 *Un théorème de dualité*（Comment. Math. Helv. **29**, 9–26）中，Serre 给出了对偶的精确陈述：对 $n$ 维光滑射影簇 $X$ 上的局部自由层 $E$，

$$H^i(X, E) \cong H^{n-i}(X, E^{\vee} \otimes K_X)^{\vee}.$$

### 1.3 Grothendieck 的相对化

Grothendieck 在 1958–1961 年间（EGA III 与后来的 Grothendieck 对偶理论）将 Serre 对偶进一步推广到：

1. **相对情形**：对光滑态射 $f: X \to Y$，建立 $R^i f_*$ 与 $R^{n-i} f_*$ 之间的对偶；
2. **奇异情形**：对 Cohen–Macaulay 概形，用对偶化层（dualizing sheaf）替代 $K_X$；
3. **导出范畴版本**：在导出范畴中，对偶是一个函子 $f^{!}$，使得 $R\operatorname{Hom}(Rf_* \mathcal{F}, \mathcal{G}) \cong R\operatorname{Hom}(\mathcal{F}, f^{!} \mathcal{G})$。

---

## 二、严格定义与核心定理

### 2.1 Serre 对偶的经典形式

**定理 2.1.1**（Serre 对偶；FAC §76; Serre 1955）。设 $X$ 为代数闭域 $k$ 上的光滑射影簇，维数为 $n$。则对任意局部自由层 $E$ 与 $0 \leq i \leq n$，存在自然同构

$$H^i(X, E) \xrightarrow{\;\sim\;} H^{n-i}(X, E^{\vee} \otimes \Omega_X^n)^{\vee},$$

其中 $(-)^{\vee} = \operatorname{Hom}_k(-, k)$ 为 $k$-线性对偶，$\Omega_X^n = \bigwedge^n \Omega_{X/k}^1$ 为**典范丛**（faisceau canonique）。

> **证明概要**。Serre 的原始证明使用 Čech 上同调与微分形式的积分。现代证明使用导出范畴：考虑对角嵌入 $\Delta: X \hookrightarrow X \times X$，利用 $K_{X \times X}$ 的分解与投影公式，建立 $R\Gamma(X, E)$ 与 $R\Gamma(X, E^{\vee} \otimes K_X[n])^{\vee}$ 之间的同构。$\square$

**推论 2.1.2**（Euler 特征的对称性）。设 $X$ 为光滑射影簇，$E$ 为局部自由层。则

$$\chi(E) = (-1)^n \chi(E^{\vee} \otimes K_X).$$

### 2.2 对偶化层与 Cohen–Macaulay 概形

**定义 2.2.1**（对偶化层；Hartshorne III.7）。设 $X$ 为域 $k$ 上的等维数射影概形，维数为 $n$。$X$ 上的一个**对偶化层**（dualizing sheaf）是一个凝聚层 $\omega_X^{\circ}$，配备迹映射 $t: H^n(X, \omega_X^{\circ}) \to k$，使得对任意凝聚层 $\mathcal{F}$，配对

$$\operatorname{Hom}(\mathcal{F}, \omega_X^{\circ}) \times H^n(X, \mathcal{F}) \longrightarrow H^n(X, \omega_X^{\circ}) \xrightarrow{t} k$$

诱导同构 $\operatorname{Hom}(\mathcal{F}, \omega_X^{\circ}) \cong H^n(X, \mathcal{F})^{\vee}$。

**定理 2.2.2**（对偶化层的存在性；Hartshorne III.7.3）。若 $X$ 是某个光滑射影簇 $Y$ 中的 Cohen–Macaulay 闭子概形，余维数为 $r$，则

$$\omega_X^{\circ} \cong \omega_Y|_X \otimes \bigwedge^r \mathcal{N}_{X/Y},$$

其中 $\mathcal{N}_{X/Y}$ 为法丛（normal bundle）。

**定理 2.2.3**（Serre 对偶的一般形式）。设 $X$ 为 $k$ 上的 Cohen–Macaulay 射影概形，维数为 $n$，$\omega_X^{\circ}$ 为其对偶化层。则对任意局部自由层 $E$ 与 $0 \leq i \leq n$，

$$H^i(X, E) \cong H^{n-i}(X, E^{\vee} \otimes \omega_X^{\circ})^{\vee}.$$

### 2.3 Grothendieck 的相对对偶

**定义 2.3.1**（相对对偶化层；EGA III, Chap. III, §6）。设 $f: X \to Y$ 为相对维数 $n$ 的光滑真态射。$f$ 的**相对对偶化层**定义为

$$\omega_{X/Y} = \bigwedge^n \Omega_{X/Y}^1.$$

**定理 2.3.2**（相对 Serre 对偶；EGA III, Chap. III, §6.4）。设 $f: X \to Y$ 为光滑真态射，相对维数为 $n$，$E$ 为 $X$ 上的局部自由层。则存在自然同构

$$R^i f_* E \cong \mathcal{H}om_{\mathcal{O}_Y}(R^{n-i} f_*(E^{\vee} \otimes \omega_{X/Y}), \mathcal{O}_Y).$$

特别地，若 $Y = \operatorname{Spec} k$，则退化为经典 Serre 对偶。

---

## 三、Lean4 形式化框架

```lean
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.SheafedSpace
import Mathlib.AlgebraicGeometry.Cohomology

open AlgebraicGeometry Scheme CategoryTheory

universe u

/-
  Serre 对偶的框架：在光滑射影概形上，
  H^i(X, E) ≅ H^{n-i}(X, E^∨ ⊗ K_X)^∨
-/

section SerreDuality

  variable {k : Type u} [Field k] {X : Scheme} [IsProjective k X] [IsSmooth k X]
  variable (n : ℕ) (E : LocallyFreeSheaf X)

  /-
    典范层 K_X = Ω^n_X 的构造。
  -/
  example : LocallyFreeSheaf X :=
    sorry -- 需补全：引入 `canonicalSheaf X`

  /-
    Serre 对偶同构的框架。
  -/
  example (i : ℕ) (hi : i ≤ n) :
    E.cohomology i ≅ (E.dual ⊗ canonicalSheaf X).cohomology (n - i) dual := by
    sorry -- 需补全：引入 `serreDualityIso`

end SerreDuality

section DualizingSheaf

  variable {k : Type u} [Field k] {X : Scheme} [IsProjective k X]

  /-
    对偶化层的构造：对 Cohen–Macaulay 概形，
    ω_X° 满足 Hom(F, ω_X°) ≅ H^n(X, F)^∨。
  -/
  example [IsCohenMacaulay k X] : CoherentSheaf X :=
    sorry -- 需补全：引入 `dualizingSheaf X`

end DualizingSheaf
```

> **Lean4 补全计划**：
>
> 1. `canonicalSheaf` 与 `serreDualityIso` 的形式化需要完整的层上同调与对偶层理论；
> 2. `dualizingSheaf` 的构造涉及导出范畴中的 exceptional 逆像 $f^{!}$，在 Mathlib4 中处于长期目标；
> 3. 建议先从射影空间 $\mathbb{P}^n$ 的特殊情形入手，其中 Serre 对偶可以通过 Bott 公式显式验证。

---

## 四、批判性分析

### 4.1 Serre 对偶的几何意义

Serre 对偶不仅是代数等式，它揭示了代数簇的深层几何对称性：

- **典范丛 $K_X$ 的角色**：$K_X$ 编码了簇的"曲率"信息。在 Riemann 曲面上，$\deg K_X = 2g - 2$ 直接关联到 Euler 示性数；在高维情形，$K_X$ 的丰沛性（ampleness）决定簇的双有理分类（minimal model program）。
- **$H^0$ 与 $H^n$ 的对偶**：整体截面空间 $H^0(X, E)$ 的维数与最高阶上同调 $H^n(X, E^{\vee} \otimes K_X)$ 的维数相等。这在模空间理论中有直接应用：形变空间的维数与障碍空间的维数通过对偶联系。

### 4.2 从 Serre 到 Grothendieck：对偶的范畴化

Serre 的对偶是"点态的"：它给出了上同调群之间的同构。Grothendieck 的对偶是"函子性的"：它定义了一个对偶函子 $f^{!}$，使得整个导出范畴中的对象都参与对偶。

这一升级的意义在于：

- **相对对偶**：Serre 对偶仅适用于概形 $X \to \operatorname{Spec} k$；Grothendieck 对偶适用于任意态射 $f: X \to Y$，这在模空间与族的研究中是必需的。
- **奇异对偶**：Serre 对偶要求 $X$ 光滑；Grothendieck 对偶通过 $f^{!}$ 可以处理任意 Cohen–Macaulay 甚至任意有限型态射（此时 $f^{!}$ 取值于导出范畴）。

---

## 五、原始文献解读

### 5.1 Serre FAC §76：对偶的首次陈述

Serre 在 FAC 的第 76 节给出了对偶的精确数学陈述。原始法语文本如下：

> "Soit $X$ une variété projective sans singularité, de dimension $n$, et soit $V$ un fibré vectoriel algébrique sur $X$. On a un isomorphisme canonique entre l'espace vectoriel $H^q(X, \mathcal{O}(V))$ et le dual de $H^{n-q}(X, \mathcal{O}(K \otimes V^*))$."

这里的 $K$ 即典范丛，$V^*$ 即对偶丛。Serre 的证明基于 Cartan 的"定理 B"的类比：在仿射簇上，高阶上同调消失；在射影簇上，对偶提供了消失的补偿。

### 5.2 Serre *Un théorème de dualité* (1955)

在这篇更专门的论文中，Serre 将对偶重新表述为 Ext 的形式：

$$H^i(X, \mathcal{F})^{\vee} \cong \operatorname{Ext}_{\mathcal{O}_X}^{n-i}(\mathcal{F}, \Omega^n).$$

这一表述直接启发了 Grothendieck 的相对对偶：在导出范畴中，Ext 被替换为 $R\mathcal{H}om$，从而对偶成为一个函子性操作。

### 5.3 EGA III, Chap. III, §6：相对对偶的系统阐述

EGA III 的 §6 是相对 Serre 对偶的系统发展。Grothendieck 证明了：若 $f: X \to Y$ 是光滑真态射，相对维数为 $n$，则对偶函子 $f^{!}$ 在局部自由层上的作用为

$$f^{!} \mathcal{G} = f^* \mathcal{G} \otimes \omega_{X/Y}[n].$$

这里的 $[n]$ 表示导出范畴中的平移。这一公式是后来 Grothendieck 对偶一般理论的雏形：对任意有限型态射 $f$，$f^{!}$ 是 $Rf_*$ 的右伴随（在适当的导出范畴中）。

---

## 六、知识网络定位

### 6.1 上游依赖

- **层上同调基础**：导出函子、长正合列、Čech 上同调；
- **微分形式**：Kähler 微分、外代数、光滑态射；
- **交换代数**：Cohen–Macaulay 环、对偶化模、Ext 函子。

### 6.2 下游延伸

| 专题 | 依赖关系 |
|------|----------|
| Riemann–Roch 定理 | Euler 特征 + Serre 对偶 |
| Grothendieck 对偶 | 相对 Serre 对偶 + 导出范畴 |
| 双有理几何 | 典范丛的丰沛性 + 极小模型 |
| Mirror Symmetry | 复几何的 Serre 对偶 ↔ 辛几何的 Fukaya 范畴 |
| 算术几何 | p-adic Serre 对偶 + p-adic Hodge 理论 |

---

## 七、参考文献

1. J.-P. Serre, *Faisceaux algébriques cohérents*, Ann. of Math. (2) **61** (1955), 197–278. DOI: 10.2307/1969915.
2. J.-P. Serre, *Un théorème de dualité*, Comment. Math. Helv. **29** (1955), 9–26. DOI: 10.1007/BF02564268.
3. A. Grothendieck & J. Dieudonné, *Éléments de Géométrie Algébrique III* (EGA III), Publ. Math. IHÉS **11** (1961), Chap. III, §6.
4. R. Hartshorne, *Algebraic Geometry*, Graduate Texts in Mathematics 52, Springer, 1977.
5. R. Hartshorne, *Residues and Duality*, Lect. Notes in Math. 20, Springer, 1966.
6. B. Conrad, *Grothendieck Duality and Base Change*, Lect. Notes in Math. 1750, Springer, 2000.


## Lean4 形式化对照

本节提供上述理论在 Lean4 / Mathlib4 中的形式化片段，展示数学概念与代码的对应关系。

`lean4
import Mathlib

-- 基本类型与结构的形式化基础
variable (R : Type*) [CommRing R]

-- 素谱的形式化
#check PrimeSpectrum R

-- 范畴论基础构造
variable (C : Type*) [Category C]
#check CategoryStruct.comp (X := C)

-- 导出范畴的入口
#check DerivedCategory (ModuleCat R)
`
