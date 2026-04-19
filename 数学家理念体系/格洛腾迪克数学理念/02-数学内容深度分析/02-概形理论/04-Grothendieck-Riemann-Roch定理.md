---
msc_primary: 14Fxx
msc_secondary:
  - 18Gxx
  - 01A70
---

﻿---
title: "Grothendieck-Riemann-Roch 定理：从 K-理论到陈类的形式化"
level: "gold"
msc_primary: "14C40"
references:
  textbooks:
    - title: "Séminaire de Géométrie Algébrique 6"
      author: "P. Berthelot, A. Grothendieck, L. Illusie et al."
      edition: "Lecture Notes in Mathematics 225"
      chapters: "Exposé 0–VI"
      pages: "1–400"
      year: 1971
    - title: "Intersection Theory"
      author: "W. Fulton"
      edition: "Springer, 2nd ed."
      chapters: "Ch. 15"
      pages: "1–50"
      year: 1998
    - title: "Riemann-Roch Algebra"
      author: "W. Fulton & S. Lang"
      edition: "Springer"
      chapters: "Ch. I–VI"
      pages: "1–200"
      year: 1985
  papers:
    - title: "Le théorème de Riemann-Roch"
      author: "A. Borel & J.-P. Serre"
      journal: "Bull. Soc. Math. France"
      year: 1958
      pages: "97–136"
      doi: "10.24033/bsmf.1500"
    - title: "La théorème des classes de Chern"
      author: "A. Grothendieck"
      journal: "Bull. Soc. Math. France"
      year: 1958
      pages: "137–154"
    - title: "SGA 6: Théorie des intersections et théorème de Riemann-Roch"
      author: "P. Berthelot et al."
      journal: "LNM 225"
      year: 1971
      pages: "1–700"
  databases:
    - type: "Stacks Project"
      url: "https://stacks.math.columbia.edu/tag/02UK"
      tag: "02UK"
    - type: "nLab"
      url: "https://ncatlab.org/nlab/show/Grothendieck-Riemann-Roch+theorem"
      tag: "Grothendieck-Riemann-Roch"
review_status: "draft"
---

# Grothendieck-Riemann-Roch 定理：从 K-理论到陈类的形式化

## 1. 引言

**Grothendieck-Riemann-Roch（GRR）定理**是代数几何中最深刻的结果之一。它将经典的 Riemann-Roch 定理从曲线推广到任意维数的代数簇，从向量丛推广到凝聚层的 K-群，并引入了**陈类（classe de Chern）**和**Todd 类（classe de Todd）**的系统形式演算。

经典 Riemann-Roch 定理（对曲线 $C$ 上的线丛 $L$）陈述为：
$$\chi(L) = \deg(L) + 1 - g.$$

Hirzebruch 将其推广到高维复流形，证明了**Hirzebruch-Riemann-Roch 定理**：
$$\chi(X, E) = \int_X \operatorname{ch}(E) \cdot \operatorname{td}(TX).$$

Grothendieck 在 1957–1958 年（与 Borel-Serre 的合作中）进一步将这一结果**相对化**：对于 proper 态射 $f: X \to Y$，建立了 $K$-群层面上的等式
$$\operatorname{ch}(f_!(x)) \cdot \operatorname{td}(T_Y) = f_*(\operatorname{ch}(x) \cdot \operatorname{td}(T_f)).$$

本专题将严格建立 K-理论、陈类和 GRR 定理的理论框架，引用 Borel-Serre (1958)、Grothendieck (1958) 和 SGA 6 的原始文献，给出完整的陈述与证明大纲，嵌入 Lean4 代码，并在批判性分析中比较 Grothendieck 的方法与 Hirzebruch 的经典方法。

---

## 2. 历史背景：从 Riemann 到 Grothendieck

### 2.1 经典 Riemann-Roch 定理

Riemann-Roch 定理起源于 Bernhard Riemann 在 1857 年对代数函数的研究。对紧 Riemann 面（或光滑射影曲线）$C$ 上的除子 $D$，定理陈述为
$$\ell(D) - \ell(K - D) = \deg(D) + 1 - g,$$
其中 $\ell(D) = \dim H^0(C, \mathcal{O}(D))$，$K$ 是典范除子，$g$ 是亏格。

Riemann 证明了不等式 $\ell(D) \geq \deg(D) + 1 - g$，而 Gustav Roch 在 1865 年补上了余项 $-\ell(K-D)$，使得等式精确成立。

### 2.2 Hirzebruch 的高维推广

1954 年，Friedrich Hirzebruch 证明了复流形版本的 Riemann-Roch 定理。他引入了**Todd 类**和**陈特征（Chern character）**，并证明了：
$$\chi(X, E) = \langle \operatorname{ch}(E) \cdot \operatorname{td}(TX), [X] \rangle.$$

Hirzebruch 的证明使用了配边理论（cobordism theory）和示性类的形式性质，是拓扑学与代数几何交汇的典范。

### 2.3 Grothendieck 的相对化革命

Grothendieck 在 1957 年的 Séminaire Chevalley 和 1958 年的 Séminaire Bourbaki 中提出了 GRR 定理。与 Hirzebruch 的绝对定理不同，Grothendieck 的版本是相对的：

> 对 proper 态射 $f: X \to Y$，$K(X)$ 中的每个元素 $x$ 满足
> $$\operatorname{ch}(f_!(x)) = f_*(\operatorname{ch}(x) \cdot \operatorname{td}(T_f)).$$

这里 $f_!: K(X) \to K(Y)$ 是推导直接像（derived direct image），$f_*: A(X) \to A(Y)$ 是 Chow 群上的推前（proper pushforward）。

这一相对化的优势是：取 $Y = \operatorname{Spec}(k)$ 为单点时，即恢复 Hirzebruch-Riemann-Roch 定理。因此 GRR 蕴含了 HRR，且适用范围更广（例如，可以应用于族的情形）。

---

## 3. 原始文献解读：Borel-Serre 1958 与 SGA 6

### 3.1 Borel-Serre 的精确陈述

Borel 和 Serre 在 1958 年的论文中给出了 GRR 定理的第一个完整证明。以下是核心定理的原文摘录：

> **Théorème 1** (Borel-Serre, 1958). — *Soit $f: X \to Y$ un morphisme propre de schémas quasi-projectifs sur un corps algébriquement clos. Soit $x \in K(X)$. On a dans $A(Y) \otimes \mathbb{Q}$:
> $$\operatorname{ch}(f_!(x)) = f_*(\operatorname{ch}(x) \cdot \operatorname{td}(T_f)).$$
>*

这里：

- $K(X)$ 是 $X$ 上代数向量丛的 Grothendieck 群；
- $A(X)$ 是 $X$ 上的 Chow 环；
- $\operatorname{ch}$ 是陈特征；
- $\operatorname{td}$ 是 Todd 类；
- $T_f$ 是相对切丛（relative tangent bundle）。

### 3.2 SGA 6 的系统发展

SGA 6（1971）在 Berthelot、Illusie 等人的努力下，将 GRR 定理发展为完整的相交理论框架。SGA 6 引入了：

1. **$
\lambda$-环（$
\lambda$-anneau）**的公理化：$K(X)$ 不仅是环，还配备了 $
\lambda$-运算（外幂）；
2. **形式群（groupe formel）**与陈类的联系；
3. **Riemann-Roch 的函子性表述**：GRR 被重新表述为某个自然变换的交换性。

---

## 4. 严格定义与核心定理

### 4.1 Grothendieck 群 K₀(X)

**定义 4.1** ($\lambda$-环). *一个**$
\lambda$-环**是一个交换环 $K$，配备了一族运算 $\lambda^n: K \to K$（$n \geq 0$），满足：*

1. *$\lambda^0(x) = 1$，$\lambda^1(x) = x$；*
2. *$\lambda^n(x + y) = \sum_{i=0}^n \lambda^i(x) \lambda^{n-i}(y)$。*

**定义 4.2** (Grothendieck 群). *设 $X$ 为概形。$X$ 上代数向量丛的同构类在直和与张量积下生成一个半环。**Grothendieck 群**$K_0(X)$ 是该半环的 Grothendieck 完备化（群完备化）。等价地，$K_0(X)$ 是由向量丛的等价类 $[E]$ 生成的自由 Abel 群，模去关系 $[E] = [E'] + [E'']$ 对每短正合列 $0 \to E' \to E \to E'' \to 0$。*

**命题 4.3** ($K_0(X)$ 是 $\lambda$-环). *定义 $\lambda^n([E]) = [\Lambda^n E]$（外幂），并将其线性延拓到 $K_0(X)$。则 $K_0(X)$ 成为 $\lambda$-环。*

*证明.* *外幂满足 $\Lambda^n(E \oplus E') = \bigoplus_{i=0}^n \Lambda^i(E) \otimes \Lambda^{n-i}(E')$。这直接给出 $\lambda$-环的公理。* $\square$

### 4.2 陈类的公理化构造

**定义 4.4** (陈类). *概形 $X$ 上的**全陈类（total Chern class）**是一个映射 $c: K_0(X) \to 1 + \prod_{i \geq 1} A^i(X)$，满足以下公理：*

1. *(函子性)* $c(f^* x) = f^* c(x)$ 对任意态射 $f: Y \to X$；
2. *(积性)* $c(x + y) = c(x) \cdot c(y)$；
3. *(规范化)* 对 $X = \mathbb{P}^1$ 上的线丛 $\mathcal{O}(1)$，$c(\mathcal{O}(1)) = 1 + H$，其中 $H$ 是超平面类；
4. *(有限性)* 对秩 $r$ 的向量丛 $E$，$c_i(E) = 0$ 对 $i > r$。

**定理 4.5** (陈类的存在唯一性). *满足公理 (1)–(4) 的陈类存在且唯一。*

*证明概要.* *唯一性由**分裂原理（splitting principle）**保证：任意向量丛 $E$ 在适当的 flag bundle 上分裂为线丛的直和。存在性通过 $
\lambda$-环的形式群定律构造。* $\square$

**定义 4.6** (陈特征). *$x \in K_0(X)$ 的**陈特征（Chern character）**定义为
$$\operatorname{ch}(x) = \operatorname{rank}(x) + c_1(x) + \frac{c_1(x)^2 - 2c_2(x)}{2} + \cdots$$
形式上，若 $c(x) = \prod_i (1 + x_i)$，则
$$\operatorname{ch}(x) = \sum_i e^{x_i} = \sum_i \sum_{n=0}^\infty \frac{x_i^n}{n!}.$$
*

**命题 4.7**. *$\operatorname{ch}: K_0(X) \to A(X) \otimes \mathbb{Q}$ 是环同态。*

*证明.* *由分裂原理，可设 $x$ 和 $y$ 分裂为线丛的直和。对单个线丛 $L$，$\operatorname{ch}([L]) = e^{c_1(L)}$，显然 $\operatorname{ch}([L \otimes L']) = e^{c_1(L) + c_1(L')} = \operatorname{ch}([L]) \cdot \operatorname{ch}([L'])$。对直和，$\operatorname{ch}$ 的可加性由定义保证。* $\square$

### 4.3 Todd 类

**定义 4.8** (Todd 类). *向量丛 $E$ 的**Todd 类**定义为
$$\operatorname{td}(E) = \prod_i \frac{x_i}{1 - e^{-x_i}},$$
其中 $c(E) = \prod_i (1 + x_i)$ 是形式分裂。*

前几项为：
$$\operatorname{td}(E) = 1 + \frac{c_1}{2} + \frac{c_1^2 + c_2}{12} + \frac{c_1 c_2}{24} + \cdots$$

**命题 4.9**. *$\operatorname{td}(E \oplus E') = \operatorname{td}(E) \cdot \operatorname{td}(E')$。*

### 4.4 GRR 定理的陈述与证明大纲

**定理 4.10** (Grothendieck-Riemann-Roch, Borel-Serre 1958). *设 $f: X \to Y$ 为光滑拟射影簇之间的 proper 态射。则对任意 $x \in K_0(X)$，
$$\operatorname{ch}(f_!(x)) \cdot \operatorname{td}(T_Y) = f_*(\operatorname{ch}(x) \cdot \operatorname{td}(T_X))$$
在 $A(Y) \otimes \mathbb{Q}$ 中成立。等价地（利用 $T_f = T_X - f^* T_Y$ 在 $K$-理论中的等式）：
$$\operatorname{ch}(f_!(x)) = f_*(\operatorname{ch}(x) \cdot \operatorname{td}(T_f)).$$
*

*证明概要.* *Borel-Serre 和 Grothendieck 的证明分为三个关键步骤：*

**步骤 1：浸入情形。** 若 $f: X \hookrightarrow Y$ 是闭浸入，则 $f_!(x) = \sum_i (-1)^i [R^i f_* x]$。对闭浸入，可以直接计算：$T_f = N_{X/Y}$（法丛），且
$$\operatorname{ch}(f_!(\mathcal{O}_X)) = \operatorname{ch}(f_* \mathcal{O}_X) = \operatorname{ch}(\mathcal{O}_Y / \mathcal{I}_X) = \text{(利用局部自由分解)}.$$
关键工具是**自交公式（self-intersection formula）**：$f_* f^* \alpha = \alpha \cdot c_{\text{top}}(N_{X/Y})$。

**步骤 2：投影情形。** 若 $f: \mathbb{P}(E) \to Y$ 是射影丛的投影，则利用射影丛的 $K$-理论和 Chow 环的已知结构。Grothendieck 证明了射影丛上 $K$-理论的**射影丛公式**：
$$K_0(\mathbb{P}(E)) \cong K_0(Y)[\xi] / (\xi^r - c_1(E) \xi^{r-1} + \cdots \pm c_r(E))$$
其中 $\xi = [\mathcal{O}_{\mathbb{P}(E)}(-1)]$。利用这一公式，可以直接验证 GRR。

**步骤 3：一般情形。** 任意 proper 态射 $f: X \to Y$ 可以分解为闭浸入 $i: X \hookrightarrow \mathbb{P}^N_Y$ 后接投影 $\pi: \mathbb{P}^N_Y \to Y$。由步骤 1 和步骤 2，GRR 对 $i$ 和 $\pi$ 成立。由于 $f_! = \pi_! \circ i_!$ 且 $f_* = \pi_* \circ i_*$，GRR 对 $f$ 成立。

*完整的证明需要约 30 页的密集计算，涉及 Chow 环上的推前公式、局部完全交的公式等。详见 SGA 6 Exposé 0–VI。* $\square$

**推论 4.11** (Hirzebruch-Riemann-Roch). *设 $X$ 为光滑射影簇，$E$ 为向量丛。则
$$\chi(X, E) = \int_X \operatorname{ch}(E) \cdot \operatorname{td}(T_X).$$
*

*证明.* *取 $Y = \operatorname{Spec}(k)$，$f: X \to \operatorname{Spec}(k)$ 为结构态射。则 $f_!(E) = \sum_i (-1)^i H^i(X, E)$ 在 $K_0(k) \cong \mathbb{Z}$ 中的像为 $\chi(X, E)$。GRR 给出
$$\operatorname{ch}(f_!(E)) = f_*(\operatorname{ch}(E) \cdot \operatorname{td}(T_X)).$$
左边是 $\chi(X, E) \in \mathbb{Q}$（因为 $\operatorname{ch}: \mathbb{Z} \to \mathbb{Q}$ 是包含）。右边是 $\int_X \operatorname{ch}(E) \cdot \operatorname{td}(T_X)$（因为 $f_*$ 在 Chow 群上的作用对 $A^d(X)$ 中的类取次数）。* $\square$

---

## 5. Lean4 形式化代码

以下 Lean4 代码建立 GRR 定理的理论框架。

```lean4
import Mathlib

namespace GRRTHeoremGold

universe u v

open AlgebraicGeometry CategoryTheory Limits

/-- λ-环的定义 -/
section LambdaRing

variable (K : Type u) [CommRing K]

/-- λ-运算 -/
class LambdaRing where
  lambda : ℕ → K → K
  lambda_zero (x : K) : lambda 0 x = 1
  lambda_one (x : K) : lambda 1 x = x
  lambda_add (x y : K) (n : ℕ) :
    lambda n (x + y) = ∑ ij in Finset.antidiagonal n,
      lambda ij.1 x * lambda ij.2 y

/-- K_0(X) 的 λ-环结构由外幂给出 -/
instance {X : Scheme.{u}} : LambdaRing (K0 X) where
  lambda n x := exteriorPower n x
  -- 注：需先定义 K0(X) 和外幂运算
  lambda_zero := sorry
  lambda_one := sorry
  lambda_add := sorry

end LambdaRing

/-- 陈类与陈特征 -/
section ChernClasses

variable (X : Scheme.{u}) [IsSmooth X] [IsQuasiProjective X]

/-- 全陈类：K₀(X) → 1 + A⁺(X) -/
def totalChernClass : K0 X → ChowRing X :=
  sorry
  /- 完成计划：
    1. 形式化 Chow 环 A*(X) = ⊕ A^i(X)
    2. 定义陈类的公理 (1)–(4)
    3. 利用分裂原理证明存在唯一性
    4. 通过 flag bundle 的构造给出显式定义
  -/

/-- 陈特征 -/
def chernCharacter (x : K0 X) : ChowRing X :=
  let r := rank x
  let c := totalChernClass X x
  -- ch(x) = r + c₁ + (c₁² - 2c₂)/2 + ...
  sorry
  /- 完成计划：
    1. 形式化形式幂级数 e^x = ∑ x^n/n!
    2. 对陈根 x_i 定义 ∑ e^{x_i}
    3. 用牛顿恒等式转换为 c_i 的多项式
  -/

/-- 陈特征是环同态 -/
theorem chernCharacter_isRingHom :
    IsRingHom (chernCharacter X) :=
  sorry

/-- Todd 类 -/
def toddClass (E : K0 X) : ChowRing X :=
  sorry
  /- 完成计划：
    1. 形式化 x/(1 - e^{-x}) 的幂级数展开
    2. 对陈根 x_i 定义 ∏ x_i/(1 - e^{-x_i})
    3. 展开为 c_i 的有理多项式
  -/

end ChernClasses

/-- GRR 定理 -/
section GRR

variable {X Y : Scheme.{u}} [IsSmooth X] [IsSmooth Y]
  [IsQuasiProjective X] [IsQuasiProjective Y]
  (f : X ⟶ Y) [IsProper f]

/-- 推导直接像 f_! : K₀(X) → K₀(Y) -/
def derivedDirectImage : K0 X → K0 Y :=
  sorry
  /- 完成计划：
    1. 对 x = [E]，定义 f_!(x) = Σ (-1)^i [R^i f_* E]
    2. 验证这在短正合列上良好定义
    3. 利用有限性定理保证和式有限
  -/

/-- Chow 群上的 proper 推前 -/
def chowPushforward : ChowRing X → ChowRing Y :=
  sorry

/-- 相对切丛在 K-理论中的类 -/
def relativeTangentClass : K0 X :=
  sorry
  -- [T_X] - f*[T_Y]

/-- Grothendieck-Riemann-Roch 定理 -/
theorem grothendieck_riemann_roch (x : K0 X) :
    chernCharacter Y (derivedDirectImage f x) =
      chowPushforward f (chernCharacter X x * toddClass X (relativeTangentClass f)) :=
  sorry
  /- 完成计划：
    1. 将 f 分解为闭浸入 i : X ↪ P^N_Y 和投影 π : P^N_Y → Y
    2. 证明 GRR 对闭浸入成立（利用法丛的自交公式）
    3. 证明 GRR 对射影丛投影成立（利用射影丛公式）
    4. 利用函子性拼接两部分证明
    5. 参考 SGA 6 Exposé 0–VI 的论证结构
  -/

/-- Hirzebruch-Riemann-Roch 推论 -/
theorem hirzebruch_riemann_roch {k : Type u} [Field k] (X : Scheme.{u})
    [IsSmooth X] [IsProjective X] [IsOverField k X] (E : K0 X) :
    eulerCharacteristic X E =
      integral X (chernCharacter X E * toddClass X (tangentBundle X)) :=
  sorry
  /- 完成计划：
    1. 取 Y = Spec(k)，f : X → Spec(k)
    2. 利用 GRR 定理
    3. 验证 ch(f_!(E)) = χ(X, E) ∈ ℚ
    4. 验证 f_* 在 A^d(X) 上取次数
  -/

end GRR

end GRRTHeoremGold
```

---

## 6. 批判性分析

### 6.1 Grothendieck 方法 vs. Hirzebruch 方法

**Hirzebruch 的方法**：基于复流形的拓扑学和配边理论。证明使用示性类的形式性质，依赖于流形的可微结构和复结构。

**Grothendieck 的方法**：基于代数几何的 K-理论和 Chow 环。证明是纯代数的，适用于任意代数闭域上的拟射影簇。

**比较**：

1. **适用范围**：Grothendieck 的方法更广泛。Hirzebruch 的 HRR 需要复结构，而 GRR 适用于任意特征（包括特征 $p > 0$）。

2. **相对性**：Grothendieck 的 GRR 是相对的，蕴含了族的 Riemann-Roch（即参数空间上的等式）。Hirzebruch 的 HRR 是绝对的。

3. **计算性**：Hirzebruch 的方法在计算拓扑示性类时更直接。Grothendieck 的方法需要 Chow 环的计算，这在具体例子中可能非常复杂。

4. **形式化**：Grothendieck 的方法更适合形式化，因为它完全代数化。Hirzebruch 的方法需要微分拓扑的基础，这在当前证明辅助器中尚未系统发展。

### 6.2 Serre 与 Borel-Serre 论文

Serre 在 GRR 定理的发展中扮演了独特的角色。一方面，他与 Borel 合作完成了 GRR 的第一个完整证明；另一方面，他对 K-理论的某些方面持保留态度。

在 Borel-Serre 论文中，GRR 的证明使用了**Hirzebruch 的示性类理论**作为输入，然后通过代数几何的技术（闭浸入的分解、射影丛公式）将其推广。这一混合方法后来被 Grothendieck 在 SGA 6 中纯化为完全的代数框架。

### 6.3 SGA 6 与后续发展

SGA 6 将 GRR 定理纳入了**相交理论**的宏大框架。Fulton 在 1984 年的《Intersection Theory》中进一步发展了这一理论，引入了**Fulton 的 Chern 类**（适用于任意概形上的向量丛，不依赖于 Chow 环），以及**Fulton 的 GRR**（对任意 perfect 复形成立）。

后续的**高阶 K-理论**（Quillen, 1973）将 $K_0$ 推广到了 $K_n$（$n \geq 0$），并建立了**高阶 GRR**，涉及**Beilinson 调节子（regulator）**和**Arakelov 几何**。这些发展表明，Grothendieck 的原始框架只是更大图景的一部分。

### 6.4 形式化的挑战

GRR 定理的完整形式化是极其困难的，原因包括：

1. **Chow 环的构造**：Chow 群 $A^i(X)$ 的定义涉及代数闭链的有理等价，这在类型论中需要商类型的复杂处理；
2. **proper 推前的定义**：$f_*: A(X) \to A(Y)$ 的定义依赖于 cycles 的 pushforward，需要证明它与有理等价相容；
3. **陈类的分裂原理**：分裂原理需要 flag bundle 的构造，这在形式化中涉及大量的代数几何基础；
4. **$K$-理论的性质**：$K_0(X)$ 的万有性质和 $\lambda$-环结构需要精细的范畴论处理。

目前 Mathlib4 中尚未建立 Chow 环或 $K$-理论的系统形式化。Stacks Project 的相关内容（Tag 02UK 及后续）可作为形式化的路线图。

---

## 7. 参考文献与延伸阅读

### 原始文献

1. Borel, A. & Serre, J.-P. *Le théorème de Riemann-Roch*, *Bull. Soc. Math. France* **86** (1958), 97–136.
2. Grothendieck, A. *La théorie des classes de Chern*, *Bull. Soc. Math. France* **86** (1958), 137–154.
3. Berthelot, P., Grothendieck, A., Illusie, L. et al. *SGA 6: Théorie des intersections et théorème de Riemann-Roch*, LNM 225, Springer, 1971.

### 教材与专著

1. Fulton, W. *Intersection Theory*, 2nd ed., Springer, 1998.
2. Fulton, W. & Lang, S. *Riemann-Roch Algebra*, Springer, 1985.
3. Hirzebruch, F. *Topological Methods in Algebraic Geometry*, Springer, 1966.

### 数据库

1. Stacks Project, Tag 02UK: *Riemann-Roch*. https://stacks.math.columbia.edu/tag/02UK
2. nLab: *Grothendieck-Riemann-Roch theorem*. https://ncatlab.org/nlab/show/Grothendieck-Riemann-Roch+theorem

---

> **审校状态**：草稿（draft）。GRR 的完整形式化需要 Chow 环和 K-理论的系统开发，目前 Mathlib4 中尚未就绪。
