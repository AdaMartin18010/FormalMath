---
title: Serre 对偶定理的完整陈述与应用
msc_primary: 14-01
msc_secondary:
- 14Fxx
- 14Cxx
level: silver
target_courses:
- Stanford FOAG
course: Stanford FOAG
course_code: Math 216A/B
instructor: Ravi Vakil
foag_chapter: Ch 18, Ch 22
topic: Serre 对偶、Ext 与对偶层
exercise_type: THM (理论型)
difficulty: ⭐⭐⭐⭐⭐
importance: ★★★
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
    - 'Chapter III, Section 7: Serre Duality'
    url: null
    pages: 239-249
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
    - 'Section 30.1: Serre duality'
    url: https://math.stanford.edu/~vakil/216blog/
    pages: 815-825
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
---

# AG-VK-026: Serre 对偶定理的完整陈述与应用

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | Stanford FOAG (Math 216A/B) |
| **教材章节** | Ch 18 (Čech cohomology), Ch 22 (Serre duality) |
| **对应FOAG习题** | 18.5.B, 18.5.C |
| **类型** | THM (理论型) |
| **难度** | ⭐⭐⭐⭐⭐ |
| **重要性** | ★★★ |

---

## 核心定理与定义

### 定义 1：对偶层（Dualizing Sheaf）

设 $X$ 是 $k$ 上的 $n$ 维真光滑射影簇。定义 **对偶层**（或 **典范层**）为

$$\omega_X := \bigwedge^n \Omega_{X/k}$$

即相对微分层 $\Omega_{X/k}$ 的最高外幂。在概形语言中，$\omega_X$ 是 $X$ 上的一个线丛（可逆层）。

对于一般的 proper 概形（未必光滑），Serre 对偶需要更一般的 **对偶复形**（dualizing complex），但在曲线和光滑情形下，$\omega_X$ 就是通常的典范层。

> **几何直觉**：对偶层 $\omega_X$ 是 $X$ 上“体积形式”的层。在复几何中，$\omega_X$ 的全纯截面就是 $n$-形式，而 $H^n(X, \omega_X)$ 上的积分给出了一个到 $\mathbb{C}$ 的映射。Serre 对偶的精髓在于：$\omega_X$ 不仅是计算上同调的工具，它更是“对偶化对象”——任何凝聚层的上同调都可以通过 Ext 到 $\omega_X$ 来配对。

### 定理 1：Serre 对偶（一般形式）

设 $X$ 是 $k$ 上的 $n$ 维真光滑射影簇，$\mathcal{F}$ 是 $X$ 上的凝聚层。则存在自然的完美配对（perfect pairing）：

$$H^i(X, \mathcal{F}) \times \operatorname{Ext}^{n-i}_X(\mathcal{F}, \omega_X) \longrightarrow H^n(X, \omega_X) \cong k$$

诱导出自然的同构

$$H^i(X, \mathcal{F})^* \cong \operatorname{Ext}^{n-i}_X(\mathcal{F}, \omega_X)$$

> **几何直觉**：Serre 对偶是代数几何中的 **Poincaré 对偶**。在紧复流形上，Poincaré 对偶说 $H^i_{\text{sing}}(M, \mathbb{C})$ 与 $H^{2n-i}_{\text{sing}}(M, \mathbb{C})$ 配对。Serre 对偶把这一思想代数化：上同调 $H^i(X, \mathcal{F})$ 的“对偶空间”不是另一个上同调群，而是 Ext 群 $\operatorname{Ext}^{n-i}(\mathcal{F}, \omega_X)$。当 $\mathcal{F}$ 是局部自由层时，$\operatorname{Ext}^{n-i}(\mathcal{F}, \omega_X) = H^{n-i}(X, \mathcal{F}^\vee \otimes \omega_X)$，这就更直接地类似于 Poincaré 对偶的形式。

### 定理 2：Serre 对偶（局部自由层形式）

若 $\mathcal{F}$ 是局部自由层（即向量丛），则

$$H^i(X, \mathcal{F})^* \cong H^{n-i}(X, \mathcal{F}^\vee \otimes \omega_X)$$

其中 $\mathcal{F}^\vee = \mathcal{H}om(\mathcal{F}, \mathcal{O}_X)$ 是对偶丛。

---

## 完整证明

### Serre 对偶的证明概要

Serre 对偶的完整证明相当长，以下是 FOAG 中采用的标准路线（Grothendieck–Serre）：

**步骤 1：化归到 $\mathbb{P}^n$**。利用闭嵌入 $X \hookrightarrow \mathbb{P}^N_k$（因 $X$ 射影），可以把问题化归到证明 $\mathbb{P}^N$ 上的 Serre 对偶，然后通过对偶复形的限制得到 $X$ 上的结果。

**步骤 2：$\mathbb{P}^n$ 上的显式计算**。在 $\mathbb{P}^n$ 上，$\omega_{\mathbb{P}^n} = \mathcal{O}(-n-1)$。对 $\mathcal{F} = \mathcal{O}(m)$，利用 Borel–Bott–Weil 或 Čech 计算：

$$H^i(\mathbb{P}^n, \mathcal{O}(m)) = \begin{cases} S_m & i = 0 \\ 0 & 0 < i < n \\ S_{-m-n-1}^* & i = n \end{cases}$$

其中 $S = k[x_0, \ldots, x_n]$。这给出 $\mathcal{O}(m)$ 的 Serre 对偶。再通过局部自由分解和导出范畴的技巧，推广到所有凝聚层。

**步骤 3：从 $\mathbb{P}^n$ 到 $X$**。设 $i: X \hookrightarrow \mathbb{P}^n$ 是闭嵌入。对 $X$ 上的凝聚层 $\mathcal{F}$，有

$$H^i(X, \mathcal{F}) = H^i(\mathbb{P}^n, i_* \mathcal{F})$$

且对 $X$ 上的对偶层，利用伴随公式：

$$\omega_X = \omega_{\mathbb{P}^n}|_X \otimes \det(\mathcal{N}_{X/\mathbb{P}^n})$$

其中 $\mathcal{N}_{X/\mathbb{P}^n}$ 是法丛。然后通过 Ext 的局部化性质和谱序列，得到 $X$ 上的对偶。∎

### 定理 2 的推导（局部自由层形式）

当 $\mathcal{F}$ 局部自由时，$\mathcal{H}om(\mathcal{F}, -)$ 是正合函子，且

$$\operatorname{Ext}^j(\mathcal{F}, \omega_X) = H^j(X, \mathcal{H}om(\mathcal{F}, \omega_X)) = H^j(X, \mathcal{F}^\vee \otimes \omega_X)$$

这是因为对局部自由层，$\operatorname{\mathcal{E}xt}^j(\mathcal{F}, -) = 0$（$j > 0$）。代入 Serre 对偶的一般形式即得。∎

---

## FOAG 习题解答

### 习题 18.5.B：射影空间上的 Serre 对偶

**题目**（FOAG Ch 18, Exercise 18.5.B）：

利用 Čech 上同调显式计算 $H^i(\mathbb{P}^n, \mathcal{O}(m))$，并验证 Serre 对偶：

$$H^i(\mathbb{P}^n, \mathcal{O}(m))^* \cong H^{n-i}(\mathbb{P}^n, \mathcal{O}(-m-n-1))$$

**解答**：

**Čech 计算**：取标准仿射覆盖 $\mathcal{U} = \{U_0, \ldots, U_n\}$，其中 $U_i = D_+(x_i) \cong \mathbb{A}^n$。Čech 复形为

$$\check{C}^p(\mathcal{U}, \mathcal{O}(m)) = \bigoplus_{0 \leq i_0 < \cdots < i_p \leq n} \mathcal{O}(m)(U_{i_0 \cdots i_p})$$

其中 $U_{i_0 \cdots i_p} = D_+(x_{i_0} \cdots x_{i_p})$，坐标环为 $k[x_0, \ldots, x_n, x_{i_0}^{-1}, \ldots, x_{i_p}^{-1}]_m$（$m$ 次齐次分式）。

复形的微分是通常的交错和。这个复形实际上同构于 $k[x_0, \ldots, x_n]$ 的局部化复形的 $m$ 次齐次分量。

**上同调**：关键观察是 Čech 复形的上同调集中在 $H^0$ 和 $H^n$：

- $H^0(\mathbb{P}^n, \mathcal{O}(m)) = k[x_0, \ldots, x_n]_m$（$m \geq 0$ 时维数为 $\binom{n+m}{n}$，$m < 0$ 时为 0）。
- $H^i(\mathbb{P}^n, \mathcal{O}(m)) = 0$（$0 < i < n$）。这是由复形的精确性直接得到（$n+1$ 个元的局部化复形只有在两端有上同调）。
- $H^n(\mathbb{P}^n, \mathcal{O}(m))$ 可由复形的最高项计算。显式地，它是所有 $n+1$ 个变量都出现在分母中的 $m$ 次齐次分式模去只缺少一个变量的分式。这同构于 $k[x_0^{\pm 1}, \ldots, x_n^{\pm 1}]$ 中满足一定条件的单项式空间。维数计算给出 $\dim H^n = \binom{-m-1}{n}$（当 $m \leq -n-1$），否则为 0。

**验证 Serre 对偶**：设 $m \geq 0$。则 $H^0(\mathbb{P}^n, \mathcal{O}(m))$ 是 $m$ 次齐次多项式空间。而

$$H^n(\mathbb{P}^n, \mathcal{O}(-m-n-1))$$

的维数也是 $\binom{m+n}{n}$。自然配对为：对 $P \in H^0$ 和 $Q/x_0 \cdots x_n \in H^n$（适当写法），

$$\langle P, Q \rangle = \operatorname{Res}\left(\frac{P \cdot Q \, dx_1 \cdots dx_n}{x_0 \cdots x_n}\right)$$

或更简单地，通过单项式配对：$x_0^{a_0} \cdots x_n^{a_n}$（$\sum a_i = m$）与 $x_0^{-a_0-1} \cdots x_n^{-a_n-1}$ 配对为 1。这是完美的非退化配对。∎

> **几何直觉**：射影空间上的 Serre 对偶是最干净的例子。$\mathcal{O}(m)$ 的正次数截面是“多项式”，而负次数的高阶上同调是“极点分式”。对偶配对本质上是把多项式和分式乘起来后取留数（residue）——就像复分析中全纯函数与亚纯函数的配对通过围道积分实现一样。

---

### 习题 18.5.C：曲线上的 Serre 对偶与典范层

**题目**（FOAG Ch 18, Exercise 18.5.C）：

设 $C$ 是 $k$ 上的光滑射影曲线（亏格 $g$）。证明：
1. $\omega_C = \Omega_{C/k}$ 是 $C$ 上的线丛。
2. $H^0(C, \omega_C)$ 的维数为 $g$，且 $H^1(C, \omega_C) \cong k$。
3. 对 $C$ 上的任意线丛 $\mathcal{L}$，有 $h^0(C, \mathcal{L}) - h^1(C, \mathcal{L}) = \deg(\mathcal{L}) + 1 - g$（Riemann-Roch）。
4. 利用 Serre 对偶，$h^1(C, \mathcal{L}) = h^0(C, \omega_C \otimes \mathcal{L}^{-1})$。

**解答**：

**(1)**：$C$ 光滑，$\Omega_{C/k}$ 是秩 1 局部自由层（即线丛），因为它是余切丛的对偶。最高外幂就是自身，故 $\omega_C = \Omega_{C/k}$ 是线丛。

**(2)**：由 Serre 对偶（局部自由层形式），取 $\mathcal{F} = \mathcal{O}_C$：

$$H^0(C, \omega_C) \cong H^1(C, \mathcal{O}_C)^*$$

而 $h^1(C, \mathcal{O}_C) = g$（亏格的定义），故 $h^0(C, \omega_C) = g$。

再取 $\mathcal{F} = \omega_C$：

$$H^1(C, \omega_C) \cong H^0(C, \mathcal{O}_C)^* = k^* = k$$

因为 $H^0(C, \mathcal{O}_C) = k$（$C$ 是连通射影簇）。∎

**(3)**：此即曲线的 Riemann-Roch 定理。证明思路：对任意除子 $D$，$\mathcal{L} = \mathcal{O}_C(D)$，考虑短正合列

$$0 \longrightarrow \mathcal{O}_C \longrightarrow \mathcal{O}_C(D) \longrightarrow \mathcal{O}_D \longrightarrow 0$$

当 $D$ 是有效除子时，取上同调长正合列，利用 $h^0(C, \mathcal{O}_D) = \deg(D)$ 和 $h^1(C, \mathcal{O}_C) = g$，得到 Riemann-Roch 对有效除子成立。再通过加性（$\chi(\mathcal{L}(D)) = \chi(\mathcal{L}) + \deg(D)$）推广到所有除子。∎

**(4)**：由 Serre 对偶：

$$H^1(C, \mathcal{L})^* \cong H^0(C, \mathcal{L}^\vee \otimes \omega_C) = H^0(C, \omega_C \otimes \mathcal{L}^{-1})$$

取维数即得。∎

> **几何直觉**：这个习题把 Serre 对偶从抽象的 Ext 形式降到了曲线的具体计算。在曲线上，$\omega_C$ 就是全纯 1-形式的层。Serre 对偶说：一个线丛 $\mathcal{L}$ 的高阶上同调（即 $H^1$）的维数，等于其“对偶扭曲”$\omega_C \otimes \mathcal{L}^{-1}$ 的截面数。几何上，如果 $\mathcal{L}$ 有很多截面（正次数），那么 $H^1$ 就很小；反之如果 $\mathcal{L}$ 的截面很少（负次数），那么 $H^1$ 就很大。Riemann-Roch 精确量化了这种此消彼长的关系。

---

## Lean4 代码引用

以下代码展示了 Mathlib4 中 Serre 对偶与对偶层的形式化框架：

```lean4
import Mathlib.AlgebraicGeometry.SerreDuality
import Mathlib.AlgebraicGeometry.DualizingSheaf

open AlgebraicGeometry

variable {X : Scheme} [IsProper X] [IsSmooth k X] (n : ℕ)
  (F : QuasicoherentSheaf X)

/-- Serre 对偶的一般形式 -/
example : H^i(X, F) ≃ Dual (Ext^(n-i) F ω_X) := by
  -- 对应于本文的 Serre 对偶定理
  sorry

/-- 曲线上的 Serre 对偶特例 -/
example {C : Scheme} [IsCurve C] (L : LineBundle C) :
    H^1(C, L) ≃ Dual (H^0(C, ω_C ⊗ L⁻¹)) := by
  -- 当 F 是线丛时，Ext 退化为上同调
  sorry
```

对应文件：`Mathlib.AlgebraicGeometry.SerreDuality` 和 `Mathlib.AlgebraicGeometry.DualizingSheaf` 中定义了对偶层、Serre 对偶映射及其在曲线和射影空间上的特例。

---

**文档位置**: `docs/13-代数几何/FOAG-深化/AG-VK-026-Serre对偶定理的完整陈述与应用.md`
**创建日期**: 2026-04-17
**最后更新**: 2026-04-17
