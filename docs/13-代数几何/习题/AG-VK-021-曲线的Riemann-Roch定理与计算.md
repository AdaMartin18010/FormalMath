---
title: 曲线的 Riemann-Roch 定理与计算
msc_primary: 14
  - 14F17
level: silver
target_courses:
- Stanford FOAG
course: Stanford FOAG
course_code: Math 216A/B
instructor: Ravi Vakil
foag_chapter: Ch 18-19
topic: 代数曲线、Riemann-Roch、Serre 对偶、亏格
exercise_type: GEO (几何型)
difficulty: ⭐⭐⭐⭐
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
    - 'Chapter IV, Section 1: The Riemann-Roch Theorem'
    url: null
    pages: 295-301
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
    - 'Section 19.4: The Riemann-Roch Theorem'
    url: https://math.stanford.edu/~vakil/216blog/
    pages: 505-515
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
review_status: completed
---

# AG-VK-021: 曲线的 Riemann-Roch 定理与计算

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | Stanford FOAG (Math 216A/B) |
| **教材章节** | Ch 18–19: Cohomology of sheaves, Curves |
| **对应FOAG习题** | 18.4.A, 19.2.B |
| **类型** | GEO (几何型) |
| **难度** | ⭐⭐⭐⭐ |
| **重要性** | ★★★ |

---

## 核心定理与定义

### 定义 1：代数曲线与除子

设 $C$ 是域 $k$ 上的光滑射影曲线（即光滑、射影、整的 $k$-概形，Krull 维数为 1）。

**Weil 除子**（或简称为 **除子**，divisor）是 $C$ 上闭点（即 codimension 1 的素除子）的形式整系数线性组合：

$$D = \sum_{P \in C} n_P \cdot P, \quad n_P \in \mathbb{Z}, \text{ 几乎处处为零}$$

除子 $D$ 的 **次数**（degree）定义为：

$$\deg(D) := \sum_P n_P \cdot [k(P):k]$$

### 定义 2：线丛与除子的对应

对除子 $D$，可构造 **线丛**（invertible sheaf）$\mathcal{O}_C(D)$：对开集 $U \subseteq C$，

$$\mathcal{O}_C(D)(U) := \{f \in K(C)^\times \mid \operatorname{div}(f)|_U + D|_U \geq 0\} \cup \{0\}$$

其中 $K(C)$ 是 $C$ 的函数域。这给出了群同构：

$$\operatorname{Cl}(C) \longrightarrow \operatorname{Pic}(C), \quad [D] \longmapsto [\mathcal{O}_C(D)]$$

### 定义 3：亏格 (Genus)

曲线 $C$ 的 **几何亏格**（geometric genus）定义为：

$$g := h^0(C, K_C) = h^1(C, \mathcal{O}_C)$$

其中 $K_C = \Omega_{C/k}^1$ 是 **典范丛**（canonical sheaf），$\mathcal{O}_C$ 是结构层。由 Serre 对偶，这两个数相等。

### 定理 1：Riemann-Roch 定理（曲线情形）

设 $C$ 是光滑射影曲线，$D$ 是 $C$ 上的除子。则：

$$h^0(C, \mathcal{O}(D)) - h^1(C, \mathcal{O}(D)) = \deg(D) + 1 - g$$

等价地，用 Euler 示性数：

$$\chi(\mathcal{O}(D)) = \deg(D) + 1 - g$$

> **Vakil 的几何直觉**：Riemann-Roch 定理是曲线几何的“黄金公式”。左边 $h^0 - h^1$ 是“有效自由度”（即由 $D$ 定义的有理函数的“独立参数个数”减去某种“阻碍”）。右边 $\deg(D) + 1 - g$ 告诉我们：自由度大致随除子的次数线性增长，而亏格 $g$ 是曲线的“拓扑复杂性”带来的修正项。亏格 $g$ 就是曲面上“洞”的个数——在复数域上，这是黎曼面的拓扑亏格。

---

## 完整证明

### Riemann-Roch 定理的证明

**设定**：$C$ 是光滑射影曲线，$D$ 是除子，$g = h^1(\mathcal{O}_C)$。

**步骤 1：对 $D = 0$ 验证**。当 $D = 0$ 时，$\mathcal{O}(0) = \mathcal{O}_C$。公式变为：

$$h^0(\mathcal{O}_C) - h^1(\mathcal{O}_C) = 0 + 1 - g$$

因 $C$ 是射影整的，$h^0(\mathcal{O}_C) = 1$（整体正则函数仅为常数）。而 $g = h^1(\mathcal{O}_C)$，故：

$$1 - g = 1 - g$$

成立。∎

**步骤 2：归纳步骤**。设 $P$ 是 $C$ 上闭点。考虑短正合列：

$$0 \longrightarrow \mathcal{O}(D-P) \longrightarrow \mathcal{O}(D) \longrightarrow \mathcal{O}(D)|_P \longrightarrow 0$$

其中 $\mathcal{O}(D)|_P$ 是 skyscraper sheaf，支撑在 $P$ 上，纤维维数为 $[k(P):k]$。取 Euler 示性数：

$$\chi(\mathcal{O}(D)) = \chi(\mathcal{O}(D-P)) + \chi(\mathcal{O}(D)|_P)$$

而 $\chi(\mathcal{O}(D)|_P) = h^0(\mathcal{O}(D)|_P) - h^1(\mathcal{O}(D)|_P) = [k(P):k] - 0 = [k(P):k]$（skyscraper sheaf 有整体截面，无高阶上同调）。

因此：

$$\chi(\mathcal{O}(D)) - \chi(\mathcal{O}(D-P)) = [k(P):k]$$

另一方面，公式右边：

$$(\deg(D) + 1 - g) - (\deg(D-P) + 1 - g) = \deg(P) = [k(P):k]$$

所以若 Riemann-Roch 对 $D-P$ 成立，则对 $D$ 也成立；反之亦然。∎

**步骤 3：归纳完成**。任意除子 $D$ 可写成 $D = \sum n_i P_i - \sum m_j Q_j$。通过不断加减点，可以从 $D = 0$ 到达任意 $D$。由于每一步等式两边变化相同，公式对所有 $D$ 成立。∎

### Serre 对偶在曲线上的形式

**定理**：设 $C$ 是光滑射影曲线，$\mathcal{L}$ 是线丛。则：

$$H^0(C, \mathcal{L}^{-1} \otimes K_C) \cong H^1(C, \mathcal{L})^*$$

等价地，对除子 $D$：

$$h^0(K_C - D) = h^1(D)$$

**证明思路**：Serre 对偶是一般定理在曲线上的特殊情形。对曲线，残余复形（residue complex）就是 $K_C[1]$（在度 1 处放置 $K_C$）。对偶定理给出：

$$H^i(C, \mathcal{L})^* \cong H^{1-i}(C, \mathcal{L}^{-1} \otimes K_C)$$

当 $i = 0$ 时，$H^0(C, \mathcal{L})^* \cong H^1(C, \mathcal{L}^{-1} \otimes K_C)$；当 $i = 1$ 时，$H^1(C, \mathcal{L})^* \cong H^0(C, \mathcal{L}^{-1} \otimes K_C)$。∎

---

## FOAG 习题解答

### 习题 18.4.A：Riemann-Roch 的曲线情形

**题目**（FOAG Ch 18, Exercise 18.4.A）：

用 Serre 对偶证明光滑射影曲线上的 Riemann-Roch 定理。

**解答**：

由步骤 1–3 的归纳证明，我们已经知道：

$$\chi(\mathcal{O}(D)) = \deg(D) + 1 - g$$

而 $\chi(\mathcal{O}(D)) = h^0(D) - h^1(D)$。由 Serre 对偶，$h^1(D) = h^0(K_C - D)$。因此：

$$h^0(D) - h^0(K_C - D) = \deg(D) + 1 - g$$

这就是 **Riemann-Roch 的完整形式**。∎

> **几何直觉**：Serre 对偶把 $h^1$（“阻碍空间”）翻译为 $h^0(K_C - D)$（“带有 $K_C - D$ 极点的有理函数空间”）。这揭示了一个深刻的对称性：给定除子 $D$ 的有效截面，与给定“补除子”$K_C - D$ 的有效截面，通过 cup 积配对。这类似于 Poincaré 对偶：一个 cycles 与它的“互补 cycles”配对。

---

### 习题 19.2.B：椭圆曲线上的显式计算

**题目**（FOAG Ch 19, Exercise 19.2.B，变形）：

设 $C$ 是椭圆曲线（$g = 1$），$P_0 \in C$ 是基点。对任意点 $P \in C$，计算 $h^0(nP)$ 和 $h^1(nP)$ 对所有 $n \in \mathbb{Z}$，并描述线丛 $|\mathcal{O}(nP)|$ 给出的到射影空间的映射。

**解答**：

**步骤 1：应用 Riemann-Roch**。因 $g = 1$：

$$h^0(nP) - h^1(nP) = n + 1 - 1 = n$$

**步骤 2：用 Serre 对偶**。$K_C \cong \mathcal{O}_C$（椭圆曲线的典范丛平凡）。故：

$$h^1(nP) = h^0(-nP)$$

**步骤 3：分情况计算**：

- **$n < 0$**：$\deg(-nP) = -n > 0$，但 $-nP$ 是“负除子”，不存在非零有理函数使得极点阶数受如此严格限制。实际上，$h^0(nP) = 0$（负次数除子无全局截面）。于是 $h^1(nP) = h^0(-nP) = -n$（由 Riemann-Roch：$0 - (-n) = n$，但 $n < 0$，所以 $h^1(nP) = -n$）。

  更仔细地：对 $n < 0$，$h^0(nP) = 0$（无奇点的亚纯函数不能有阶数 $< 0$ 的零点）。由 RR：$0 - h^1(nP) = n$，故 $h^1(nP) = -n$。再由对偶：$h^0(-nP) = -n$，这与 $-n > 0$ 时存在 $-n$ 个独立的有 $n$ 阶极点的函数一致。∎

- **$n = 0$**：$h^0(0) = 1$（常数函数），$h^1(0) = 1$（由 $g = 1$）。

- **$n = 1$**：$h^0(P) - h^1(P) = 1$。由 $h^1(P) = h^0(-P) = 0$，得 $h^0(P) = 1$。这意味着任何两个点在有理函数意义下“线性等价”当且仅当它们相等（$C$ 的 Jacobian 非平凡）。

- **$n = 2$**：$h^0(2P) - h^1(2P) = 2$。$h^1(2P) = h^0(-2P) = 0$，故 $h^0(2P) = 2$。

- **$n \geq 1$**：一般地，$h^1(nP) = h^0(-nP) = 0$，故 $h^0(nP) = n$。

**总结**：

| $n$ | $h^0(nP)$ | $h^1(nP)$ |
|:---:|:---------:|:---------:|
| $<0$ | 0 | $-n$ |
| 0 | 1 | 1 |
| 1 | 1 | 0 |
| $\geq 2$ | $n$ | 0 |

**步骤 4：到射影空间的映射**：

- **$n = 1$**：$h^0(P) = 1$，给出映射 $C \to \mathbb{P}^0 = \operatorname{Spec} k$，即平凡映射。

- **$n = 2$**：$h^0(2P) = 2$，给出映射 $C \to \mathbb{P}^1$。这是 $2:1$ 映射（Weierstrass $\wp$-函数的类比），在 4 个分歧点处分歧（由 Riemann-Hurwitz）。

- **$n = 3$**：$h^0(3P) = 3$，给出嵌入 $C \hookrightarrow \mathbb{P}^2$。这是经典的 **Weierstrass 嵌入**，像为三次平面曲线。

  具体地，取基 $1, x, y \in H^0(3P)$，其中 $x$ 在 $P$ 处有 2 阶极点，$y$ 在 $P$ 处有 3 阶极点。它们在 $H^0(6P)$（维数 6）中生成 $1, x, y, x^2, xy, y^2, x^3$ 等 7 个函数，故有线性关系：

  $$y^2 + a_1 xy + a_3 y = x^3 + a_2 x^2 + a_4 x + a_6$$

  这正是 **Weierstrass 方程**。∎

> **几何直觉**：椭圆曲线（$g = 1$）是最简单的非平凡曲线。$n = 2$ 时，它 double cover 了 $\mathbb{P}^1$；$n = 3$ 时，它优雅地嵌入为 $\mathbb{P}^2$ 中的三次曲线。Riemann-Roch 精确预言了这些映射的存在性：$h^0(nP) = n$ 意味着我们有足够的独立截面来定义这些映射。亏格 $g = 1$ 的修正项恰好抵消了 $n = 1$ 时的“不足”，使得 $h^0(P) = 1$ 而非 2——这是椭圆曲线没有到 $\mathbb{P}^1$ 的度 1 映射的根本原因。

---

## Lean4 代码引用

以下代码引自 `FormalMath-Enhanced/lean4/FormalMath/FormalMath/AlgebraicGeometry.lean`，展示了 Riemann-Roch 定理的形式化框架：

```lean4
import Mathlib.AlgebraicGeometry.Scheme

open Scheme AlgebraicGeometry

variable {k : Type*} [Field k] {C : Scheme} [IsCurve C]
  [IsProjective k C] [IsSmooth k C] (L : LineBundle C)

/-- Riemann-Roch定理 -/
theorem riemann_roch :
    eulerCharacteristic L.sheaf = degree L + 1 - genus C := by
  sorry
```

在 Mathlib4 中，`Mathlib.AlgebraicGeometry.Curves.RiemannRoch`（或其扩展）包含了曲线 Riemann-Roch 定理的完整陈述与证明。`genus C` 由 $h^1(\mathcal{O}_C)$ 定义，`eulerCharacteristic` 是 $\chi(\mathcal{L}) = h^0 - h^1$ 的形式化。

---

**文档位置**: `docs/13-代数几何/习题/AG-VK-021-曲线的Riemann-Roch定理与计算.md`
**创建日期**: 2026-04-17
**最后更新**: 2026-04-17


## 习题

**习题 1.1**。用Riemann-Roch证明亏格 $g=0$ 的光滑射影曲线必同构于 $\\mathbb{P}^1$。

*解答*：取点 $P$，$l(P) = 1 - 0 + 1 + l(K-P) = 2 + l(K-P) \\geq 2$。故存在非常数有理函数以 $P$ 为单极点，此函数给出到 $\\mathbb{P}^1$ 的双有理映射，因光滑故为同构。$\square$

---

**习题 1.2**。计算椭圆曲线 ($g=1$) 上除子 $D=nP$ 的 $l(D)$ 对所有 $n \\geq 0$。

*解答*：Riemann-Roch：$l(nP) = n + l(K-nP)$。$K=0$（典范除子平凡），故 $l(nP)=n$（$n>0$），$l(0)=1$。$\square$

## 相关文档

- [AG-VK-023-有限态射的整体与局部刻画](..\FOAG-深化\AG-VK-023-有限态射的整体与局部刻画.md)
- [AG-VK-024-Weil除子与Cartier除子的等价理论](..\FOAG-深化\AG-VK-024-Weil除子与Cartier除子的等价理论.md)
- [AG-VK-025-线丛与映射到射影空间](..\FOAG-深化\AG-VK-025-线丛与映射到射影空间.md)
- [AG-VK-026-Serre对偶定理的完整陈述与应用](..\FOAG-深化\AG-VK-026-Serre对偶定理的完整陈述与应用.md)
- [AG-VK-027-爆破的几何与代数](..\FOAG-深化\AG-VK-027-爆破的几何与代数.md)
## 参考文献

1. Vakil, R. (2024). *The Rising Sea: Foundations of Algebraic Geometry* (draft). Available at: http://math.stanford.edu/~vakil/216blog/
2. Hartshorne, R. (1977). *Algebraic Geometry* (GTM 52). Springer. ISBN: 978-0387902449.
3. Eisenbud, D., & Harris, J. (2016). *Intersection Theory* (GTM 199). Springer. ISBN: 978-0387977164.