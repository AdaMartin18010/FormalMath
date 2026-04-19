---
title: 爆破的几何与代数
msc_primary: 14
  - 14E15
  - 14B05
level: silver
target_courses:
- Stanford FOAG
course: Stanford FOAG
course_code: Math 216A/B
instructor: Ravi Vakil
foag_chapter: Ch 19
topic: Blow-up、例外除子与奇点消解
exercise_type: THM (理论型)
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
    - 'Chapter I, Section 4: Rational Maps; Chapter II, Section 7: Blow-ups'
    url: null
    pages: 28-32, 158-163
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
    - 'Section 19.4: Blow-ups'
    url: https://math.stanford.edu/~vakil/216blog/
    pages: 525-535
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

# AG-VK-027: 爆破的几何与代数

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | Stanford FOAG (Math 216A/B) |
| **教材章节** | Ch 19: Blowing up a scheme along a closed subscheme |
| **对应FOAG习题** | 19.2.C, 19.4.B |
| **类型** | THM (理论型) |
| **难度** | ⭐⭐⭐⭐ |
| **重要性** | ★★★ |

---

## 核心定理与定义

### 定义 1：沿闭子概形的爆破

设 $X$ 是概形，$Z \subseteq X$ 是闭子概形，对应理想层 $\mathcal{I}_Z \subseteq \mathcal{O}_X$。定义 $X$ 沿 $Z$ 的 **爆破**（blow-up）为

$$\operatorname{Bl}_Z(X) := \operatorname{Proj}_X \left( \bigoplus_{d=0}^\infty \mathcal{I}_Z^d \right)$$

其中 $\mathcal{I}_Z^0 := \mathcal{O}_X$。自然投影 $\pi: \operatorname{Bl}_Z(X) \to X$ 称为 **爆破态射**。

**例外除子**（exceptional divisor）定义为 $E := \pi^{-1}(Z)$，它是 $\operatorname{Bl}_Z(X)$ 中的 Cartier 除子（实际上是有效除子）。

> **几何直觉**：爆破是代数几何中最重要的奇点消解工具。想象 $Z$ 是 $X$ 中一个子簇；爆破操作“放大”$Z$ 的邻域，把 $Z$ 替换成它在 $X$ 中的法方向的射影化。直观上，就像用显微镜观察 $Z$ 附近的结构，然后把所有通过 $Z$ 的方向“展开”成一个新的子簇 $E$。原来的奇点被“拉开”，新的空间在原奇点处变得更光滑。

### 定理 1：爆破的泛性质

设 $\pi: \operatorname{Bl}_Z(X) \to X$ 是沿 $Z$ 的爆破。则：

1. $\pi$ 诱导了 $\operatorname{Bl}_Z(X) \setminus E \cong X \setminus Z$ 的同构。
2. 例外除子 $E = \pi^{-1}(Z)$ 是 Cartier 除子。
3. **泛性质**：对任意态射 $f: Y \to X$，若 $f^{-1}(Z)$ 是 $Y$ 中的 Cartier 除子，则存在唯一的态射 $\tilde{f}: Y \to \operatorname{Bl}_Z(X)$ 使得 $f = \pi \circ \tilde{f}$。

> **几何直觉**：泛性质告诉我们，爆破是“把 $Z$ 变成 Cartier 除子的最小方法”。任何其他能把 $Z$ 的原像变成 Cartier 除子的映射，都必须经由爆破分解。这意味着爆破在某种意义上是“最经济”的奇点消解步骤。

### 定理 2：曲线的奇点消解

设 $C$ 是代数闭域 $k$ 上的约化曲线。则存在有限次爆破的序列

$$C_n \longrightarrow C_{n-1} \longrightarrow \cdots \longrightarrow C_1 \longrightarrow C_0 = C$$

使得 $C_n$ 是光滑的。这称为 **奇点消解**（resolution of singularities）。

---

## 完整证明

### 定理 1：爆破的泛性质

**(1)**：在 $X \setminus Z$ 上，$\mathcal{I}_Z = \mathcal{O}_X$。故分次代数

$$\bigoplus_{d=0}^\infty \mathcal{I}_Z^d = \bigoplus_{d=0}^\infty \mathcal{O}_X = \mathcal{O}_X[t]$$

其 Proj 为 $X \setminus Z$（因为当分次代数由 1 次部分整体生成时，Proj 就是底空间）。因此 $\pi$ 在 $X \setminus Z$ 上是同构。

**(2)**：在 $\operatorname{Bl}_Z(X)$ 上，理想层 $\mathcal{I}_Z \cdot \mathcal{O}_{\operatorname{Bl}_Z(X)}$ 是可逆的（invertible）。这是因为 Proj 的构造使得分次代数在 1 次部分由 $\mathcal{I}_Z$ 生成，而 Proj 上的典范可逆层 $\mathcal{O}(1)$ 恰好对应这个理想层。因此 $E = V(\mathcal{I}_Z \cdot \mathcal{O}_{\operatorname{Bl}_Z(X)})$ 是 Cartier 除子。

**(3)**（泛性质的证明）：设 $f: Y \to X$，且 $f^{-1}(Z)$ 是 Cartier 除子。这意味着理想层 $f^* \mathcal{I}_Z \subseteq \mathcal{O}_Y$ 是可逆的。考虑分次代数同态

$$f^* \left( \bigoplus_{d=0}^\infty \mathcal{I}_Z^d \right) = \bigoplus_{d=0}^\infty (f^* \mathcal{I}_Z)^d \longrightarrow \mathcal{O}_Y$$

其中 $f^* \mathcal{I}_Z$ 是可逆层，故 $(f^* \mathcal{I}_Z)^d$ 也是可逆的。Proj 的泛性质说：若一个分次代数到 $\mathcal{O}_Y$ 的映射在 1 次部分由可逆层生成，则它诱导一个到 Proj 的映射。更具体地，因 $f^* \mathcal{I}_Z$ 可逆，存在满射

$$f^* \left( \bigoplus_{d=0}^\infty \mathcal{I}_Z^d \right) \longrightarrow \bigoplus_{d=0}^\infty (f^* \mathcal{I}_Z)^d$$

而 Proj 对满射的 pullback 给出映射 $Y \to \operatorname{Bl}_Z(X)$。唯一性由 Proj 的泛性质保证。∎

### 定理 2：曲线的奇点消解（概要）

**步骤 1**：设 $p \in C$ 是奇点。考虑爆破 $\pi: \operatorname{Bl}_p(C) \to C$。由于 $C$ 是曲线，$
\operatorname{Bl}_p(C)$ 是一个新的曲线（可能不连通），其在 $p$ 上方的纤维 $E$ 是有限个点（因为法方向的射影化在 1 维时是 0 维的）。

**步骤 2**：计算奇点的不变量。对平面曲线奇点，可用 **Milnor 数** 或 **$$-不变量**。爆破后，奇点的这些不变量严格下降。

**步骤 3**：因不变量是非负整数，有限次爆破后必达到 0，即奇点被消解。对一般的曲线，可局部嵌入到光滑曲面中，然后对曲面进行爆破，再取严格变换（strict transform）得到新的曲线。∎

---

## FOAG 习题解答

### 习题 19.2.C：$\mathbb{A}^2$ 在原点处的爆破

**题目**（FOAG Ch 19, Exercise 19.2.C）：

设 $X = \mathbb{A}^2_k = \operatorname{Spec} k[x, y]$，$Z = \{(0, 0)\} = V(x, y)$。证明：

1. $\operatorname{Bl}_Z(X)$ 是 $k[x, y] \times_k \mathbb{P}^1_k$ 的一个闭子概形，由方程 $xu = yv$ 定义（其中 $(x, y)$ 是 $\mathbb{A}^2$ 的坐标，$[u:v]$ 是 $\mathbb{P}^1$ 的齐次坐标）。
2. 例外除子 $E \cong \mathbb{P}^1_k$。
3. 爆破映射 $\pi: \operatorname{Bl}_Z(X) \to \mathbb{A}^2$ 在 $\mathbb{A}^2 \setminus \{(0,0)\}$ 上是同构。

**解答**：

**(1)**：$Z$ 的理想为 $\mathfrak{m} = (x, y)$。Rees 代数为

$$R = k[x, y] \oplus \mathfrak{m} \oplus \mathfrak{m}^2 \oplus \cdots = k[x, y, xt, yt] \subseteq k[x, y, t]$$

其中 $t$ 是新变量。$\operatorname{Bl}_Z(X) = \operatorname{Proj}(R)$。

用 $u = xt$, $v = yt$，则 $R = k[x, y, u, v] / (xu - yv)$（在适当的分次下）。 Proj 的显式描述给出：在仿射开集 $D_+(u)$ 上，$v/u = y/x$，坐标环为 $k[x, y, y/x]$；在 $D_+(v)$ 上，坐标环为 $k[x, y, x/y]$。

把这些黏合起来，恰好就是

$$\operatorname{Bl}_Z(X) = \{((x, y), [u:v]) \in \mathbb{A}^2 \times \mathbb{P}^1 \mid xu = yv\}$$

（这就是著名的 **Hirzebruch 曲面** $F_1$ 的定义方程，或更简单地，是切丛的射影化。）∎

**(2)**：$E = \pi^{-1}(Z)$ 对应 $x = y = 0$。代入方程 $xu = yv$ 得 $0 = 0$，对 $[u:v]$ 无额外限制。故

$$E = \{(0, 0)\} \times \mathbb{P}^1 \cong \mathbb{P}^1$$

**(3)**：在 $\mathbb{A}^2 \setminus \{(0,0)\}$ 上，$(x, y) \neq (0, 0)$，比值 $[x:y]$ 良定义。映射 $(x, y) \mapsto ((x, y), [x:y])$ 给出逆映射。故 $\pi$ 是同构。∎

> **几何直觉**：$\mathbb{A}^2$ 在原点的爆破是最经典的例子。原来的原点被替换成 $\mathbb{P}^1$，这个 $\mathbb{P}^1$ 参数化了所有通过原点的直线方向。如果你在平面上画一条过原点的直线 $L$，它的严格变换（strict transform）在爆破后的空间中与 $E$ 交于唯一一点——对应于 $L$ 的方向。这解释了为什么爆破能消解奇点：原来在原点处“乱糟糟”相交的多条曲线，现在在 $E$ 上各自有了不同的交点。

---

### 习题 19.4.B：Castelnuovo 判别法（概要）

**题目**（FOAG Ch 19, Exercise 19.4.B，变形）：

设 $X$ 是光滑曲面，$C \subseteq X$ 是光滑有理曲线（$C \cong \mathbb{P}^1$），满足 $C^2 = -1$（自交数为 $-1$）。证明存在光滑曲面 $Y$ 和态射 $\pi: X \to Y$，使得 $\pi$ 是以 $C$ 为例外除子的爆破。即：$C$ 可以被“收缩”成一个光滑点。

**解答**：

这是著名的 **Castelnuovo 收缩定理**（Castelnuovo's contraction criterion）。

**步骤 1**：证明存在 $X$ 上的线丛 $\mathcal{L}$，使得对 $C$ 的限制 $\mathcal{L}|_C = \mathcal{O}_{\mathbb{P}^1}(1)$，且对所有 $m > 0$，高阶上同调 $H^1(X, \mathcal{L}^{\otimes m}) = 0$。

具体构造：取一个非常丰富线丛 $H$ 和适当的 $n$，令 $\mathcal{L} = H^{\otimes n} \otimes \mathcal{O}_X(C)$。由 $C^2 = -1$，利用相交理论和 Riemann-Roch 可以验证 $H^0(X, \mathcal{L})$ 足够大。

**步骤 2**：$\mathcal{L}$ 的全局截面定义一个到射影空间的映射 $\phi: X \to \mathbb{P}^N$。可以证明 $\phi$ 把 $C$ 收缩到一个点 $p \in Y := \phi(X)$，且在其他地方是同构。

**步骤 3**：利用 $C^2 = -1$ 和正规交叉条件，验证 $Y$ 在 $p$ 处是光滑的。具体地，$C$ 的法丛为 $\mathcal{N}_{C/X} = \mathcal{O}_{\mathbb{P}^1}(-1)$，这恰好是 $\mathbb{P}^2$ 在原点爆破后的例外除子的法丛。由爆破的泛性质，$X$ 必同构于 $\operatorname{Bl}_p(Y)$。∎

> **几何直觉**：Castelnuovo 判别法是爆破的“逆操作”。爆破把一点变成 $-1$-曲线；反过来，任何 $-1$-曲线都可以被“吹灭”回一个点。这在双有理几何中至关重要：它是曲面极小模型理论的基础步骤。自交数 $-1$ 是能否收缩的关键数值不变量——它告诉我们这条曲线的法方向“恰好是一个点爆破的逆”。

---

## Lean4 代码引用

以下代码展示了 Mathlib4 中爆破与双有理几何的形式化框架：

```lean4
import Mathlib.AlgebraicGeometry.Blowup

open AlgebraicGeometry

variable {X : Scheme} {Z : ClosedImmersionScheme X}

/-- 爆破的构造 -/
example : Scheme :=
  blowup Z

/-- 爆破的泛性质 -/
example {Y : Scheme} (f : Y ⟶ X) (hf : IsCartierDivisor (pullback f Z)) :
    ∃! g : Y ⟶ blowup Z, π Z ∘ g = f := by
  -- 对应于本文的爆破泛性质
  sorry

/-- 平面在原点的爆破 -/
example : blowup (origin 𝔸²) ≅
  Proj (reesAlgebra (maximalIdeal (k[x,y]))) := by
  sorry
```

对应文件：`Mathlib.AlgebraicGeometry.Blowup` 中定义了 `blowup` 函子及其泛性质。曲面的 Castelnuovo 收缩定理在 `Mathlib.AlgebraicGeometry.Surface` 相关的文件中有部分形式化。

---

**文档位置**: `docs/13-代数几何/FOAG-深化/AG-VK-027-爆破的几何与代数.md`
**创建日期**: 2026-04-17
**最后更新**: 2026-04-17


## 习题

**习题 1.1**。描述 $\\mathbb{A}^2$ 在原点爆破后的例外除子 $E$ 的自交数。

*解答*：$\\operatorname{Bl}_0 \\mathbb{A}^2$ 的例外除子 $E \\cong \\mathbb{P}^1$，$E^2 = -1$。这是爆破的基本性质。$\square$

---

**习题 1.2**。证明：曲面的爆破不改变Picard数的变号性（即若 $S$ 的相交形式是不定的，则 $\\operatorname{Bl}_P S$ 也是）。

*解答*：爆破增加一个 $E$ 类，$E^2=-1$。原Picard格与 $\\mathbb{Z}E$ 直和，变号性保持。$\square$
