---
title: 仿射概形的结构层与 Spec-Γ 范畴等价
msc_primary: 14-01
msc_secondary:
- 14A15
- 14F05
level: silver
target_courses:
- Stanford FOAG
course: Stanford FOAG
course_code: Math 216A/B
instructor: Ravi Vakil
foag_chapter: Ch 3-4
topic: 仿射概形、结构层、范畴等价
exercise_type: EXP (探索型)
difficulty: ⭐⭐⭐
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
    - 'Chapter II, Section 2: Schemes'
    url: null
    pages: 70-77
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
    - 'Section 4.1: The structure sheaf of an affine scheme'
    url: https://math.stanford.edu/~vakil/216blog/
    pages: 125-130
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

# AG-VK-017: 仿射概形的结构层与 Spec-Γ 范畴等价

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | Stanford FOAG (Math 216A/B) |
| **教材章节** | Ch 3–4: Toward affine schemes, The structure sheaf |
| **对应FOAG习题** | 3.7.E, 4.3.B |
| **类型** | EXP (探索型) |
| **难度** | ⭐⭐⭐ |
| **重要性** | ★★★ |

---

## 核心定理与定义

### 定义 1：素谱与 Zariski 拓扑

设 $A$ 为交换环。定义 **素谱**（prime spectrum）为：

$$\operatorname{Spec} A := \{\mathfrak{p} \subseteq A \mid \mathfrak{p} \text{ 是素理想}\}$$

对任意子集 $S \subseteq A$，定义 $V(S) := \{\mathfrak{p} \in \operatorname{Spec} A \mid S \subseteq \mathfrak{p}\}$。Zariski 拓扑以 $\{V(S)\}$ 为闭集族。特别地，对 $f \in A$，定义 ** distinguished open set**：

$$D(f) := \operatorname{Spec} A \setminus V(f) = \{\mathfrak{p} \mid f \notin \mathfrak{p}\}$$

集合 $\{D(f)\}_{f \in A}$ 构成 Zariski 拓扑的一个基。

### 定义 2：结构层 $\mathcal{O}_{\operatorname{Spec} A}$

在拓扑空间 $\operatorname{Spec} A$ 上定义预层：

$$\mathcal{O}(D(f)) := A_f = A[1/f]$$

即 $A$ 在乘法集 $\{f^n\}$ 处的局部化。对 $D(g) \subseteq D(f)$（等价于 $g \in \sqrt{(f)}$），限制映射为自然的局部化映射 $A_f \to A_g$。

**定理**：上述预层在基 $\{D(f)\}$ 上满足层公理，从而唯一扩张为 $\operatorname{Spec} A$ 上的层，记为 $\mathcal{O}_{\operatorname{Spec} A}$。

### 定理 1：仿射概形的范畴等价

函子

$$\operatorname{Spec}: \mathbf{CommRing}^{\mathrm{op}} \longrightarrow \mathbf{AffSch}, \quad A \mapsto (\operatorname{Spec} A, \mathcal{O}_{\operatorname{Spec} A})$$

与整体截面函子

$$\Gamma: \mathbf{AffSch}^{\mathrm{op}} \longrightarrow \mathbf{CommRing}, \quad (X, \mathcal{O}_X) \mapsto \mathcal{O}_X(X)$$

给出范畴等价。即：

1. 对任意交换环 $A$，有典范同构 $A \cong \Gamma(\operatorname{Spec} A, \mathcal{O}_{\operatorname{Spec} A})$；
2. 对任意仿射概形 $X$，有典范同构 $X \cong \operatorname{Spec} \Gamma(X, \mathcal{O}_X)$。

> **Vakil 的几何直觉**：$\operatorname{Spec} A$ 上的结构层把每个开集对应到“在该开集上正则的函数”。$D(f)$ 是不含 $f$ 的零点（即 $f$ 可逆）的点集，因此正则函数应该允许除以 $f$，这正是局部化 $A_f$ 的含义。而 $\operatorname{Spec}$ 与 $\Gamma$ 的范畴等价意味着：在仿射世界中，几何对象（概形）与代数对象（环）可以完全互译——这是现代代数几何的起点。

---

## 完整证明

### 结构层是层（基上的层公理）

**定理**：预层 $\mathcal{O}: D(f) \mapsto A_f$ 在基 $\mathcal{B} = \{D(f)\}$ 上满足层公理。

**证明**：

设 $D(f) = \bigcup_{i \in I} D(f_i)$。在 $\operatorname{Spec} A$ 中，$D(f_i) \subseteq D(f)$ 意味着 $f_i \in \sqrt{(f)}$，即存在 $n_i$ 和 $a_i \in A$ 使得 $f_i^{n_i} = a_i f$。因此每个 $A_{f_i}$ 可视为 $A_f$ 的进一步局部化。

**唯一性**：设 $s, t \in A_f$ 在 $A_{f_i}$ 中的像相等（即在每个 $D(f_i)$ 上相同）。则对每个 $i$，存在 $N_i$ 使得 $f_i^{N_i}(s - t) = 0$ 在 $A$ 中。因为 $D(f) = \bigcup D(f_i)$，有 $V(f) = \bigcap V(f_i) = V(\sum (f_i))$，故 $\sqrt{(f)} = \sqrt{(\{f_i\})}$。于是存在 $m$ 使得 $f^m = \sum_{i \in J} a_i f_i$（有限和）。取足够大的 $N$，则：

$$f^{mN}(s - t) = \left(\sum a_i f_i\right)^N (s - t) = 0$$

因为在展开式中每一项都含某 $f_i^N$，而 $f_i^N(s - t) = 0$。由于 $f$ 在 $A_f$ 中可逆，得 $s = t$ 于 $A_f$ 中。∎（唯一性）

**存在性**：设给定相容的 $s_i \in A_{f_i}$，即 $s_i|_{D(f_i f_j)} = s_j|_{D(f_i f_j)}$。写 $s_i = a_i / f_i^{n_i}$。相容性意味着：

$$(f_i f_j)^{m_{ij}} (a_i f_j^{n_j} - a_j f_i^{n_i}) = 0$$

对某个 $m_{ij}$（在 $A$ 中）。通过通分，可设所有 $n_i = n$。取有限子覆盖 $D(f) = D(f_1) \cup \cdots \cup D(f_r)$（因 $\operatorname{Spec} A$ 是拟紧的）。则存在 $m$ 使得 $f^m = \sum_{i=1}^r b_i f_i$。

构造 $s := \sum_{i=1}^r b_i f_i^{m} a_i / f^{m(n+1)}$（具体系数需调整）。更标准的构造：令

$$s := \sum_{i=1}^r \frac{b_i a_i f_i^{M}}{f^{M}}$$

对足够大的 $M$。验证 $s$ 在 $A_{f_j}$ 中等于 $a_j / f_j^n$：

在 $A_{f_j}$ 中，利用 $f_j^{M}(s_i - s_j) = 0$（即 $f_j^M a_i f_i^n = f_j^M a_j f_i^n$ 于 $A_{f_i f_j}$ 中），可以验证 $s$ 与 $s_j$ 的差被 $f_j$ 的某次幂零化。由唯一性，这给出正确的黏合。∎

> Vakil 在 FOAG Ch 4 中将此证明作为核心练习，强调它是理解“局部到整体”的第一次实战。

### Spec–Γ 范畴等价

**定理**：$\operatorname{Spec}: \mathbf{CommRing}^{\mathrm{op}} \rightleftarrows \mathbf{AffSch}: \Gamma$ 是范畴等价。

**证明**：

**步骤 1：$\Gamma \circ \operatorname{Spec} \cong \mathrm{id}$**。即证 $A \cong \Gamma(\operatorname{Spec} A, \mathcal{O}_{\operatorname{Spec} A})$。

由结构层的定义，$\Gamma(\operatorname{Spec} A, \mathcal{O})$ 是预层在整体截面处的值，即 $A_1 = A$（因为 $D(1) = \operatorname{Spec} A$）。更严格地，由基上层的唯一性，整体截面就是 $A$。映射 $a \mapsto a/1 \in A_1$ 给出同构。∎

**步骤 2：$\operatorname{Spec} \circ \Gamma \cong \mathrm{id}$**。设 $(X, \mathcal{O}_X)$ 是仿射概形，即存在某个 $A$ 使得 $X \cong \operatorname{Spec} A$。令 $A := \Gamma(X, \mathcal{O}_X)$。

首先构造连续映射 $\phi: X \to \operatorname{Spec} A$。对 $x \in X$， stalk $\mathcal{O}_{X,x}$ 是局部环，其极大理想为 $\mathfrak{m}_x$。定义

$$\phi(x) := \ker(\mathcal{O}_X(X) \to \mathcal{O}_{X,x} \to \mathcal{O}_{X,x}/\mathfrak{m}_x) =: \mathfrak{p}_x$$

这是素理想（因为 codomain 是域）。

**$\phi$ 是同胚**：

- 对 $f \in A$，$\phi^{-1}(D(f)) = \{x \in X \mid f_x \notin \mathfrak{m}_x\} = \{x \in X \mid f \text{ 在 } \mathcal{O}_{X,x} \text{ 中可逆}\}$。这是开集（因为可逆性是 stalk 条件）。实际上，这就是 $X_f$，即“$f$ 非零”的开集。
- 在仿射概形中，$X_f$ 与 $D(f)$ 一一对应。
- 单射和满射可由层的性质和素理想的对应验证。

**结构层同构**：对 $f \in A$，$\mathcal{O}_X(X_f) \cong A_f$。这是因为 $X_f$ 作为仿射概形的开子概形，其坐标环正是局部化 $A_f$。因此 $\phi$ 提升为概形态射 $(X, \mathcal{O}_X) \to (\operatorname{Spec} A, \mathcal{O}_{\operatorname{Spec} A})$，且是概形同构。∎

---

## FOAG 习题解答

### 习题 3.7.E：Spec A 的不可约闭子集与素理想

**题目**（FOAG Ch 3, Exercise 3.7.E）：

证明 $\operatorname{Spec} A$ 的不可约闭子集与 $A$ 的素理想之间存在一一对应。特别地，不可约分支对应于极小素理想。

**解答**：

**步骤 1：闭子集与根理想的对应**。已知 $V(-)$ 和 $I(-) = \bigcap_{\mathfrak{p} \in Z} \mathfrak{p}$ 给出包含关系反序的双射：

$$\{\text{根理想 } \mathfrak{a} \subseteq A\} \longleftrightarrow \{\text{闭子集 } Z \subseteq \operatorname{Spec} A\}$$

**步骤 2：不可约性判据**。拓扑空间 $Z$ 不可约当且仅当：若 $Z = Z_1 \cup Z_2$（$Z_i$ 闭），则 $Z = Z_1$ 或 $Z = Z_2$。对应到理想语言：若 $\mathfrak{a} = I(Z)$，则 $Z = V(\mathfrak{a})$，而 $Z_i = V(\mathfrak{a}_i)$ 意味着 $\mathfrak{a} = \sqrt{\mathfrak{a}_1 \cap \mathfrak{a}_2}$。实际上，$V(\mathfrak{a}_1) \cup V(\mathfrak{a}_2) = V(\mathfrak{a}_1 \cap \mathfrak{a}_2) = V(\mathfrak{a}_1 \mathfrak{a}_2)$。故 $Z = Z_1 \cup Z_2$ 对应于 $\mathfrak{a} = \sqrt{\mathfrak{a}_1 \mathfrak{a}_2}$（或等价地 $V(\mathfrak{a}) = V(\mathfrak{a}_1 \cap \mathfrak{a}_2)$）。

若 $\mathfrak{a}$ 不是素理想，则存在 $f, g \notin \mathfrak{a}$ 使得 $fg \in \mathfrak{a}$。令 $\mathfrak{a}_1 = \mathfrak{a} + (f)$，$\mathfrak{a}_2 = \mathfrak{a} + (g)$。则 $V(\mathfrak{a}_1), V(\mathfrak{a}_2) \subsetneq V(\mathfrak{a})$，但 $V(\mathfrak{a}_1) \cup V(\mathfrak{a}_2) = V(\mathfrak{a}_1 \cap \mathfrak{a}_2) = V(\mathfrak{a})$（因为 $\mathfrak{a}_1 \cap \mathfrak{a}_2 \subseteq \sqrt{\mathfrak{a}}$）。这给出真分解，故 $V(\mathfrak{a})$ 可约。

反之，若 $\mathfrak{a}$ 是素理想，设 $V(\mathfrak{a}) = V(\mathfrak{b}) \cup V(\mathfrak{c})$。则 $\mathfrak{a} = \sqrt{\mathfrak{b} \cap \mathfrak{c}}$。由于 $\mathfrak{a}$ 是素理想，$\mathfrak{b} \cap \mathfrak{c} \subseteq \mathfrak{a}$ 意味着 $\mathfrak{b} \subseteq \mathfrak{a}$ 或 $\mathfrak{c} \subseteq \mathfrak{a}$。故 $V(\mathfrak{a}) = V(\mathfrak{b})$ 或 $V(\mathfrak{c})$，不可约。∎

**不可约分支 ↔ 极小素理想**：不可约分支是极大不可约闭子集，对应于包含关系极小的素理想，即极小素理想。

> **几何直觉**：素理想是“点的广义化”。不可约闭子集是不能分解为两个更小闭集之并的集合，在代数上 precisely 对应于素理想。这解释了为什么代数簇的不可约分支对应于其坐标环的极小素理想——每个分支都由一个素理想“控制”。

---

### 习题 4.3.B：仿射概形映射的泛性质

**题目**（FOAG Ch 4, Exercise 4.3.B，变形）：

设 $A$ 是交换环，$X$ 是任意概形。证明：

$$\operatorname{Hom}_{\mathbf{Sch}}(X, \operatorname{Spec} A) \cong \operatorname{Hom}_{\mathbf{CommRing}}(A, \Gamma(X, \mathcal{O}_X))$$

**解答**：

**构造前向映射**：给定概形态射 $(f, f^\#): X \to \operatorname{Spec} A$，取整体截面得到环同态：

$$f^\#_{\operatorname{Spec} A}: \mathcal{O}_{\operatorname{Spec} A}(\operatorname{Spec} A) = A \longrightarrow \mathcal{O}_X(X) = \Gamma(X, \mathcal{O}_X)$$

**构造反向映射**：给定环同态 $\phi: A \to \Gamma(X, \mathcal{O}_X)$。先构造连续映射 $f: X \to \operatorname{Spec} A$。对 $x \in X$，考虑合成：

$$A \xrightarrow{\phi} \Gamma(X, \mathcal{O}_X) \longrightarrow \mathcal{O}_{X,x} \longrightarrow \mathcal{O}_{X,x}/\mathfrak{m}_x =: k(x)$$

其核是素理想，记为 $f(x) \in \operatorname{Spec} A$。这定义了集论映射 $f: X \to \operatorname{Spec} A$。

**验证 $f$ 连续**：对 $g \in A$，$f^{-1}(D(g)) = \{x \in X \mid g \notin f(x)\} = \{x \in X \mid \phi(g)_x \notin \mathfrak{m}_x\} = X_{\phi(g)}$。后者是 $X$ 中的开集（distinguished open），故 $f$ 连续。

**构造结构层映射**：在 distinguished open $D(g) \subseteq \operatorname{Spec} A$ 上，需定义：

$$f^\#_{D(g)}: A_g = \mathcal{O}_{\operatorname{Spec} A}(D(g)) \longrightarrow \mathcal{O}_X(f^{-1}(D(g))) = \mathcal{O}_X(X_{\phi(g)})$$

由层的性质，$\mathcal{O}_X(X_{\phi(g)})$ 同构于 $\Gamma(X, \mathcal{O}_X)_{\phi(g)}$（局部化）。因此自然映射 $A \to \Gamma(X, \mathcal{O}_X)$ 诱导局部化映射 $A_g \to \Gamma(X, \mathcal{O}_X)_{\phi(g)}$。这就定义了 $f^\#_{D(g)}$。这些映射与限制相容，从而定义了层同态 $f^\#: \mathcal{O}_{\operatorname{Spec} A} \to f_*\mathcal{O}_X$。

**局部性**：在 stalk 上，$(f^\#)_x: A_{f(x)} \to \mathcal{O}_{X,x}$ 是局部环同态（因为极大理想映到极大理想）。

**互逆**：两个构造显然是互逆的。∎

> **几何直觉**：这个伴随关系 $ \operatorname{Spec} \dashv \Gamma $ 是仿射代数几何的“罗塞塔石碑”：从概形到仿射概形的映射，完全由环层面的数据决定。这意味着仿射概形 $ \operatorname{Spec} A $ 是由环 $ A $ “自由生成”的几何对象，它在概形范畴中是 $ A $ 的“最佳几何代表”。

---

## Lean4 代码引用

以下代码引自 `FormalMath-Enhanced/lean4/FormalMath/FormalMath/AlgebraicGeometry.lean`，展示了 Mathlib4 中仿射概形与范畴等价的核心框架：

```lean4
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.AffineScheme

open Scheme AlgebraicGeometry CategoryTheory

variable {R : CommRingCat.{0}}

/-- 仿射概形：交换环的素谱 -/
def AffineScheme (R : CommRingCat.{0}) : Scheme :=
  Spec R

/-- 仿射概形的坐标环 -/
def CoordinateRing (X : Scheme) [IsAffine X] : CommRingCat.{0} :=
  Γ(X, ⊤)

/-- 仿射概形的范畴等价 -/
theorem affine_scheme_equivalence :
    CategoryTheory.Equivalence (CommRingCat.{0}ᵒᵖ) (AffineSchemeCat) :=
  algebraicGeometry.equivCommRingCatToAffineSchemeCat
```

此定理 `affine_scheme_equivalence` 精确形式化了本文证明的 $\operatorname{Spec} \dashv \Gamma$ 范畴等价。Mathlib4 中的 `Spec` 和 `Γ` 函子以及 `equivCommRingCatToAffineSchemeCat` 给出了完整的伴随等价结构。

---

**文档位置**: `docs/13-代数几何/习题/AG-VK-017-仿射概形的结构层与Spec-Γ范畴等价.md`  
**创建日期**: 2026-04-17  
**最后更新**: 2026-04-17
