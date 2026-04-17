---
title: Proj 构造与其泛性质
msc_primary: 14-01
msc_secondary:
- 14A15
- 14Mxx
level: silver
target_courses:
- Stanford FOAG
course: Stanford FOAG
course_code: Math 216A/B
instructor: Ravi Vakil
foag_chapter: Ch 6
topic: Proj 构造、射影概形、泛性质
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
    - 'Chapter II, Section 2: Schemes (Proj construction)'
    url: null
    pages: 76-81
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
    - 'Section 4.5: Proj and projective schemes'
    url: https://math.stanford.edu/~vakil/216blog/
    pages: 145-152
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

# AG-VK-018: Proj 构造与其泛性质

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | Stanford FOAG (Math 216A/B) |
| **教材章节** | Ch 6: Morphisms of schemes (§6.3–6.4) |
| **对应FOAG习题** | 6.3.M, 6.4.F |
| **类型** | GEO (几何型) |
| **难度** | ⭐⭐⭐⭐ |
| **重要性** | ★★★ |

---

## 核心定理与定义

### 定义 1：分次环与齐次素谱

设 $S = \bigoplus_{d \geq 0} S_d$ 为 $\mathbb{Z}_{\geq 0}$-分次交换环。定义 **齐次素谱**（homogeneous prime spectrum）为：

$$\operatorname{Proj} S := \{\mathfrak{p} \subseteq S \mid \mathfrak{p} \text{ 是齐次素理想，且 } S_+ \not\subseteq \mathfrak{p}\}$$

其中 $S_+ := \bigoplus_{d > 0} S_d$ 是 ** irrelevant ideal**。Zariski 拓扑的闭集为 $V_h(T) := \{\mathfrak{p} \in \operatorname{Proj} S \mid T \subseteq \mathfrak{p}\}$（$T$ 为齐次子集）。对 $f \in S_d$（$d > 0$），定义 **齐次 distinguished open**：

$$D_+(f) := \operatorname{Proj} S \setminus V_h(f) = \{\mathfrak{p} \in \operatorname{Proj} S \mid f \notin \mathfrak{p}\}$$

$\{D_+(f)\}_{f \text{ 齐次}}$ 构成 $\operatorname{Proj} S$ 的拓扑基。

### 定义 2：Proj 上的结构层

在基 $\{D_+(f)\}$ 上定义预层：

$$\mathcal{O}_{\operatorname{Proj} S}(D_+(f)) := (S_f)_0$$

其中 $S_f$ 是 $S$ 在 $f$ 处的局部化，下标 $0$ 表示 **次数零部分**。对 $D_+(g) \subseteq D_+(f)$，限制映射为自然的局部化映射在零次部分的限制。

**定理**：上述预层在基上满足层公理，从而唯一扩张为 $\operatorname{Proj} S$ 上的层。赋有此层的环化空间 $(\operatorname{Proj} S, \mathcal{O}_{\operatorname{Proj} S})$ 称为 **射影概形**（projective scheme）。

### 定理 1：Proj 的泛性质

设 $S$ 为分次环。则概形 $\operatorname{Proj} S$ 具有以下泛性质：

对任意概形 $X$ 和满足以下条件的环同态 $\phi: S \to \Gamma_*(X, \mathcal{L})$（其中 $\mathcal{L}$ 是 $X$ 上的可逆层，$\Gamma_*(X, \mathcal{L}) := \bigoplus_{d \geq 0} \Gamma(X, \mathcal{L}^{\otimes d})$ 是分次环）：

1. $\phi$ 保持分次（即 $\phi(S_d) \subseteq \Gamma(X, \mathcal{L}^{\otimes d})$）；
2. $S_+$ 的像局部生成 $\mathcal{L}$（即对任意 $x \in X$，存在 $f \in S_1$ 使得 $\phi(f)_x$ 是 $\mathcal{L}_x$ 的生成元）；

则存在唯一的概形态射 $f: X \to \operatorname{Proj} S$ 使得 $f^*\mathcal{O}(1) \cong \mathcal{L}$ 且图表交换。

> **Vakil 的几何直觉**：$\operatorname{Proj}$ 是把一个“齐次代数对象”（分次环）转化成一个“紧几何对象”的过程。与仿射情形不同，$\operatorname{Proj}$ 天然排除了 irrelevant ideal 对应的点，这相当于在几何上进行了“紧化”——把那些“不 behaves well 的无穷远点”排除掉。$\mathbb{P}^n = \operatorname{Proj} k[x_0, \ldots, x_n]$ 是最典型的例子：齐次坐标 $[x_0 : \cdots : x_n]$ 在比例缩放下不变，这正是分次结构的体现。

---

## 完整证明

### Proj 是概形

**步骤 1：拓扑结构**。$\operatorname{Proj} S$ 的 Zariski 拓扑由齐次素理想定义。关键观察：$D_+(f)$ 与仿射概形 $\operatorname{Spec}((S_f)_0)$ 同胚。映射为：

$$\mathfrak{p} \in D_+(f) \longmapsto \mathfrak{p} S_f \cap (S_f)_0 \in \operatorname{Spec}((S_f)_0)$$

这是连续双射，且开集对应开集。

**步骤 2：结构层**。预层 $\mathcal{O}(D_+(f)) = (S_f)_0$ 在基上满足层公理。验证方法与仿射情形类似，但需注意只取零次部分。设 $D_+(f) = \bigcup D_+(f_i)$，在 $(S_f)_0$ 中验证唯一性和黏合性。

- **唯一性**：若 $s, t \in (S_f)_0$ 在每个 $(S_{f_i})_0$ 中相等，则 $s = t$（由局部化的泛性质，零次部分也唯一）。
- **黏合性**：给定相容的 $s_i \in (S_{f_i})_0$，可找到共同分母 $f^N g$（$g$ 为某齐次元），使得 $s_i = a_i / (f^{N} g^{M})$。通过仿射情形的黏合论证（限制在零次部分），可黏合成 $s \in (S_f)_0$。

**步骤 3：局部仿射性**。每个点 $\mathfrak{p} \in \operatorname{Proj} S$ 都含于某个 $D_+(f)$（因 $S_+ \not\subseteq \mathfrak{p}$，故存在齐次 $f \in S_+ \setminus \mathfrak{p}$）。而 $(D_+(f), \mathcal{O}|_{D_+(f)}) \cong \operatorname{Spec}((S_f)_0)$ 是仿射概形。因此 $\operatorname{Proj} S$ 是概形。∎

### Proj 的泛性质（详述）

**设定**：设 $X$ 为概形，$\mathcal{L}$ 为 $X$ 上的可逆层，$\phi: S \to \Gamma_*(X, \mathcal{L})$ 为分次环同态，满足 $S_+$ 局部生成 $\mathcal{L}$。

**构造态射 $f: X \to \operatorname{Proj} S$**：

对 $x \in X$，条件 (2) 意味着存在 $x$ 的开邻域 $U$ 和 $f \in S_1$ 使得 $\phi(f)|_U$ 是 $\mathcal{L}|_U$ 的 nowhere-vanishing 截面。这给出 trivialization $\mathcal{L}|_U \cong \mathcal{O}_U$。对 $g \in S_d$，$\phi(g)|_U$ 对应 $\mathcal{O}_U$ 的截面，即环元素 $\psi(g) \in \mathcal{O}_U(U)$。

具体地，对任意齐次 $g \in S_d$，截面 $\phi(g)|_U \otimes (\phi(f)|_U)^{-d} \in \mathcal{O}_U(U)$ 定义了环元素。这给出环同态：

$$\psi_f: (S_f)_0 \longrightarrow \mathcal{O}_U(U), \quad \frac{g}{f^d} \longmapsto \phi(g)|_U \otimes (\phi(f)|_U)^{-d}$$

由习题 4.3.B（仿射概形的泛性质），这诱导唯一的态射 $f_U: U \to \operatorname{Spec}((S_f)_0) \cong D_+(f) \subseteq \operatorname{Proj} S$。

**相容性**：若 $f, g \in S_1$ 都满足条件，则在 $U \cap V$ 上，映射 $f_U$ 和 $f_V$ 相容（因为局部化映射 $(S_f)_0 \to (S_{fg})_0$ 与限制映射相容）。由层的性质，这些局部态射黏合成整体态射 $f: X \to \operatorname{Proj} S$。

**$f^*\mathcal{O}(1) \cong \mathcal{L}$**：在 $D_+(f)$ 上，$\mathcal{O}(1)$ 对应于分次 $S$-模 $S(1)$ 的层化。拉回 $f^*\mathcal{O}(1)$ 的局部描述由 $\phi(f)$ 给出，这恰好是 $\mathcal{L}$ 的局部平凡化。因此 $f^*\mathcal{O}(1) \cong \mathcal{L}$。∎

---

## FOAG 习题解答

### 习题 6.3.M：Proj 的泛性质

**题目**（FOAG Ch 6, Exercise 6.3.M）：

陈述并证明 $\operatorname{Proj} S$ 的泛性质：到 $\operatorname{Proj} S$ 的态射与满足局部生成条件的线丛及分次环同态之间的对应。

**解答**：

**陈述**：设 $S$ 为分次环。函子

$$X \longmapsto \left\{ (\mathcal{L}, \phi) \;\middle|\; \mathcal{L} \in \operatorname{Pic}(X), \phi: S \to \Gamma_*(X, \mathcal{L}) \text{ 分次同态}, S_+ \text{ 局部生成 } \mathcal{L} \right\} / \cong$$

由 $f \mapsto (f^*\mathcal{O}(1), f^*\natural)$ 给出，与 $\operatorname{Hom}(X, \operatorname{Proj} S)$ 自然同构。

**证明概要**：

- **前向**：给定 $f: X \to \operatorname{Proj} S$，令 $\mathcal{L} = f^*\mathcal{O}(1)$。整体截面的拉回给出分次同态 $S \cong \Gamma_*(\operatorname{Proj} S, \mathcal{O}(1)) \to \Gamma_*(X, \mathcal{L})$。局部生成条件来自 $\mathcal{O}(1)$ 在 $\operatorname{Proj} S$ 上由 $S_1$ 局部生成。

- **反向**：给定 $(\mathcal{L}, \phi)$，按上节构造 $f: X \to \operatorname{Proj} S$。

- **互逆**：$f^*\mathcal{O}(1) \cong \mathcal{L}$ 由构造保证；而从 $f$ 恢复的分次同态就是原来的 $\phi$（因为在 $D_+(s)$ 上，$s \in S_1$ 对应 $\mathcal{O}(1)$ 的局部生成元，其拉回正是 $\phi(s)$）。∎

> **几何直觉**：这个泛性质告诉我们，$\operatorname{Proj} S$ 是“拥有由 $S$ 参数化的线丛”的泛概形。特别地，当 $S = k[x_0, \ldots, x_n]$ 时，到 $\mathbb{P}^n$ 的态射就是由 $n+1$ 个“无处同时为零”的整体截面给出的——这正是经典代数几何中射影嵌入的描述。

---

### 习题 6.4.F：射影空间与坐标环

**题目**（FOAG Ch 6, Exercise 6.4.F，变形）：

设 $S = k[x_0, \ldots, x_n]$ 为多项式环（标准分次）。验证：

1. $\operatorname{Proj} S \cong \mathbb{P}^n_k$ 作为概形；
2. 计算 $\Gamma(\mathbb{P}^n_k, \mathcal{O}(m))$ 对所有 $m \in \mathbb{Z}$。

**解答**：

**(1) $\operatorname{Proj} S \cong \mathbb{P}^n_k$**

由定义，$\mathbb{P}^n_k = \operatorname{Proj} k[x_0, \ldots, x_n]$。标准覆盖由 $D_+(x_i)$（$i = 0, \ldots, n$）给出。每个开集：

$$D_+(x_i) \cong \operatorname{Spec}((S_{x_i})_0) = \operatorname{Spec} k\left[\frac{x_0}{x_i}, \ldots, \frac{x_n}{x_i}\right] \cong \mathbb{A}^n_k$$

交 $D_+(x_i) \cap D_+(x_j) = D_+(x_i x_j)$ 对应于：

$$\operatorname{Spec} k\left[\frac{x_0}{x_i}, \ldots, \frac{x_n}{x_i}\right]_{x_j/x_i} = \operatorname{Spec} k\left[\frac{x_0}{x_j}, \ldots, \frac{x_n}{x_j}\right]_{x_i/x_j}$$

这 precisely 是 $\mathbb{P}^n_k$ 的经典构造中的粘合。因此 $\operatorname{Proj} S$ 与经典射影空间概形同构。∎

**(2) 计算 $\Gamma(\mathbb{P}^n_k, \mathcal{O}(m))$**

回忆 $\mathcal{O}(m)$ 对应于分次 $S$-模 $S(m)$（次数平移 $m$）。由定义：

$$\Gamma(D_+(x_i), \mathcal{O}(m)) = (S(m)_{x_i})_0 = \left\{ \frac{f}{x_i^d} \;\middle|\; f \in S_{m+d} \right\}$$

整体截面 $\Gamma(\mathbb{P}^n_k, \mathcal{O}(m))$ 是这些局部截面在所有 $D_+(x_i) \cap D_+(x_j)$ 上相容的族。

- **$m \geq 0$**：整体截面 precisely 是 $S$ 中 $m$ 次齐次多项式。即：

$$\Gamma(\mathbb{P}^n_k, \mathcal{O}(m)) \cong S_m = k[x_0, \ldots, x_n]_m$$

维数为 $\binom{n+m}{n}$。

  **证明**：给定 $f \in S_m$，它在 $D_+(x_i)$ 上对应 $f/x_i^0 = f$（若视 $f/x_i^0$ 为 $S(m)_{x_i}$ 中次数 $0$ 元素）。更准确地说，$f/x_i^0$ 在 $(S(m)_{x_i})_0$ 中当且仅当 $\deg(f) - 0 = m$，即总是。而在交上，$f/x_i^0$ 和 $f/x_j^0$ 在 $S(m)_{x_i x_j}$ 中相等（都是 $f$）。故每个 $f \in S_m$ 给出一个整体截面。

  反之，设 $(s_i)$ 是相容整体截面。写 $s_i = f_i / x_i^{d_i}$，其中 $f_i \in S_{m+d_i}$。相容性意味着在 $D_+(x_i x_j)$ 上：

  $$\frac{f_i}{x_i^{d_i}} = \frac{f_j}{x_j^{d_j}} \in S(m)_{x_i x_j}$$

  即 $(x_i x_j)^N (f_i x_j^{d_j} - f_j x_i^{d_i}) = 0$ 于 $S(m)$ 中。由于 $S$ 是整环（多项式环），这意味着 $f_i x_j^{d_j} = f_j x_i^{d_i}$。于是存在 $f \in S_m$ 使得 $f_i = f x_i^{d_i}$，即 $s_i = f$。∎

- **$m < 0$**：此时不存在非零的整体截面。因为若有 $f \in S_k$ 对应 $f/x_i^{d_i} \in (S(m)_{x_i})_0$，则 $k - d_i = m < 0$，即 $k < d_i$。相容性要求这样的 $f$ 在所有 $x_i$ 上同时满足，这在负次数下不可能（除非 $f = 0$）。故：

$$\Gamma(\mathbb{P}^n_k, \mathcal{O}(m)) = 0, \quad m < 0$$

综上：

$$\Gamma(\mathbb{P}^n_k, \mathcal{O}(m)) = \begin{cases} k[x_0, \ldots, x_n]_m & m \geq 0 \\ 0 & m < 0 \end{cases}$$

> **几何直觉**：$\mathcal{O}(m)$ 的截面次数反映了“极点/零点”的权衡。正次数对应齐次多项式（全局正则函数），零次数对应常数函数，负次数则没有全局截面——因为在整个紧的 $\mathbb{P}^n$ 上，“允许极点”意味着必须在某处真的有极点，而负次数的层要求极点比零点更多，这在整体紧流形上是不可能的。

---

## Lean4 代码引用

以下代码展示了 Mathlib4 中 `Proj` 构造的核心框架：

```lean4
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme

open AlgebraicGeometry ProjectiveSpectrum

variable {S : Type*} [CommRing S] [GradedRing (fun n => S_n)]

/-- 射影概形：分次环的 Proj -/
def ProjectiveScheme (S : Type*) [CommRing S] [GradedRing (fun n => S_n)] : Scheme :=
  Proj S

/-- 射影空间 P^n -/
def ProjectiveSpace (n : ℕ) (k : Type*) [Field k] : Scheme :=
  Proj (MvPolynomial (Fin (n + 1)) k)
```

对应文件：`FormalMath-Enhanced/lean4/FormalMath/FormalMath/AlgebraicGeometry.lean` 中定义了 `ProjectiveScheme` 和 `ProjectiveSpace`，并说明了 $\mathcal{O}(1)$ 作为 Serre 扭层的概念。

---

**文档位置**: `docs/13-代数几何/习题/AG-VK-018-Proj构造与其泛性质.md`  
**创建日期**: 2026-04-17  
**最后更新**: 2026-04-17
