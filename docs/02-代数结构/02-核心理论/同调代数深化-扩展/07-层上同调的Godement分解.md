---
msc_primary: 18F20
msc_secondary:
- 14F05
- 18G15
- 32L10
title: 15.7 层上同调的Godement分解 / Godement Resolution in Sheaf Cohomology
processed_at: '2026-04-05'
references:
  textbooks:
    - id: artin_algebra
      type: textbook
      title: Algebra
      authors:
      - Michael Artin
      publisher: Pearson
      edition: 2nd
      year: 2011
      isbn: 978-0132413770
      msc: 16-01
      chapters: []
      url: ~
    - id: strang_la
      type: textbook
      title: Introduction to Linear Algebra
      authors:
      - Gilbert Strang
      publisher: Wellesley-Cambridge Press
      edition: 5th
      year: 2016
      isbn: 978-0980232776
      msc: 15-01
      chapters: []
      url: ~
    - id: dummit_foote_aa
      type: textbook
      title: Abstract Algebra
      authors:
      - David S. Dummit
      - Richard M. Foote
      publisher: Wiley
      edition: 3rd
      year: 2003
      isbn: 978-0471433347
      msc: 13-01
      chapters: []
      url: ~
  databases:
    - id: nlab
      type: database
      name: nLab
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
      consulted_at: 2026-04-17
    - id: stacks_project
      type: database
      name: Stacks Project
      entry_url: "https://stacks.math.columbia.edu/tag/{tag}"
      consulted_at: 2026-04-17
    - id: zbmath
      type: database
      name: zbMATH Open
      entry_url: "https://zbmath.org/?q=an:{zb_id}"
      consulted_at: 2026-04-17
---
# 15.7 层上同调的Godement分解 / Godement Resolution in Sheaf Cohomology

**主题编号**: B.15.07
**创建日期**: 2026年4月3日
**最后更新**: 2026年4月3日

---

## 目录 / Table of Contents

- [15.7 层上同调的Godement分解 / Godement Resolution in Sheaf Cohomology](#157-层上同调的godement分解-godement-resolution-in-sheaf-cohomology)
  - 目录 / Table of Contents
  - [15.7.1 引言 / Introduction](#1571-引言-introduction)
  - [15.7.2 松软层与内射层 / Flabby and Injective Sheaves](#1572-松软层与内射层-flabby-and-injective-sheaves)
    - [松软层的定义与性质 / Definition and Properties of Flabby Sheaves](#松软层的定义与性质-definition-and-properties-of-flabby-sheaves)
    - [内射层与Abel群层范畴 / Injective Sheaves and the Category of Abelian Sheaves](#内射层与abel群层范畴-injective-sheaves-and-the-category-of-abelian-sheaves)
  - [15.7.3 Godement分解的构造 / Construction of Godement Resolution](#1573-godement分解的构造-construction-of-godement-resolution)
    - [茎上的正合列 / Exact Sequence on Stalks](#茎上的正合列-exact-sequence-on-stalks)
    - [Godement分解的定义 / Definition of Godement Resolution](#godement分解的定义-definition-of-godement-resolution)
  - [15.7.4 Godement分解的性质 / Properties of Godement Resolution](#1574-godement分解的性质-properties-of-godement-resolution)
    - [函子性 / Functoriality](#函子性-functoriality)
    - [正合性 / Exactness](#正合性-exactness)
    - [与环层情形的兼容性 / Compatibility with Ringed Spaces](#与环层情形的兼容性-compatibility-with-ringed-spaces)
  - [15.7.5 层上同调作为导出函子 / Sheaf Cohomology as Derived Functors](#1575-层上同调作为导出函子-sheaf-cohomology-as-derived-functors)
    - [整体截影函子 / Global Section Functor](#整体截影函子-global-section-functor)
    - [Čech上同调与导出上同调的关系 / Relation with Čech Cohomology](#čech上同调与导出上同调的关系-relation-with-čech-cohomology)
  - [15.7.6 计算实例 / Computational Examples](#1576-计算实例-computational-examples)
  - [15.7.7 参考文献 / References](#1577-参考文献-references)

---

## 15.7.1 引言 / Introduction

层上同调（Sheaf Cohomology）是现代代数几何、复几何和代数拓扑的核心工具。与群上同调类似，层上同调可以定义为整体截影函子的右导出函子。然而，与模范畴不同，Abel 群层范畴 $\mathbf{Ab}(X)$ 中的内射对象通常难以显式构造。Godement 分解（Godement Resolution）提供了一个典范的、函子性的松软层（flabby sheaf）分解，从而既证明了层上同调作为导出函子的存在性，又给出了实际计算层上同调的有效方法。

**Sheaf cohomology is a central tool in modern algebraic geometry, complex geometry, and algebraic topology. Like group cohomology, sheaf cohomology can be defined as the right derived functors of the global section functor. However, unlike module categories, injective objects in the category of abelian sheaves $\mathbf{Ab}(X)$ are usually difficult to construct explicitly. The Godement resolution provides a canonical, functorial flabby sheaf resolution, thereby proving the existence of sheaf cohomology as derived functors and offering an effective method for computing sheaf cohomology in practice.**

Godement 分解由 Roger Godement 在其经典著作《Topologie algébrique et théorie des faisceaux》（1958）中系统阐述。本文档将详细介绍 Godement 分解的构造、性质及其在层上同调计算中的应用。

---

## 15.7.2 松软层与内射层 / Flabby and Injective Sheaves

### 松软层的定义与性质 / Definition and Properties of Flabby Sheaves

**定义 15.7.1** (松软层 / Flabby Sheaf)
设 $X$ 是拓扑空间，$\mathcal{F}$ 是 $X$ 上的 Abel 群层。称 $\mathcal{F}$ 是**松软的**（flabby 或 flasque），如果对任意开集 $U \subseteq X$，限制映射

$$
\rho_{XU}: \mathcal{F}(X) \longrightarrow \mathcal{F}(U)
$$

是满射。等价地，对任意开集 $V \subseteq U$，限制映射 $\mathcal{F}(U) \to \mathcal{F}(V)$ 是满射。

**命题 15.7.1**
1. 若 $0 \to \mathcal{F}' \to \mathcal{F} \to \mathcal{F}'' \to 0$ 是层的短正合序列且 $\mathcal{F}'$ 松软，则对任意开集 $U$，序列 $0 \to \mathcal{F}'(U) \to \mathcal{F}(U) \to \mathcal{F}''(U) \to 0$ 正合。
2. 若 $0 \to \mathcal{F}' \to \mathcal{F} \to \mathcal{F}'' \to 0$ 正合且 $\mathcal{F}', \mathcal{F}$ 都松软，则 $\mathcal{F}''$ 也松软。
3. 松软层的直和、直积仍是松软层。

**证明** (概要)：
(1) 的关键在于：层正合性意味着 $\mathcal{F} \to \mathcal{F}''$ 是满态射（即茎上的满射）。给定 $s'' \in \mathcal{F}''(U)$，利用 Zorn 引理和 $\mathcal{F}'$ 的松软性，可将局部提升逐步拼成整体提升。
(2) 由 (1)，$\mathcal{F}(U) \to \mathcal{F}''(U)$ 满射，而 $\mathcal{F}(X) \to \mathcal{F}(U)$ 也满射（因 $\mathcal{F}$ 松软），复合即得 $\mathcal{F}''$ 松软。

**定理 15.7.1**
松软层是 $\Gamma(X, -)$-零调的：若 $\mathcal{F}$ 松软，则 $H^q(X, \mathcal{F}) = 0$ 对 $q > 0$。

**证明**：
将 $\mathcal{F}$ 嵌入内射层 $0 \to \mathcal{F} \to \mathcal{I} \to \mathcal{G} \to 0$。因 $\mathcal{F}$ 松软，由命题 15.7.1(1)，$0 \to \mathcal{F}(X) \to \mathcal{I}(X) \to \mathcal{G}(X) \to 0$ 正合。因 $\mathcal{I}$ 内射，$H^q(X, \mathcal{I}) = 0$ 对 $q > 0$。由长正合序列，$H^1(X, \mathcal{F}) = 0$ 且 $H^q(X, \mathcal{G}) \cong H^{q+1}(X, \mathcal{F})$。由命题 15.7.1(2)，$\mathcal{G}$ 也松软，故归纳可得结论。

### 内射层与Abel群层范畴 / Injective Sheaves and the Category of Abelian Sheaves

**定理 15.7.2**
Abel 群层范畴 $\mathbf{Ab}(X)$ 具有充足的内射对象。

**证明思路**：
对每一点 $x \in X$，茎函子 $\mathcal{F} \mapsto \mathcal{F}_x$ 有右伴随函子——摩天大楼层（skyscraper sheaf）函子 $i_{x,*}$。由于 Abel 群范畴具有充足内射对象，且 $i_{x,*}$ 保持内射性（因它有左伴随且正合），可以构造 $\mathcal{F}$ 到一族摩天大楼层的乘积中的嵌入。具体地，对每个 $x$ 取 $(\mathcal{F}_x \to I_x)$ 为 Abel 群的内射嵌入，则

$$
\mathcal{F} \longrightarrow \prod_{x \in X} i_{x,*}(I_x)
$$

是层范畴中的内射嵌入。详见 Godement [2, Théorème 3.1.2] 或 Stacks Project [4, Tag 01DH]。

---

## 15.7.3 Godement分解的构造 / Construction of Godement Resolution

### 茎上的正合列 / Exact Sequence on Stalks

**构造 15.7.1** (Godement 前层 / Godement Presheaf)
设 $\mathcal{F}$ 是 $X$ 上的 Abel 群层。定义前层 $C^0(\mathcal{F})$ 为

$$
C^0(\mathcal{F})(U) = \prod_{x \in U} \mathcal{F}_x
$$

限制映射为自然的坐标投影。由于 $C^0(\mathcal{F})$ 满足层的拼接条件，它实际上是一个层。

**命题 15.7.2**
$C^0(\mathcal{F})$ 是松软层。

**证明**：
由定义，$C^0(\mathcal{F})$ 在开集 $U$ 上的截面就是所有 $x \in U$ 处茎的乘积。给定 $U$ 上的截面，要提升到 $X$ 上，只需在 $X \setminus U$ 的点处任意指定茎中的元素即可。因此限制映射显然是满射。

**命题 15.7.3**
存在自然的单态射 $j: \mathcal{F} \to C^0(\mathcal{F})$，在每个开集上将局部截面 $s \in \mathcal{F}(U)$ 映到其在各点茎中的芽 $(s_x)_{x \in U}$。

**证明**：
若 $s \in \mathcal{F}(U)$ 映为零，则对所有 $x \in U$ 有 $s_x = 0$。由层的局部性质，$s = 0$。因此 $j$ 是单的。

### Godement分解的定义 / Definition of Godement Resolution

**定义 15.7.2** (Godement 分解 / Godement Resolution)
递归地定义：
- $C^0(\mathcal{F})$ 如上
- $Z^0(\mathcal{F}) = \mathcal{F}$
- $Z^1(\mathcal{F}) = \operatorname{coker}(\mathcal{F} \to C^0(\mathcal{F}))$
- 对 $n \geq 1$，定义 $C^n(\mathcal{F}) = C^0(Z^n(\mathcal{F}))$，$Z^{n+1}(\mathcal{F}) = \operatorname{coker}(Z^n(\mathcal{F}) \to C^n(\mathcal{F}))$

则**Godement 分解**是复形：

$$
0 \longrightarrow \mathcal{F} \longrightarrow C^0(\mathcal{F}) \longrightarrow C^1(\mathcal{F}) \longrightarrow C^2(\mathcal{F}) \longrightarrow \cdots
$$

其中微分 $d^n: C^n(\mathcal{F}) \to C^{n+1}(\mathcal{F})$ 是复合 $C^n(\mathcal{F}) \twoheadrightarrow Z^{n+1}(\mathcal{F}) \hookrightarrow C^{n+1}(\mathcal{F})$。

**定理 15.7.3**
Godement 分解是正合的，且每个 $C^n(\mathcal{F})$ 都是松软层。

**证明**：
由构造，对每个 $n$ 有短正合序列 $0 \to Z^n \to C^n \to Z^{n+1} \to 0$。这些序列拼接成长正合序列。由于 $C^n$ 是松软层（归纳：$C^0$ 松软，若 $Z^n$ 是某层的商则...实际上需要更细致的分析）。关键是：层的短正合序列 $0 \to \mathcal{F} \to C^0 \to Z^1 \to 0$ 在每个茎上分裂（因为 $C^0$ 的茎就是 $\mathcal{F}_x \oplus \cdots$ 的形式），因此在茎上正合。由于正合性是茎上的性质，Godement 分解在茎上正合，从而作为层复形也正合。

更精确地说，$C^0(\mathcal{F})_x = \mathcal{F}_x \oplus K_x$（对某 Abel 群 $K_x$），因此 $0 \to \mathcal{F}_x \to C^0(\mathcal{F})_x \to Z^1_x \to 0$ 分裂正合。递归构造保持这一性质，故整个复形茎上正合。

---

## 15.7.4 Godement分解的性质 / Properties of Godement Resolution

### 函子性 / Functoriality

**定理 15.7.4**
Godement 分解是函子性的：对任意层态射 $f: \mathcal{F} \to \mathcal{G}$，存在唯一的链映射 $C^\bullet(f): C^\bullet(\mathcal{F}) \to C^\bullet(\mathcal{G})$ 使得下图交换：

$$
\begin{array}{ccccccccc}
0 & \to & \mathcal{F} & \to & C^0(\mathcal{F}) & \to & C^1(\mathcal{F}) & \to & \cdots \\
 & & \downarrow{f} & & \downarrow & & \downarrow & & \\
0 & \to & \mathcal{G} & \to & C^0(\mathcal{G}) & \to & C^1(\mathcal{G}) & \to & \cdots
\end{array}
$$

**证明**：
由 $C^0$ 的函子性和余核的泛性质，递归构造即得。

### 正合性 / Exactness

**定理 15.7.5**
若 $0 \to \mathcal{F}' \to \mathcal{F} \to \mathcal{F}'' \to 0$ 是层的短正合序列，则诱导的 Godement 分解序列 $0 \to C^\bullet(\mathcal{F}') \to C^\bullet(\mathcal{F}) \to C^\bullet(\mathcal{F}'') \to 0$ 是复形的短正合序列（每列都正合）。

**证明**：
由于茎上的短正合序列分裂，且 $C^0$ 的构造在茎上是直和（含一个额外的直和项），$0 \to C^0(\mathcal{F}')_x \to C^0(\mathcal{F})_x \to C^0(\mathcal{F}'')_x \to 0$ 对每个 $x$ 正合。因此 $0 \to C^0(\mathcal{F}') \to C^0(\mathcal{F}) \to C^0(\mathcal{F}'') \to 0$ 是层的短正合序列。由归纳法，结论对 $C^n$ 成立。

这一性质使得 Godement 分解成为一个**Cartan-Eilenberg 消解**，在研究导出函子时非常有用。

### 与环层情形的兼容性 / Compatibility with Ringed Spaces

**定理 15.7.6**
设 $(X, \mathcal{O}_X)$ 是环化空间。若 $\mathcal{F}$ 是 $\mathcal{O}_X$-模层，则 Godement 分解中的每一项 $C^n(\mathcal{F})$ 都可以自然赋予 $\mathcal{O}_X$-模层结构，使得整个分解是 $\mathcal{O}_X$-模层的正合序列。

**证明思路**：
$C^0(\mathcal{F})(U) = \prod_{x \in U} \mathcal{F}_x$ 自然具有 $\mathcal{O}_X(U)$-模结构：对 $r \in \mathcal{O}_X(U)$ 和 $(s_x)_{x \in U}$，定义 $r \cdot (s_x) = (r_x s_x)$，其中 $r_x$ 是 $r$ 在 $x$ 处的芽。这赋予 $C^0(\mathcal{F})$ $\mathcal{O}_X$-模层结构。递归构造保持此结构。

因此，Godement 分解同样适用于环化空间上的模层上同调 $H^q(X, \mathcal{F})$，其结果与 Abel 群层上同调一致（当 $\mathcal{F}$ 是 Abel 群层时）。

---

## 15.7.5 层上同调作为导出函子 / Sheaf Cohomology as Derived Functors

### 整体截影函子 / Global Section Functor

**定义 15.7.3** (层上同调 / Sheaf Cohomology)
设 $X$ 是拓扑空间，$\mathcal{F} \in \mathbf{Ab}(X)$。$X$ 的系数在 $\mathcal{F}$ 中的**第 $q$ 个层上同调群**定义为

$$
H^q(X, \mathcal{F}) = R^q\Gamma(X, \mathcal{F})
$$

即整体截影函子 $\Gamma(X, -): \mathbf{Ab}(X) \to \mathbf{Ab}$ 的右导出函子。

**定理 15.7.7**
利用 Godement 分解，有：

$$
H^q(X, \mathcal{F}) = H^q(\Gamma(X, C^\bullet(\mathcal{F})))
$$

**证明**：
因 $C^\bullet(\mathcal{F})$ 是 $\mathcal{F}$ 的松软消解，而松软层是 $\Gamma(X, -)$-零调的（定理 15.7.1），根据导出函子的基本定理，可用任何零调消解计算导出函子。详见 Weibel [1, Theorem 10.5.6] 或 Godement [2, Théorème 4.4.1]。

### Čech上同调与导出上同调的关系 / Relation with Čech Cohomology

**定理 15.7.8** (Leray 定理)
设 $\mathcal{U} = \{U_i\}_{i \in I}$ 是 $X$ 的开覆盖。若对所有 $q > 0$ 和所有有限交 $U_{i_0 \cdots i_p}$ 有 $H^q(U_{i_0 \cdots i_p}, \mathcal{F}|_{U_{i_0 \cdots i_p}}) = 0$，则

$$
\check{H}^p(\mathcal{U}, \mathcal{F}) \cong H^p(X, \mathcal{F})
$$

**定义 15.7.4** (无环覆盖 / Acyclic Cover)
满足 Leray 定理条件的覆盖称为**无环覆盖**（acyclic cover）或**Leray 覆盖**。

**例子 15.7.1** (仿射概形上的拟凝聚层)
设 $X = \operatorname{Spec} A$ 是仿射概形，$\mathcal{F} = \widetilde{M}$ 是拟凝聚层。则 $X$ 的任何由主开集 $D(f_i)$ 构成的有限覆盖都是 Leray 覆盖。这是因为拟凝聚层在仿射开集上的层上同调为零（Serre 定理）。此时 Čech 上同调计算给出：

$$
H^p(X, \mathcal{F}) = 0 \quad (p > 0)
$$

这与导出函子的定义完全一致。

---

## 15.7.6 计算实例 / Computational Examples

**例子 15.7.2** ($X = \mathbb{R}$ 上的常值层)
设 $X = \mathbb{R}$（通常拓扑），$\underline{\mathbb{Z}}$ 是常值层。计算 $H^q(\mathbb{R}, \underline{\mathbb{Z}})$。

$\underline{\mathbb{Z}}$ 是松软层吗？不是，因为 $\underline{\mathbb{Z}}(\mathbb{R}) = \mathbb{Z}$，而对不连通开集 $U = (-\infty, 0) \cup (0, \infty)$，$\underline{\mathbb{Z}}(U) = \mathbb{Z}^2$，限制映射不是满射。

但我们知道 $\mathbb{R}$ 可缩，$H^q(\mathbb{R}, \underline{\mathbb{Z}}) = H^q_{\text{sing}}(\mathbb{R}; \mathbb{Z}) = \begin{cases} \mathbb{Z} & q = 0 \\ 0 & q > 0 \end{cases}$。

通过 Godement 分解，$C^0(\underline{\mathbb{Z}})$ 是松软层，$Z^1 = \operatorname{coker}(\underline{\mathbb{Z}} \to C^0(\underline{\mathbb{Z}}))$。可验证 $Z^1$ 也是松软的（因为 $\mathbb{R}$ 是局部紧、局部连通的）。因此 $H^1(\mathbb{R}, \underline{\mathbb{Z}}) = 0$。

**例子 15.7.3** ($S^1$ 上的常值层)
设 $X = S^1$，$\underline{\mathbb{Z}}$ 是常值层。利用开覆盖 $\mathcal{U} = \{U, V\}$，其中 $U, V$ 都是可缩开集且 $U \cap V$ 有两个连通分支。这是 Leray 覆盖（因为可缩开集上的常值层上同调平凡）。

Čech 复形为：

$$
C^0 = \mathcal{F}(U) \oplus \mathcal{F}(V) = \mathbb{Z} \oplus \mathbb{Z}
$$

$$
C^1 = \mathcal{F}(U \cap V) = \mathbb{Z}^2
$$

微分 $d: C^0 \to C^1$ 为 $(a, b) \mapsto (b-a, b-a)$。因此：

$$
\check{H}^0 = \ker(d) = \{(a, a)\} \cong \mathbb{Z}
$$

$$
\check{H}^1 = \operatorname{coker}(d) = \mathbb{Z}^2 / \langle(1,1)\rangle \cong \mathbb{Z}
$$

这与奇异上同调 $H^*(S^1; \mathbb{Z})$ 一致。

**例子 15.7.4** (复流形上的全纯函数层)
设 $X$ 是复流形，$\mathcal{O}_X$ 是全纯函数层。Cartan 定理 B 断言：若 $X$ 是 Stein 流形，则对任意凝聚解析层 $\mathcal{F}$，$H^q(X, \mathcal{F}) = 0$ 对 $q > 0$。这意味着 Stein 流形上的凝聚层上同调是高阶消失的，Godement 分解在此情形下提供了具体的零调消解。

---

## 15.7.7 参考文献 / References

### 经典教材 / Classical Textbooks

1. **C. A. Weibel**, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced Mathematics 38, Cambridge University Press, 1994.
   - 第10章：层上同调与 Godement 分解（第10.6节）

2. **R. Godement**, *Topologie algébrique et théorie des faisceaux*, Actualités Scientifiques et Industrielles 1252, Hermann, Paris, 1958.
   - 第II章 §3：松软层与内射层
   - 第II章 §4：Godement 分解的原始构造
   - 第II章 §4.3：层上同调作为导出函子

3. **R. Hartshorne**, *Algebraic Geometry*, Graduate Texts in Mathematics 52, Springer, 1977.
   - 第III章 §2：导出函子定义的层上同调
   - 第III章 §4：Čech 上同调与 Leray 定理

### 课程讲义 / Lecture Notes

4. **Oxford Mathematics**, *C2.2 Homological Algebra*, Michaelmas Term 2024/25.
   - Lecture 27-28: 松软层与 Godement 分解
   - Lecture 29: 层上同调的导出函子定义与 Čech 上同调

### 在线资源 / Online Resources

5. **Stacks Project**, Tag 01D9 — Flabby Sheaves, Chapter 20.
   - `https://stacks.math.columbia.edu/tag/01D9[需更新[需更新]]`

6. **Stacks Project**, Tag 01DF — Godement Resolution, Chapter 20.
   - `https://stacks.math.columbia.edu/tag/01DF[需更新[需更新]]`

7. **Stacks Project**, Tag 01E1 — Cohomology of Sheaves as Derived Functors.
   - `https://stacks.math.columbia.edu/tag/01E1[需更新[需更新]]`

### 中文参考 / Chinese References

8. **李克正**，《同调代数基础》，科学出版社，1996.
   - 第7章：层上同调基础

9. **陈志杰**，《同调代数》，北京大学出版社，2006.
   - 第9章：Godement 分解与松软层

---

## 补充内容：Godement分解与其他消解的比较 / Supplement: Godement vs. Other Resolutions

### 软层消解与Godement分解 / Soft Resolution and Godement

**定义 15.7.4** (软层 / Soft Sheaf)
设 $X$ 是仿紧（paracompact）Hausdorff 空间。层 $\mathcal{F}$ 称为**软的**（soft），如果对任意闭集 $K \subseteq X$，限制映射 $\mathcal{F}(X) \to \mathcal{F}(K)$ 是满射。这里 $\mathcal{F}(K) = \varinjlim_{U \supset K} \mathcal{F}(U)$。

**定理 15.7.8**
在仿紧 Hausdorff 空间上，软层是 $\Gamma(X, -)$-零调的。且任何层都可以嵌入到软层中。

**比较**：
- 松软层（flabby）不要求 $X$ 仿紧，但软层要求
- 在仿紧空间上，松软层都是软层
- Godement 分解产生的是松软层，因此适用于任意拓扑空间
- 在微分几何中，光滑函数的精细层（fine sheaves）是软层，常用于 de Rham 定理的证明

### Godement分解与fine层 / Godement Resolution and Fine Sheaves

**定义 15.7.5** (精细层 / Fine Sheaf)
设 $X$ 是仿紧空间。层 $\mathcal{F}$ 称为**精细的**，如果 $\operatorname{\mathcal{H}om}(\mathcal{F}, \mathcal{F})$ 有足够多的单位分解。即对任意局部有限开覆盖，存在层自同态的分解 $1 = \sum \rho_i$ 使得 $\rho_i$ 在覆盖外为零。

**定理 15.7.9**
在微分流形上，光滑微分形式层 $\mathcal{A}^q_X$ 是精细层，因此是软层，也是零调的。这给出了 de Rham 消解：

$$
0 \longrightarrow \underline{\mathbb{R}}_X \longrightarrow \mathcal{A}^0_X \longrightarrow \mathcal{A}^1_X \longrightarrow \mathcal{A}^2_X \longrightarrow \cdots
$$

**de Rham 定理**：对光滑流形 $X$，

$$
H^q_{\mathrm{dR}}(X) \cong H^q(X, \underline{\mathbb{R}}_X)
$$

Godement 分解提供了这一同构的另一种证明路径：因为 $\underline{\mathbb{R}}_X$ 的 Godement 分解和 de Rham 消解都是零调的，它们在导出范畴中给出同构的对象，从而诱导同调同构。

### Godement分解在复几何中的角色 / Godement Resolution in Complex Geometry

**定理 15.7.10** ($\bar{\partial}$-Poincaré 引理)
设 $X$ 是复流形，$\mathcal{O}_X$ 是全纯函数层。则序列

$$
0 \longrightarrow \mathcal{O}_X \longrightarrow \mathcal{A}^{0,0}_X \xrightarrow{\bar{\partial}} \mathcal{A}^{0,1}_X \xrightarrow{\bar{\partial}} \mathcal{A}^{0,2}_X \longrightarrow \cdots
$$

是正合的。这称为 Dolbeault 消解。

因为 $\mathcal{A}^{p,q}_X$ 是精细层（当 $X$ 是仿紧时），Dolbeault 定理给出：

$$
H^q(X, \Omega^p_X) \cong H^{p,q}_{\bar{\partial}}(X)
$$

Godement 分解再次提供了这一结果的导出函子视角：$H^q(X, \Omega^p_X)$ 作为层上同调群，可以用 Godement 分解或 Dolbeault 消解计算，结果自然同构。

### 直接像函子的Godement分解 / Godement Resolution for Direct Image Functors

**定理 15.7.11**
设 $f: X \to Y$ 是连续映射，$\mathcal{F}$ 是 $X$ 上的层。则对 $Y$ 的任意开集 $V$，

$$
(R^q f_* \mathcal{F})(V) = H^q(f^{-1}(V), \mathcal{F}|_{f^{-1}(V)})

$$

若 $C^\bullet(\mathcal{F})$ 是 $\mathcal{F}$ 的 Godement 分解，则 $f_* C^\bullet(\mathcal{F})$ 计算 $Rf_* \mathcal{F}$。这是因为 $C^q(\mathcal{F})$ 是松软层，而松软层的直接像 $f_* C^q(\mathcal{F})$ 仍是松软层（从而零调）。因此 Godement 分解也是计算高阶直接像函子的有效工具。

**例子 15.7.5** (投影的 Leray 谱序列)
设 $f: X \times Y \to Y$ 是投影。对 $X \times Y$ 上的层 $\mathcal{F}$，Godement 分解给出计算 $R^q f_* \mathcal{F}$ 的具体复形。当 $X$ 是紧的，$\mathcal{F}$ 是局部常值层时，$R^q f_* \mathcal{F}$ 是 $Y$ 上的局部系，其茎为 $H^q(X, \mathcal{F}|_{X \times \{y\}})$。这在族的上同调研究中至关重要。

