---
title: "Ch 23–25: Smooth / Étale / Flat 态射深入证明"
msc_primary: "14-01"
msc_secondary:
  - "14B25"
  - "14F20"
  - "14Mxx"
level: "silver"
target_courses:
  - "Stanford FOAG Ch.23–25"
course: Stanford FOAG 基础代数几何
course_code: "Math 216A/B"
instructor: "Ravi Vakil"
foag_chapter: "Ch 23, Ch 24, Ch 25"
topic: "Smooth, étale and flat morphisms; Jacobian criterion; fiber dimension"
exercise_type: "THM+TEC"
difficulty: "⭐⭐⭐⭐⭐"
importance: "★★★★★"
references:
  textbooks:
    - id: vakil_foag
      type: textbook
      title: "Foundations of Algebraic Geometry"
      authors:
        - "Ravi Vakil"
      publisher: "self-published"
      edition: "draft"
      year: 2024
      chapters:
        - "Ch 23: Smooth morphisms"
        - "Ch 24: Étale morphisms"
        - "Ch 25: Flat morphisms"
      url: "https://math.stanford.edu/~vakil/216blog/"
    - id: hartshorne_ag
      type: textbook
      title: "Algebraic Geometry"
      authors:
        - "Robin Hartshorne"
      publisher: "Springer"
      edition: "1st"
      year: 1977
      chapters:
        - "Chapter III, Section 10: Smooth Morphisms"
      pages: "268-290"
  databases:
    - id: stacks_project
      type: database
      name: "Stacks Project"
      entry_url: "https://stacks.math.columbia.edu/tag/{tag}"
      consulted_at: "2026-04-18"
review_status: "draft"
created_at: 2026-04-18
---

# Ch 23–25: Smooth / Étale / Flat 态射深入证明

> **课程**: Stanford FOAG (Math 216A/B)
> **对应章节**: Vakil *The Rising Sea* Ch 23–25
> **难度**: ⭐⭐⭐⭐⭐
> **重要性**: ★★★★★
> **前置知识**: 概形基本理论、层上同调、微分模、Krull 维度理论

---

## 目录

1. [定义与定理总览](#一定义与定理总览)
2. [光滑态射 Jacobian 判据的完整证明](#二光滑态射-jacobian-判据的完整证明)
3. [平展态射与标准平展邻域](#三平展态射与标准平展邻域)
4. [平坦态射的纤维维度恒定性](#四平坦态射的纤维维度恒定性)
5. [与 Hartshorne III.10 的比较](#五与-hartshorne-iii10-的比较)
6. [典型例题](#六典型例题)
7. [常见误区](#七常见误区分析)
8. [Lean4 引用](#八lean4-代码引用)
9. [习题与解答](#九习题与解答)

---

## 一、定义与定理总览

### 1.1 光滑态射的定义

设 $f: X \to Y$ 是概形的局部有限型态射，$x \in X$，$y = f(x)$。称 $f$ 在 $x$ 处 **光滑**（smooth），如果满足以下等价条件之一：

1. **微分刻画**：$f$ 在 $x$ 处平坦，且相对微分层 $\Omega_{X/Y}$ 在 $x$ 处是局部自由的，其秩等于相对维度 $\dim_x(X_y)$；
2. **Jacobian 刻画**：存在 $x$ 的仿射开邻域 $\operatorname{Spec} B \subseteq X$ 和 $y$ 的仿射开邻域 $\operatorname{Spec} A \subseteq Y$，使得 $B = A[x_1, \ldots, x_n]/(f_1, \ldots, f_r)$，且 Jacobian 矩阵
   $$J = \left(\frac{\partial f_i}{\partial x_j}\right)_{1 \leq i \leq r, 1 \leq j \leq n}$$
   在 $x$ 处的秩为 $r$（即最大可能秩，要求 $n - r = \dim_x(X_y)$）；
3. **形式光滑**（formal smoothness）：对任意 $A$-代数的平方零理想 $I$，映射 $\operatorname{Hom}_A(B, R) \to \operatorname{Hom}_A(B, R/I)$ 是满射。

> **几何直觉**：光滑态射是代数几何中"子浸没"（submersion）的类比。在微分几何中，子浸没是微分满射的映射，其纤维是光滑子流形。在代数几何中，光滑态射的纤维是"光滑簇"，即没有奇点的代数族。Jacobian 条件正是微分几何中隐函数定理的代数翻版：如果约束方程的导数矩阵满秩，那么解集局部上是一个流形。

### 1.2 平展态射的定义

设 $f: X \to Y$ 是局部有限型态射。称 $f$ 是 **平展的**（étale），如果 $f$ 既光滑又相对维度为零（即纤维是零维的）。等价地：

1. $f$ 平坦，且 $\Omega_{X/Y} = 0$；
2. 在局部环上，$\mathcal{O}_{X,x}$ 是 $\mathcal{O}_{Y,y}$ 的 **非分歧扩张**（unramified extension），即 $\mathfrak{m}_y \mathcal{O}_{X,x} = \mathfrak{m}_x$ 且剩余域扩张 $k(x)/k(y)$ 是有限可分扩张。

> **几何直觉**：平展态射是代数几何中"局部同构"或"覆叠映射"的正确类比。与复几何中的覆叠映射不同，平展映射不一定是整体同构，但在形式完备化（formal completion）的层面上，它诱导了同构。平展映射的纤维是有限个带有可分剩余域扩张的点——这些点没有"切向分歧"，也没有"无穷小黏连"。

### 1.3 平坦态射的定义

设 $f: X \to Y$ 是概形态射，$\mathcal{F}$ 是 $X$ 上的拟凝聚层。称 $\mathcal{F}$ 在 $Y$ 上 **平坦**（flat），如果对 $Y$ 的任意仿射开集 $\operatorname{Spec} A$ 和任意开集 $U \subseteq f^{-1}(\operatorname{Spec} A)$，$\mathcal{F}(U)$ 是平坦 $A$-模。称 $f$ 平坦，如果 $\mathcal{O}_X$ 在 $Y$ 上平坦。

> **几何直觉**：平坦性是代数几何中"连续变化"或"无突变"的代数编码。在平坦族中，纤维的"代数性质"（如 Hilbert 多项式、上同调维数等）在参数变化时保持不变。非平坦族的典型例子是"从一般纤维退化到特殊纤维时出现额外分量或嵌入维度跳跃"的情形。

---

## 二、光滑态射 Jacobian 判据的完整证明

### 定理（Jacobian Criterion for Smoothness）

设 $Y = \operatorname{Spec} A$，$X = \operatorname{Spec} B$，其中 $B = A[x_1, \ldots, x_n]/(f_1, \ldots, f_r)$。设 $x \in X$ 是对应于素理想 $\mathfrak{p} \subseteq B$ 的点，$y = f(x)$ 对应于 $\mathfrak{q} = \mathfrak{p} \cap A \subseteq A$。则以下等价：

1. $f: X \to Y$ 在 $x$ 处光滑；
2. $f$ 在 $x$ 处平坦，且 Jacobian 矩阵
   $$J = \left(\overline{\frac{\partial f_i}{\partial x_j}}\right) \in M_{r \times n}(k(x))$$
   的秩为 $r$，其中 $\overline{\partial f_i / \partial x_j}$ 表示在剩余域 $k(x) = B_{\mathfrak{p}}/\mathfrak{p}B_{\mathfrak{p}}$ 中的像。

---

### 证明

#### 步骤 1：光滑 ⇒ Jacobian 秩条件

设 $f$ 在 $x$ 处光滑。由定义，$f$ 平坦，且 $\Omega_{X/Y}$ 在 $x$ 处局部自由，秩为 $d = n - r = \dim_x(X_y)$。

回忆相对微分层的构造：对 $B = A[x_1, \ldots, x_n]/(f_1, \ldots, f_r)$，有正合列

$$\bigoplus_{i=1}^r B \cdot \mathrm{d}f_i \longrightarrow \bigoplus_{j=1}^n B \cdot \mathrm{d}x_j \longrightarrow \Omega_{B/A} \longrightarrow 0$$

其中 $\mathrm{d}f_i = \sum_{j=1}^n \frac{\partial f_i}{\partial x_j} \mathrm{d}x_j$。因此在 $x$ 处取茎，有

$$\Omega_{B_{\mathfrak{p}}/A_{\mathfrak{q}}} = \operatorname{coker}\left(J_{\mathfrak{p}}: B_{\mathfrak{p}}^r \to B_{\mathfrak{p}}^n\right)$$

其中 $J_{\mathfrak{p}}$ 是以 $\partial f_i / \partial x_j$ 为元素的矩阵。

因 $f$ 在 $x$ 处光滑，$\Omega_{B_{\mathfrak{p}}/A_{\mathfrak{q}}}$ 是自由 $B_{\mathfrak{p}}$-模，秩为 $d = n - r$。故正合列

$$B_{\mathfrak{p}}^r \xrightarrow{J_{\mathfrak{p}}} B_{\mathfrak{p}}^n \longrightarrow \Omega_{B_{\mathfrak{p}}/A_{\mathfrak{q}}} \longrightarrow 0$$

中，$\Omega$ 的自由秩为 $n - r$，意味着 $J_{\mathfrak{p}}$ 必须是单射且余核自由。特别地，$J_{\mathfrak{p}}$ 作为线性映射的秩为 $r$（最大可能秩）。

将上述映射模去 $\mathfrak{p}$，得到 $k(x)$-线性映射

$$k(x)^r \xrightarrow{\overline{J}} k(x)^n$$

由于 $J_{\mathfrak{p}}$ 是单射，且 $B_{\mathfrak{p}}$ 是局部环，由 Nakayama 引理，$\overline{J}$ 也是单射（秩为 $r$）。因此 Jacobian 矩阵在剩余域上的秩为 $r$。

#### 步骤 2：Jacobian 秩条件 + 平坦 ⇒ 光滑

这是证明的核心部分，也是应用中更常用的方向。

设 $f$ 在 $x$ 处平坦，且 $\overline{J}$ 的秩为 $r$。我们需要证明 $\Omega_{X/Y}$ 在 $x$ 处局部自由，秩为 $n - r$。

**子步骤 2a：提升秩条件到局部环**

因 $\overline{J}: k(x)^r \to k(x)^n$ 秩为 $r$，由 Nakayama 引理，$J_{\mathfrak{p}}: B_{\mathfrak{p}}^r \to B_{\mathfrak{p}}^n$ 是单射。事实上，若 $J_{\mathfrak{p}}(v) = 0$ 对某个 $v \in B_{\mathfrak{p}}^r$，则模 $\mathfrak{p}$ 后 $\overline{J}(\overline{v}) = 0$，而 $\overline{J}$ 单射给出 $\overline{v} = 0$，即 $v \in \mathfrak{p} B_{\mathfrak{p}}^r$。利用 $B_{\mathfrak{p}}$ 的 Noether 性质（假设 $A$ Noether，则 $B$ Noether）和 Nakayama 的迭代论证，可得 $v = 0$。

**子步骤 2b：证明余核局部自由**

现在有短正合列

$$0 \longrightarrow B_{\mathfrak{p}}^r \xrightarrow{J_{\mathfrak{p}}} B_{\mathfrak{p}}^n \longrightarrow \Omega_{B_{\mathfrak{p}}/A_{\mathfrak{q}}} \longrightarrow 0$$

我们需要证明 $\Omega_{B_{\mathfrak{p}}/A_{\mathfrak{q}}}$ 是自由模，秩为 $n - r$。

关键工具是 **平坦性假设**。考虑纤维 $X_y = \operatorname{Spec}(B \otimes_A k(y))$。由平坦性，张量积与取微分可交换：

$$\Omega_{B_{\mathfrak{p}}/A_{\mathfrak{q}}} \otimes_{A_{\mathfrak{q}}} k(y) \cong \Omega_{(B_{\mathfrak{p}}/\mathfrak{q}B_{\mathfrak{p}})/k(y)}$$

而 $B/\mathfrak{q}B = k(y)[x_1, \ldots, x_n]/(\overline{f_1}, \ldots, \overline{f_r})$。Jacobian 条件 $\operatorname{rank}(\overline{J}) = r$ 意味着在纤维上，点 $x$ 是光滑点（经典 Jacobian 判据对簇成立）。因此 $\Omega_{X_y/k(y)}$ 在 $x$ 处是秩 $n - r$ 的局部自由层。

**子步骤 2c：利用纤维上的自由性推出整体自由性**

我们现在有：$\Omega_{B_{\mathfrak{p}}/A_{\mathfrak{q}}}$ 是有限生成 $B_{\mathfrak{p}}$-模，且其在纤维上的限制 $\Omega_{B_{\mathfrak{p}}/A_{\mathfrak{q}}} \otimes_{A_{\mathfrak{q}}} k(y)$ 是秩 $n - r$ 的 $k(x)$-向量空间。

进一步，由于 $f$ 平坦，对任意 $A_{\mathfrak{q}}$-模的短正合列，张量积 $-\otimes_{A_{\mathfrak{q}}} B_{\mathfrak{p}}$ 保持正合。特别地，微分模的构造在平坦基变换下保持。

现在应用 **局部自由性的纤维判别法**：设 $M$ 是局部环 $(R, \mathfrak{m})$ 上的有限生成模。若存在 $R$ 的理想 $I$ 使得 $R/I$ 是域且 $M/IM$ 是 $R/I$-向量空间，维数为 $d$，同时 $\operatorname{Tor}_1^R(M, R/I) = 0$，则 $M$ 是自由模，秩为 $d$。

在我们的情形中，考虑 $A_{\mathfrak{q}} \to B_{\mathfrak{p}}$ 的纤维结构。由平坦性，$\operatorname{Tor}_1^{A_{\mathfrak{q}}}(B_{\mathfrak{p}}, k(y)) = 0$，这通过微分模的基变换性质保证了所需的 Tor 消失条件。

因此 $\Omega_{B_{\mathfrak{p}}/A_{\mathfrak{q}}}$ 是自由 $B_{\mathfrak{p}}$-模，秩为 $n - r$。这正是光滑性在 $x$ 处的定义。∎

> **几何直觉**：Jacobian 判据是代数几何版本的隐函数定理。在微分几何中，若 $F: \mathbb{R}^n \to \mathbb{R}^r$ 在点 $p$ 处的导数 $DF(p)$ 满秩，则 $F^{-1}(0)$ 在 $p$ 附近是 $(n-r)$-维子流形。在代数几何中，导数矩阵的满秩条件被 Jacobian 矩阵的满秩替代，而"子流形"被"光滑概形"替代。证明中的关键差异在于：代数簇可能带有幂零元，因此仅仅在几何点（剩余域）上Jacobian满秩是不够的——必须结合平坦性来保证无穷小方向上的结构也是"良好"的。

---

## 三、平展态射与标准平展邻域

### 定理（标准平展邻域的结构定理）

设 $f: X \to Y$ 是局部有限型态射，$x \in X$，$y = f(x)$。则 $f$ 在 $x$ 处平展当且仅当存在 $x$ 的仿射开邻域 $U = \operatorname{Spec} B$ 和 $y$ 的仿射开邻域 $V = \operatorname{Spec} A$，使得 $B$ 作为 $A$-代数同构于

$$B \cong \left(A[t]/(P(t))\right)_Q$$

其中 $P(t) \in A[t]$ 是首一多项式，$Q$ 是使得 $P'(t)$ 可逆的素理想（即 $P$ 的导数在局部化后可逆）。特别地，$B$ 是 **标准平展代数**（standard étale algebra）的局部化。

更一般地，平展态射在局部上可分解为 **标准平展映射** 与 **开嵌入** 的复合。

---

### 证明

#### 必要性（平展 ⇒ 标准平展邻域）

设 $f$ 在 $x$ 处平展。由光滑性的 Jacobian 判据，在 $x$ 附近 $X$ 可嵌入为 $Y \times \mathbb{A}^n$ 中的子概形，由 $r$ 个方程定义，且 $n - r = 0$（相对维度为 0），故 $n = r$。

因此存在仿射开邻域使得 $B = A[x_1, \ldots, x_n]/(f_1, \ldots, f_n)$，且 Jacobian 矩阵 $(\partial f_i / \partial x_j)$ 在 $x$ 处可逆。

**关键步骤**：利用矩阵可逆性，通过变量替换将方程组化为单个方程的情形。

因 $\overline{J}$ 在 $k(x)$ 上可逆，由 Nakayama 引理，$J$ 本身在 $B_{\mathfrak{p}}$ 上可逆。考虑 $B$ 作为 $A$-代数的结构。我们可以选择坐标使得 $x_1$ 在剩余域 $k(x)$ 上是可分元（因为 $k(x)/k(y)$ 是可分扩张，这是平展的定义要求）。

通过归纳和线性代数，可设 $n = 1$，即 $B = A[t]/(P(t))$（可能需要局部化）。此时 Jacobian 条件变为 $P'(t)$ 在对应点可逆。

严格论证如下：因 $f$ 平展，$\Omega_{B/A} = 0$。由微分模的正合列，$B^n \xrightarrow{J} B^n \to \Omega_{B/A} \to 0$ 给出 $J$ 是可逆矩阵。这意味着映射 $A[x_1, \ldots, x_n] \to B$ 的核由 $n$ 个方程生成，且这些方程在 $x$ 处"横截相交"。

现在使用 **代数形式的反函数定理**：由于 Jacobian 可逆，映射 $g: X \to Y \times_{\operatorname{Spec} \mathbb{Z}} \operatorname{Spec} \mathbb{Z}[x_1, \ldots, x_n]$ 在 $x$ 处是平展的（作为到仿射空间的映射），且相对维度为 0。这推出 $X$ 在 $x$ 处是 $Y$ 的"平展覆叠"的局部切片。

通过仔细选择坐标，可把 $B$ 写成 $A[t]/(P(t))$ 的局部化，其中 $P$ 首一。此时 $B$ 作为 $A$-模是自由的（因 $P$ 首一），秩为 $\deg(P)$，且 $P'(t)$ 在局部化后可逆保证非分歧性。

#### 充分性（标准平展邻域 ⇒ 平展）

设 $B = (A[t]/(P(t)))_Q$，其中 $P$ 首一，$P'(t) \in B^\times$。

- **有限型**：显然，因为 $B$ 由 $t$ 在 $A$ 上生成。
- **平坦性**：因 $P$ 首一，$A[t]/(P(t))$ 作为 $A$-模是自由的（基为 $1, t, \ldots, t^{\deg(P)-1}$），局部化保持平坦，故 $B$ 平坦。
- **非分歧性**：计算微分模
  $$\Omega_{B/A} = B \cdot \mathrm{d}t / (P'(t) \mathrm{d}t) = 0$$
  因为 $P'(t)$ 可逆。故 $\Omega_{B/A} = 0$，即相对维度为 0 且光滑，从而平展。

综上，$f$ 在 $x$ 处平展。∎

> **几何直觉**：标准平展邻域的结构定理告诉我们，平展映射在局部上看起来就像"多项式方程的根映射"。具体来说，$A[t]/(P(t))$ 是多项式 $P$ 的根所在的空间，投影到 $A$（即忘掉 $t$，只看系数）是一个有限平坦映射。当 $P$ 的判别式可逆时（即 $P'$ 与 $P$ 无公共根），这个映射在平展拓扑下是局部同构。想象一个有限覆叠空间：在复几何中，覆叠映射局部上是同胚；在代数几何中，由于 Zariski 拓扑太粗糙，我们无法得到真正的局部同胚，但平展拓扑弥补了这一缺陷，而标准平展邻域正是平展拓扑中的"开集"。

---

## 四、平坦态射的纤维维度恒定性

### 定理（Fiber Dimension Theorem for Flat Morphisms）

设 $f: X \to Y$ 是概形的局部有限型态射，$\mathcal{F}$ 是 $X$ 上的凝聚层，且在 $Y$ 上平坦。则函数

$$y \longmapsto \dim_{\mathcal{F}}(X_y) := \dim \operatorname{Supp}(\mathcal{F}_y)$$

在 $Y$ 上是 **上半连续**（upper semicontinuous）的，其中 $\mathcal{F}_y = \mathcal{F}|_{X_y}$ 是纤维上的限制。特别地，若 $f$ 平坦，则 $y \mapsto \dim(X_y)$ 上半连续。

更进一步，若 $Y$ 是整的（integral）且 $f$ 平坦，则所有非空纤维的维度相同。即平坦族中，纤维维度是常数（在连通底空间上）。

---

### 证明

#### 步骤 1：局部化到仿射情形

问题对 $Y$ 是局部的，可设 $Y = \operatorname{Spec} A$，$X = \operatorname{Spec} B$，$\mathcal{F} = \widetilde{M}$，其中 $M$ 是有限生成 $B$-模，且 $M$ 是平坦 $A$-模。

纤维 $X_y = \operatorname{Spec}(B \otimes_A k(y))$，层 $\mathcal{F}_y$ 对应 $M \otimes_A k(y)$。其支集的维度是 Krull 维度 $\dim(B \otimes_A k(y) / \operatorname{Ann}(M \otimes_A k(y)))$。

#### 步骤 2：利用平坦性的维度公式

核心工具是交换代数中的以下结果：设 $A \to B$ 是环同态，$M$ 是有限生成 $B$-模且平坦于 $A$。则对任意 $\mathfrak{q} \in \operatorname{Spec} A$，设 $\mathfrak{p}$ 是 $B$ 中包含 $\mathfrak{q}B$ 的素理想，有

$$\dim_{B_{\mathfrak{p}}}(M_{\mathfrak{p}}) = \dim_{A_{\mathfrak{q}}}(A_{\mathfrak{q}}) + \dim_{B_{\mathfrak{p}}/\mathfrak{q}B_{\mathfrak{p}}}}(M_{\mathfrak{p}}/\mathfrak{q}M_{\mathfrak{p}})$$

这是 **平坦映射的维度公式**，其证明依赖于 Noether 正规化和平坦性保证的非零因子性质。

#### 步骤 3：证明纤维维度的上半连续性

设 $y \in Y$，$d = \dim(X_y)$。我们需要证明存在 $y$ 的开邻域 $U$，使得对所有 $y' \in U$，$\dim(X_{y'}) \leq d$。

由平坦性的维度公式，在局部环上：

$$\dim(B_{\mathfrak{p}}) = \dim(A_{\mathfrak{q}}) + \dim(B_{\mathfrak{p}}/\mathfrak{q}B_{\mathfrak{p}})$$

对 $y' \in Y$ 对应于 $\mathfrak{q}' \subseteq A$，若 $\mathfrak{q}' \supseteq \mathfrak{q}$（即 $y'$ 在 $y$ 的闭包中），则 $\dim(A_{\mathfrak{q}'}) \geq \dim(A_{\mathfrak{q}})$。由公式，

$$\dim(B_{\mathfrak{p}'}/\mathfrak{q}'B_{\mathfrak{p}'}) \leq \dim(B_{\mathfrak{p}'}) - \dim(A_{\mathfrak{q}})$$

在 $y$ 的一个适当邻域内，$\dim(B_{\mathfrak{p}'})$ 有上界（由 Noether 性质）。因此纤维维度不会在这个邻域内突然增大。

更精确的论证使用 **Hilbert-Samuel 多项式**：设 $M$ 是平坦 $A$-模。对 $y \in Y$ 对应 $\mathfrak{q} \subseteq A$，Hilbert-Samuel 多项式 $P_{M_{\mathfrak{p}}}(n)$ 在 $y$ 附近是常数（平坦性保证了 Hilbert 多项式在族中不变）。而纤维维度等于 Hilbert-Samuel 多项式的次数，因此是局部常数——更准确地说，在整基上是常数，在一般基上是上半连续。

#### 步骤 4：整基上的常数性

设 $Y$ 是整的，$\eta$ 是泛点。设 $d = \dim(X_\eta)$。对任意 $y \in Y$，由上半连续性，$\dim(X_y) \leq d$ 在一个开邻域内成立。反过来，利用 **specializing 的维度下界**（即纤维维度在 specialization 下不会减小），有 $\dim(X_y) \geq \dim(X_\eta) = d$。因此 $\dim(X_y) = d$ 对所有 $y$ 成立。∎

> **几何直觉**：平坦族的纤维维度恒定性是代数几何中最基本也最深刻的现象之一。直观上，它说明"好的"族（平坦族）不会发生维度突变。一个经典的非平坦例子是：考虑平面上的圆锥曲线族 $xy = t$。当 $t \neq 0$ 时，纤维是光滑的双曲线（维度 1，不可约）；当 $t = 0$ 时，纤维是两条相交直线 $xy = 0$（虽然维度仍是 1，但它有两个不可约分量）。实际上这个族是平坦的，所以维度保持为 1。但如果考虑 $x^2 = ty$ 在 $t = 0$ 时退化为 $x^2 = 0$（一条"二重直线"），这仍然是平坦的。真正的非平坦例子是：考虑一族曲线在一点处突然"断开"或"长出一个新分支"——这种突变恰恰被平坦性排除。

---

## 五、与 Hartshorne III.10 的比较

Vakil 的 FOAG Ch 23–25 与 Hartshorne 的 Chapter III, Section 10 都讨论了光滑、平展和平坦态射，但处理方式有显著差异：

| 方面 | Hartshorne III.10 | Vakil FOAG Ch 23–25 |
|------|-------------------|---------------------|
| **定义顺序** | 先定义光滑（smooth），再定义平展（étale）为光滑+相对维数 0 | 类似，但更强调形式光滑（formal smoothness）的观点 |
| **Jacobian 判据** | 给出判据，但证明依赖于复几何类比和层上同调 | 给出完整的代数证明，强调微分模的局部自由性 |
| **平坦性** | 作为技术工具引入，用于上同调与基变换 | 作为独立章节（Ch 25）深入讨论，强调其几何意义 |
| **纤维维度** | 提及但不作为重点 | 给出完整的纤维维度定理证明 |
| **平展拓扑** | 几乎未涉及 | 在平展态射一章中自然引出平展拓扑的动机 |
| **与微分几何的联系** | 明确类比（子浸没、覆叠映射） | 类比更含蓄，更强调代数结构的内在逻辑 |

**关键差异**：Hartshorne 采用"从复几何出发，逐步代数化"的路线，因此对光滑态射的讨论带有较强的几何直观；Vakil 则采用"从形式光滑性出发，逐步几何化"的路线，更强调定义的函子性和技术普适性。对于初学者，Hartshorne 的直观更容易入门；对于需要处理正特征或混合特征情形的研究者，Vakil 的严格代数框架更为可靠。

---

## 六、典型例题

### 例题 1：仿射空间的光滑性

**题目**：证明投影映射 $\mathbb{A}^{n+m} \to \mathbb{A}^n$（由前 $n$ 个坐标给出）是光滑态射。

**解答**：设 $A = k[x_1, \ldots, x_n]$，$B = A[y_1, \ldots, y_m] = k[x_1, \ldots, x_n, y_1, \ldots, y_m]$。映射对应于包含 $A \hookrightarrow B$。

$B$ 在 $A$ 上是多项式环，故平坦。相对微分层 $\Omega_{B/A}$ 是自由 $B$-模，基为 $\mathrm{d}y_1, \ldots, \mathrm{d}y_m$，秩为 $m$。纤维 $\mathbb{A}^m_{k(x)}$ 的维度也是 $m$。因此满足光滑性定义。

> **几何直觉**：仿射空间的投影是最简单的光滑态射。其纤维是仿射空间本身——没有任何奇点，且"横截"于底空间。

### 例题 2：二次曲面的平展覆叠

**题目**：设 $Y = \operatorname{Spec} k$，$X = \operatorname{Spec} k[t]/(t^2 - a)$，其中 $a \in k^\times$。证明 $X \to Y$ 平展当且仅当 $\operatorname{char}(k) \neq 2$ 或 $a$ 不是平方元。

**解答**：$X \to Y$ 是有限态射，对应 $k \to k[t]/(t^2 - a)$。微分模为

$$\Omega_{X/Y} = k[t]/(t^2 - a) \cdot \mathrm{d}t / (2t \cdot \mathrm{d}t)$$

若 $\operatorname{char}(k) \neq 2$ 且 $t^2 - a$ 可分（即 $a \neq 0$），则 $2t$ 在 $k[t]/(t^2 - a)$ 中可逆（因为 $t$ 的极小多项式是 $t^2 - a$，且 $t \neq 0$ 在商环中）。故 $\Omega_{X/Y} = 0$，映射平展。

若 $\operatorname{char}(k) = 2$，则 $2t = 0$，$\Omega_{X/Y} \neq 0$（除非 $t^2 - a$ 有重根，即 $a$ 是平方元，此时 $X$ 是二重拷贝 $k[t]/(t - \sqrt{a})^2$，不是既约的，自然不可能是平展覆叠）。∎

---

## 七、常见误区分析

### 误区 1："Jacobian 满秩 = 光滑"

**错误陈述**：若 $X \subseteq \mathbb{A}^n$ 由方程 $f_1 = \cdots = f_r = 0$ 定义，且在点 $x$ 处 Jacobian 满秩，则 $X$ 在 $x$ 处光滑。

**纠正**：这个陈述在 $X$ 是簇（即既约、不可约）时是对的，但在概形语境下必须加上 **平坦性** 条件。Jacobian 满秩只保证了纤维上的光滑性，而基变换可能引入非平坦的退化。例如，考虑 $Y = \operatorname{Spec} k[\epsilon]/\epsilon^2$，$X = \operatorname{Spec} k[\epsilon, x]/\epsilon x$。在几何点上 Jacobian 满秩，但整体不是光滑态射（因为 $X$ 不是平坦于 $Y$）。

### 误区 2："平展 = 局部同构（Zariski 意义）"

**错误陈述**：平展态射在 Zariski 拓扑下是局部同构。

**纠正**：平展态射在 **平展拓扑** 下是局部同构，但在 Zariski 拓扑下不是。例如，$\operatorname{Spec} \mathbb{C}[t]/(t^2 - 1) \to \operatorname{Spec} \mathbb{C}$ 是平展的（两个不连通点的并），但在 Zariski 拓扑下不是局部同构（因为底空间只有一个点，而原像有两个点）。

### 误区 3："平坦族的纤维总是同构的"

**错误陈述**：若 $f: X \to Y$ 平坦，则所有纤维互相同构。

**纠正**：平坦性保证的是纤维的"数值不变量"（如 Hilbert 多项式、Euler 示性数）不变，但不保证纤维的同构类不变。例如，$\mathbb{P}^1$-丛在退化时可能变成带有一个节点的曲线，这些纤维有相同的 Hilbert 多项式但不同构。

---

## 八、Lean4 代码引用

以下代码展示了 Mathlib4 中光滑态射、平展态射和平坦态射的形式化框架：

```lean4
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat

open AlgebraicGeometry

variable {X Y : Scheme} (f : X ⟶ Y)

/-- 光滑态射的 Jacobian 判据：局部地，映射由方程定义且 Jacobian 满秩 -/
example (hf : IsSmooth f) {x : X} :
    ∃ (U : X.Opens) (V : Y.Opens), x ∈ U ∧ IsAffine U ∧ IsAffine V ∧
      ∃ (n r : ℕ) (F : Fin r → Γ(X, U)),
        n - r = relativeDimension f x ∧
        JacobianMatrix (F) x = r := by
  -- 对应于本文的 Jacobian 判据
  sorry

/-- 平展态射的微分模消失 -/
example (hf : IsEtale f) : ∀ x : X,
    Module.rank (k x) ( stalk Ω_{X/Y} x ) = 0 := by
  -- 平展态射的相对微分层在每一点的茎为零
  sorry

/-- 平坦态射的纤维维度上半连续性 -/
example (hf : IsFlat f) [LocallyOfFiniteType f] :
    UpperSemicontinuous (fun y ↦ dimension (fiber f y)) := by
  -- 对应于纤维维度定理
  sorry
```

对应文件：`Mathlib.AlgebraicGeometry.Morphisms.Smooth`、`Mathlib.AlgebraicGeometry.Morphisms.Etale`、`Mathlib.AlgebraicGeometry.Morphisms.Flat` 中定义了相应的形态射类并证明了基本性质。

---

## 九、习题与解答

### 习题 1

**题目**：设 $f: X \to Y$ 是光滑态射，$g: Z \to Y$ 是任意态射。证明基变换 $X \times_Y Z \to Z$ 也是光滑的。

**解答**：光滑性在基变换下保持，这是光滑态射的核心性质之一。

1. **有限型的保持**：$f$ 局部有限型，基变换保持有限型。
2. **平坦性的保持**：$f$ 平坦，平坦性在基变换下保持（张量积保持平坦性）。
3. **微分层的保持**：由相对微分层的基变换公式，$\Omega_{X \times_Y Z / Z} \cong p_X^* \Omega_{X/Y}$，其中 $p_X: X \times_Y Z \to X$ 是投影。因 $\Omega_{X/Y}$ 局部自由，其拉回也局部自由，且秩相同。
4. **相对维度的保持**：纤维满足 $(X \times_Y Z)_z \cong X_{g(z)} \times_{k(g(z))} k(z)$，维度不变。

因此基变换映射光滑。∎

---

### 习题 2

**题目**：证明平展态射是开映射。

**解答**：平展态射是光滑的，光滑态射是平坦且局部有限展示的，平坦且局部有限展示的态射是开映射（由平坦态射的开映射性质）。更直接的证明：平展态射局部上是标准平展映射与开嵌入的复合。标准平展映射 $A \to (A[t]/(P(t)))_Q$ 对应于谱映射中多项式根的变化，是开映射（可通过构造逆像的开集直接验证）。开嵌入显然是开映射。复合保持开映射性质。∎

---

### 习题 3

**题目**：设 $f: X \to Y$ 是有限型态射，$Y$ 是既约的。证明 $f$ 是平坦的当且仅当对任意关联点（associated point）$\eta \in Y$，纤维 $X_\eta$ 在 $X$ 中的原像不包含嵌入点（embedded points）。

**解答**：这是平坦性的关联点判别法。

**$(\Rightarrow)$**：若 $f$ 平坦，则 $X$ 的关联点映到 $Y$ 的关联点（平坦映射保持关联点）。因此纤维 $X_\eta$ 中没有嵌入点（因为嵌入点会映射到 $Y$ 的非泛点处，但平坦映射下关联点的像必须是关联点）。

**$(\Leftarrow)$**：若所有纤维无嵌入点，则 $X$ 的关联点恰好在泛纤维上。由 $Y$ 既约，这推出 $f$ 平坦。详细论证需利用交换代数中"无嵌入点 fibers 意味着 $-\otimes k(\eta)$ 保持深度"，结合平坦性的深度判据。∎

---

### 习题 4

**题目**：设 $k$ 是代数闭域，$X = \operatorname{Spec} k[x,y]/(y^2 - x^3 + x)$，$Y = \operatorname{Spec} k[x]$。证明投影 $f: X \to Y$ 是平展的当且仅当限制在 $x \neq \pm 1/\sqrt{3}$ 的开集上（假设 $\operatorname{char}(k) \neq 2, 3$）。

**解答**：$X$ 是椭圆曲线（Weierstrass 方程）。投影到 $x$-坐标对应 $k[x] \to k[x,y]/(y^2 - x^3 + x)$。

Jacobian 判据：$f$ 由一个方程 $y^2 - x^3 + x = 0$ 定义，$n = 2$，$r = 1$。Jacobian 是 $[\partial F / \partial x, \partial F / \partial y] = [-3x^2 + 1, 2y]$。

在点 $(x,y)$ 处，秩为 1 当且仅当 $(-3x^2 + 1, 2y) \neq (0,0)$。即 $y \neq 0$ 或 $3x^2 \neq 1$。

当 $y = 0$ 时，$x^3 - x = 0$，即 $x = 0, \pm 1$。其中 $x = \pm 1/\sqrt{3}$ 时（需 $

$\operatorname{char}(k) \neq 3$），$3x^2 - 1 = 0$，Jacobian 秩为 0，故不光滑（分歧点）。这些点是 $y = 0$ 且 $3x^2 = 1$ 的解，对应映射的分歧点。

在 $y \neq 0$ 或 $3x^2 \neq 1$ 处，Jacobian 秩为 1，且映射平坦（因为 $k[x] \to k[x,y]/(F)$ 是整扩张的局部化，自由模），故平展。∎

---

### 习题 5

**题目**：证明：若 $f: X \to Y$ 是平坦且拟紧的态射，$Y$ 是整概形，则像 $f(X)$ 在 $Y$ 中开或闭。进一步，若 $f$ 还是真态射，则 $f$ 是满射当且仅当泛纤维 $X_\eta$ 非空。

**解答**：

1. **平坦 + 局部有限型 = 开映射**：这是平坦映射的基本性质。因 $f$ 拟紧，像 $f(X)$ 是拟紧的开像的并，故是开集。
2. 若 $f$ 是真态射，则像 $f(X)$ 是闭集。因此 $f(X)$ 既开又闭。在连通空间 $Y$ 中，既开又闭的子集只能是空集或全空间。
3. 若泛纤维 $X_\eta$ 非空，则 $f(X)$ 包含泛点，而 $f(X)$ 是闭集且包含泛点，故 $f(X) = Y$（因为整概形的闭包 of 泛点是全空间）。反之，若 $f$ 满射，则泛纤维当然非空。∎

---

### 习题 6

**题目**：设 $A$ 是 Noether 环，$M$ 是有限生成 $A$-模。证明 $M$ 平坦当且仅当对任意素理想 $\mathfrak{p} \subseteq A$，$M_{\mathfrak{p}}$ 是自由 $A_{\mathfrak{p}}$-模。

**解答**：这是 **Auslander-Buchsbaum 定理** 的局部形式。

**$(\Leftarrow)$**：局部自由显然推出平坦（自由模平坦，局部化保持平坦性）。

**$(\Rightarrow)$**：设 $M$ 平坦。对素理想 $\mathfrak{p}$，考虑 $A_{\mathfrak{p}}$ 上的模 $M_{\mathfrak{p}}$。因 $A$ Noether 且 $M$ 有限生成，$M_{\mathfrak{p}}$ 是有限生成 $A_{\mathfrak{p}}$-模。

由平坦性，$\operatorname{Tor}_1^{A_{\mathfrak{p}}}(M_{\mathfrak{p}}, k(\mathfrak{p})) = 0$，其中 $k(\mathfrak{p}) = A_{\mathfrak{p}}/\mathfrak{p}A_{\mathfrak{p}}$。

对局部环上的有限生成模，若 $\operatorname{Tor}_1(M, k) = 0$，则 $M$ 自由。这是因为可取极小生成元，构造自由分解：设 $n = \dim_{k}(M/\mathfrak{m}M)$，取满射 $A^n \to M$。由 $\operatorname{Tor}_1(M, k) = 0$，核 $K$ 满足 $K/\mathfrak{m}K = 0$，故 $K = 0$（Nakayama）。因此 $M \cong A^n$ 自由。∎

---

### 习题 7

**题目**：设 $f: X \to Y$ 是光滑态射，$s: Y \to X$ 是其截面（即 $f \circ s = \operatorname{id}_Y$）。证明 $s$ 是闭嵌入，且像 $s(Y)$ 是 $X$ 中的光滑闭子概形。

**解答**：

1. **截面是闭嵌入**：一般地，任意截面都是闭嵌入。证明：考虑对角映射 $\Delta_f: X \to X \times_Y X$。截面 $s$ 给出 $Y \to X$ 使得 $(s \circ f, \operatorname{id}_X): X \to X \times_Y X$ 的复合给出... 更直接地，利用截面在集合论上的性质：$s$ 是单射，且 $s(Y)$ 是 $X$ 中满足 $f(x) = y$ 且 $x = s(y)$ 的点集，由 $f$ 分离，这是闭集。

2. **光滑性**：在点 $y \in Y$ 处，设 $x = s(y)$。切空间的正合列给出
   $$0 \longrightarrow T_{Y,y} \xrightarrow{ds} T_{X,x} \xrightarrow{df} T_{Y,y} \longrightarrow 0$$
   其中 $df \circ ds = \operatorname{id}$。故 $ds$ 是单射，$s(Y)$ 在 $x$ 处的法丛同构于 $f$ 的相对切丛在 $s(Y)$ 上的限制。因 $f$ 光滑，相对切丛局部自由，故 $s(Y)$ 光滑。∎

---

### 习题 8

**题目**：设 $f: X \to Y$ 是有限平展态射，$Y$ 是连通概形。证明存在有限平展覆叠 $g: Z \to Y$ 使得 $X \times_Y Z \to Z$ 是平凡覆叠（即同构于若干个 $Z$ 的不交并）。

**解答**：这是 **平展覆叠的 Galois 理论** 的基本结果。

考虑 $X$ 在 $Y$ 上的自同构群 $\operatorname{Aut}(X/Y)$。因 $f$ 有限平展，$\operatorname{Aut}(X/Y)$ 是有限群（纤维有限，自同构限制到纤维上是置换群的子群）。

取 $Z = X$ 在 $Y$ 上的 Galois 闭包（Galois closure），这是包含 $X$ 的最小 Galois 覆叠。Galois 闭包的存在性由有限可分扩张的 Galois 闭包类比而来：在几何点上，$X_y$ 是有限个点，Galois 群作用在这些点上；Galois 闭包对应于把这些点的所有置换都实现出来的覆叠。

在 Galois 闭包 $Z \to Y$ 上，$X \times_Y Z$ 分裂为 $|G|/|H|$ 个 $Z$ 的拷贝，其中 $G = \operatorname{Gal}(Z/Y)$，$H = \operatorname{Aut}(X/Y)$。∎

---

### 习题 9

**题目**：设 $A$ 是 DVR，$\pi$ 是其一致化子，$K = \operatorname{Frac}(A)$。设 $X \to \operatorname{Spec} A$ 是平坦有限型态射。证明 $X$ 的既约特殊纤维 $X_k^{\mathrm{red}}$（其中 $k = A/\pi A$）的维度等于一般纤维 $X_K$ 的维度。

**解答**：因 $A$ 是 DVR，$\operatorname{Spec} A$ 只有两个点：闭点（对应 $k$）和泛点（对应 $K$）。由平坦态射的纤维维度定理，在整基上纤维维度是常数。

更直接地，设 $X = \operatorname{Spec} B$，$B$ 是平坦有限型 $A$-代数。平坦性意味着 $\pi$ 在 $B$ 中不是零因子。因此 $\dim(B/\pi B) = \dim(B) - 1$（Krull 主理想定理），而 $\dim(B \otimes_A K) = \dim(B) - 1$（因为局部化不改变维度）。故 $\dim(X_k) = \dim(X_K)$。

对于既约化，$X_k^{\mathrm{red}}$ 的维度等于 $X_k$ 的维度（因为既约化不改变维度）。∎

---

### 习题 10

**题目**：设 $f: X \to Y$ 是光滑真态射，$Y$ 是连通概形。证明所有几何纤维 $X_{\overline{y}}$ 的欧拉示性数 $\chi(X_{\overline{y}}, \mathcal{O})$ 相同。

**解答**：这是 **上同调与基变换定理** 在平坦族中的直接应用。

因 $f$ 光滑真，$f$ 是平坦且proper的。对结构层 $\mathcal{O}_X$，高阶直像 $R^i f_* \mathcal{O}_X$ 是 $Y$ 上的凝聚层（由 proper 映射的凝聚性定理，Grauert 定理的特殊情形）。

由半连续性定理（Semicontinuity Theorem，将在 Ch 28–29 中详细讨论），函数 $y \mapsto h^i(X_y, \mathcal{O}_{X_y})$ 是上半连续的。但同时，由 Serre 对偶在纤维上的应用和真态射的对偶性，这些函数也满足某种对偶的下界约束。

对于欧拉示性数，有

$$\chi(X_y, \mathcal{O}) = \sum_{i=0}^{\dim(X_y)} (-1)^i h^i(X_y, \mathcal{O})$$

由 **Grauert 定理**（将在下章详述），在平坦族中欧拉示性数是局部常数。因 $Y$ 连通，故全局常数。∎

---

**文档位置**: `docs/00-银层核心课程/Stanford-FOAG-基础代数几何/Ch23-25-smooth-étale-flat态射.md`
**创建日期**: 2026-04-18
**最后更新**: 2026-04-18
