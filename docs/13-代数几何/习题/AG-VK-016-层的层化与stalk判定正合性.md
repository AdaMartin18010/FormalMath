---
title: 层的层化与 stalk 判定正合性
msc_primary: 14
  - 14F05
  - 18F20
level: silver
target_courses:
- Stanford FOAG
course: Stanford FOAG
course_code: Math 216A/B
instructor: Ravi Vakil
foag_chapter: Ch 2
topic: 层化定理与 stalk 的正合性
exercise_type: TEC (技术型)
difficulty: ⭐⭐⭐
importance: ★★
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
    - 'Chapter II, Section 1: Sheaves'
    url: null
    pages: 60-69
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
    - 'Section 2.4: Sheaves, Section 2.5: Sheaves of abelian groups and O_X-modules'
    url: https://math.stanford.edu/~vakil/216blog/
    pages: 65-72
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

# AG-VK-016: 层的层化与 stalk 判定正合性

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | Stanford FOAG (Math 216A/B) |
| **教材章节** | Ch 2: Sheaves |
| **对应FOAG习题** | 2.4.B, 2.5.D |
| **类型** | TEC (技术型) |
| **难度** | ⭐⭐⭐ |
| **重要性** | ★★ |

---

## 核心定理与定义

### 定义 1：Stalk（茎）

设 $X$ 为拓扑空间，$\mathcal{F}$ 为 $X$ 上的预层（abelian group 预层），$p \in X$。定义 **stalk** 为：

$$\mathcal{F}_p := \varinjlim_{p \in U} \mathcal{F}(U)$$

即对所有包含 $p$ 的开集 $U$ 取正向极限。具体地，$\mathcal{F}_p$ 中的元素是等价类 $[(U, s)]$，其中 $p \in U$，$s \in \mathcal{F}(U)$，等价关系为：$(U, s) \sim (V, t)$ 当且仅当存在 $p \in W \subseteq U \cap V$ 使得 $s|_W = t|_W$。

> **Vakil 的几何直觉**：stalk 是在点 $p$ 处的“局部显微镜”。它抛弃了点 $p$ 之外的所有信息，只保留在该点任意小邻域内的行为。层的许多整体性质都可以通过在每一点看 stalk 来判定，就像函数的连续性可以逐点检验一样。

### 定理 1：层化定理（Sheafification）

设 $\mathcal{F}$ 是拓扑空间 $X$ 上的 abelian group 预层。则存在层 $\mathcal{F}^+$ 和典范预层同态 $\theta: \mathcal{F} \to \mathcal{F}^+$，满足以下泛性质：

对任意层 $\mathcal{G}$ 和预层同态 $\phi: \mathcal{F} \to \mathcal{G}$，存在唯一的层同态 $\tilde{\phi}: \mathcal{F}^+ \to \mathcal{G}$ 使得下图交换：

```
F ──θ──► F⁺
│        │
φ        ∃! φ̃
▼        ▼
G ═══════ G
```

等价地，层化函子 $(-)^+$ 是遗忘函子 $\mathbf{Sh}(X) \to \mathbf{PSh}(X)$ 的左伴随。

### 定理 2：正合性可在 stalk 上检验

设 $X$ 为拓扑空间，$\mathcal{F} \xrightarrow{\alpha} \mathcal{G} \xrightarrow{\beta} \mathcal{H}$ 是层同态的序列。则以下等价：

1. 该序列是层的正合列；
2. 对所有 $p \in X$，诱导的 stalk 序列 $\mathcal{F}_p \xrightarrow{\alpha_p} \mathcal{G}_p \xrightarrow{\beta_p} \mathcal{H}_p$ 是正合的。

---

## 完整证明

### 层化定理的显式构造

**构造**：对任意开集 $U \subseteq X$，定义

$$\mathcal{F}^+(U) := \left\{ (s_p)_{p \in U} \in \prod_{p \in U} \mathcal{F}_p \;\middle|\; \forall p \in U, \exists p \in V \subseteq U, \exists t \in \mathcal{F}(V), \forall q \in V: t_q = s_q \right\}$$

即 $U$ 上“局部来自 $\mathcal{F}$ 的相容茎族”。限制映射为自然的坐标限制。

**证明 $\mathcal{F}^+$ 是层**：

**唯一性**：设 $\{U_i\}$ 是 $U$ 的开覆盖，$s = (s_p), t = (t_p) \in \mathcal{F}^+(U)$ 满足 $s|_{U_i} = t|_{U_i}$ 对所有 $i$。则对每个 $p \in U$，取 $i$ 使 $p \in U_i$，有 $s_p = t_p$。故 $s = t$。

**存在性**：设 $s^{(i)} \in \mathcal{F}^+(U_i)$ 两两相容。对每个 $p \in U$，定义 $s_p := s^{(i)}_p$（任取 $p \in U_i$）。由相容性，这与 $i$ 的选取无关。需验证 $(s_p)_{p \in U}$ 局部来自 $\mathcal{F}$：对每个 $p \in U$，因 $s^{(i)} \in \mathcal{F}^+(U_i)$，存在 $p \in V \subseteq U_i$ 和 $t \in \mathcal{F}(V)$ 使得 $t_q = s^{(i)}_q = s_q$ 对所有 $q \in V$。故 $(s_p) \in \mathcal{F}^+(U)$。∎

**泛性质的验证**：

给定预层同态 $\phi: \mathcal{F} \to \mathcal{G}$，定义 $\tilde{\phi}_U: \mathcal{F}^+(U) \to \mathcal{G}(U)$ 为：

$$\tilde{\phi}_U((s_p)_{p \in U}) = \text{唯一黏合的 } t \in \mathcal{G}(U) \text{ 使得 } t_p = \phi_p(s_p)$$

这里 $\phi_p: \mathcal{F}_p \to \mathcal{G}_p$ 是 stalk 上的诱导映射。由于 $\mathcal{G}$ 是层，且 $\{t_p\}$ 局部相容（因为 $s_p$ 局部来自 $\mathcal{F}$，而 $\phi$ 保持限制），这样的 $t$ 唯一存在。

唯一性：若 $\psi: \mathcal{F}^+ \to \mathcal{G}$ 也满足 $\psi \circ \theta = \phi$，则在 stalk 上 $\psi_p \circ \theta_p = \phi_p$。但 $\theta_p: \mathcal{F}_p \to (\mathcal{F}^+)_p$ 是同构（易验证），故 $\psi_p = \phi_p \circ \theta_p^{-1}$。由于层同态由 stalk 决定，$\psi = \tilde{\phi}$。∎

### 正合性可在 stalk 上检验

**定义回顾**：层序列 $\mathcal{F} \xrightarrow{\alpha} \mathcal{G} \xrightarrow{\beta} \mathcal{H}$ 在 $\mathcal{G}$ 处正合，是指 $\operatorname{im}(\alpha) = \ker(\beta)$ 作为 $\mathcal{G}$ 的子层，即对每个开集 $U$，

$$\operatorname{im}(\alpha)(U) = \ker(\beta)(U)$$

其中 $\operatorname{im}(\alpha)$ 是预层像的层化，$\ker(\beta)$ 已是层。

**证明 $(1) \Rightarrow (2)$**：

 stalk 函子 $(-)_p: \mathbf{Sh}(X) \to \mathbf{Ab}$ 是左正合的（因为它是遗忘函子的左伴随，或直接用正向极限的正合性）。更精确地， stalk 与核交换：$\ker(\beta)_p = \ker(\beta_p)$。同时，像预层的 stalk 等于像的 stalk：$(\operatorname{im}^{\text{pre}}\alpha)_p = \operatorname{im}(\alpha_p)$。由于层化不改变 stalk，$(\operatorname{im}\alpha)_p = \operatorname{im}(\alpha_p)$。故若 $\operatorname{im}\alpha = \ker\beta$ 作为子层，则在 stalk 上 $\operatorname{im}(\alpha_p) = \ker(\beta_p)$。

**证明 $(2) \Rightarrow (1)$**：

设对所有 $p$，$\operatorname{im}(\alpha_p) = \ker(\beta_p)$。首先，$\beta \circ \alpha = 0$ 因为 stalk 上 $(\beta \circ \alpha)_p = \beta_p \circ \alpha_p = 0$，而层同态为零当且仅当所有 stalk 上为零。故 $\operatorname{im}^{\text{pre}}\alpha \subseteq \ker\beta$。由于 $\ker\beta$ 是层，层化后仍有 $\operatorname{im}\alpha \subseteq \ker\beta$。

反过来，设 $s \in \ker(\beta)(U)$，即 $\beta_U(s) = 0$。对每个 $p \in U$，有 $s_p \in \ker(\beta_p) = \operatorname{im}(\alpha_p)$。故存在 $t_p \in \mathcal{F}_p$ 使得 $\alpha_p(t_p) = s_p$。由 stalk 的定义，存在 $p \in V_p \subseteq U$ 和截面 $\tilde{t}_p \in \mathcal{F}(V_p)$ 使得 $(\alpha_{V_p}(\tilde{t}_p))_p = s_p$。即存在更小的 $p \in W_p \subseteq V_p$ 使得 $\alpha_{W_p}(\tilde{t}_p|_{W_p}) = s|_{W_p}$。

开覆盖 $\{W_p\}_{p \in U}$ 和截面族 $\{\tilde{t}_p|_{W_p}\}$ 满足：在 $W_p \cap W_q$ 上，$\alpha(\tilde{t}_p) = s = \alpha(\tilde{t}_q)$。由于我们尚不知 $\alpha$ 的核是否为零，需要调整。令 $t'_p := \tilde{t}_p|_{W_p}$。则 $\alpha(t'_p)$ 和 $\alpha(t'_q)$ 在 $W_p \cap W_q$ 上相等。这意味着 $t'_p - t'_q \in \ker(\alpha)(W_p \cap W_q)$。

实际上，更简单的方法是：由 $s_p \in \operatorname{im}(\alpha_p)$，存在邻域 $W_p$ 和 $t_p \in \mathcal{F}(W_p)$ 使得 $\alpha(t_p) = s|_{W_p}$（精确相等，不仅在 stalk 上）。这是 stalk 等价定义的直接推论：若两个层截面在某点 stalk 相同，则在某邻域相同。由于 $\alpha_p(t_p) = s_p$，存在邻域使 $\alpha(t_p) = s$。于是 $\{t_p\}$ 在重叠处满足 $\alpha(t_p - t_q) = 0$，即 $t_p - t_q \in (\ker\alpha)(W_p \cap W_q)$。

这给出 $[s] \in \operatorname{im}(\alpha)(U)$（在商意义下）。严格说，$s$ 作为 $\mathcal{G}(U)$ 的元素属于像层的 $U$-截面。∎

---

## FOAG 习题解答

### 习题 2.4.B：层在基上的恢复

**题目**（FOAG Ch 2, Exercise 2.4.B）：

设 $\mathcal{B}$ 是拓扑空间 $X$ 上一个拓扑基。证明：层 $\mathcal{F}$ 在 $X$ 上的数据可以由其在 $\mathcal{B}$ 上的限制唯一恢复。即给出 $\mathcal{B}$ 上满足层公理的“基预层”，存在唯一的 $X$ 上的层与其相容。

**解答**：

设 $\mathcal{F}_0$ 是定义在基 $\mathcal{B}$ 上的预层，满足对基元素的层公理：对任意 $U \in \mathcal{B}$ 和由基元素 $\{U_i\} \subseteq \mathcal{B}$ 构成的覆盖：

1. （唯一性）若 $s, t \in \mathcal{F}_0(U)$ 满足 $s|_{U_i} = t|_{U_i}$ 对所有 $i$，则 $s = t$；
2. （黏合性）若给定相容的 $s_i \in \mathcal{F}_0(U_i)$，则存在 $s \in \mathcal{F}_0(U)$ 使得 $s|_{U_i} = s_i$。

**构造**：对任意开集 $U \subseteq X$，定义

$$\mathcal{F}(U) := \left\{ (s_B)_{B \in \mathcal{B}, B \subseteq U} \;\middle|\; \text{相容：若 } B' \subseteq B \subseteq U, \text{ 则 } s_B|_{B'} = s_{B'} \right\} / \sim$$

更标准地，定义：

$$\mathcal{F}(U) := \varprojlim_{B \in \mathcal{B}, B \subseteq U} \mathcal{F}_0(B)$$

即对 $U$ 的所有基开子集 $B$，取相容族 $(s_B)$ 的集合。

**验证 $\mathcal{F}$ 是层**：

这是直接验证：若 $\{U_i\}$ 是 $U$ 的开覆盖，给定相容的 $s^{(i)} \in \mathcal{F}(U_i)$。每个 $s^{(i)}$ 本身是相容族 $(s^{(i)}_B)_{B \subseteq U_i}$。对任意 $B \subseteq U$，若 $B \subseteq U_i \cap U_j$，则 $s^{(i)}_B = s^{(j)}_B$（由 $s^{(i)}|_{U_i \cap U_j} = s^{(j)}|_{U_i \cap U_j}$）。故可定义 $s_B := s^{(i)}_B$（任取 $B \subseteq U_i$），这给出全局相容族 $s \in \mathcal{F}(U)$。唯一性同理。

**唯一性**：若 $\mathcal{G}$ 是 $X$ 上的层且 $\mathcal{G}|_{\mathcal{B}} \cong \mathcal{F}_0$，则对任意 $U$，由层的性质：

$$\mathcal{G}(U) = \varprojlim_{B \subseteq U, B \in \mathcal{B}} \mathcal{G}(B) = \varprojlim_{B \subseteq U, B \in \mathcal{B}} \mathcal{F}_0(B) = \mathcal{F}(U)$$

故 $\mathcal{G} \cong \mathcal{F}$。∎

> **几何直觉**：拓扑基 $\mathcal{B}$ 像是空间的“基本砖块”。层的数据只需在这些砖块上指定，然后通过层公雅自动“灰泥黏合”成整个空间上的结构。这解释了为什么层的定义常常只在基上给出。

---

### 习题 2.5.D：逆像层的泛性质

**题目**（FOAG Ch 2, Exercise 2.5.D）：

设 $f: X \to Y$ 是连续映射，$\mathcal{G}$ 是 $Y$ 上的层。定义 **逆像层**（inverse image sheaf）$f^{-1}\mathcal{G}$ 为预层逆像的层化：

$$f^{-1}\mathcal{G} := (f^{\text{pre}-1}\mathcal{G})^+, \quad (f^{\text{pre}-1}\mathcal{G})(U) = \varinjlim_{f(U) \subseteq V} \mathcal{G}(V)$$

证明逆像层满足以下伴随关系：

$$\operatorname{Hom}_X(f^{-1}\mathcal{G}, \mathcal{F}) \cong \operatorname{Hom}_Y(\mathcal{G}, f_*\mathcal{F})$$

**解答**：

**步骤 1：预像层的伴随**。先证明预层层面有：

$$\operatorname{Hom}_{\mathbf{PSh}(X)}(f^{\text{pre}-1}\mathcal{G}, \mathcal{F}) \cong \operatorname{Hom}_{\mathbf{Sh}(Y)}(\mathcal{G}, f_*\mathcal{F})$$

当右边 $\mathcal{F}$ 只是预层时，左边也应是预层同态。

给定预层同态 $\phi: f^{\text{pre}-1}\mathcal{G} \to \mathcal{F}$。对 $Y$ 中开集 $V$，因 $f(f^{-1}(V)) \subseteq V$，有典范映射：

$$\mathcal{G}(V) \to \varinjlim_{f(U) \subseteq V} \mathcal{G}(V') = (f^{\text{pre}-1}\mathcal{G})(f^{-1}(V)) \xrightarrow{\phi_{f^{-1}(V)}} \mathcal{F}(f^{-1}(V)) = (f_*\mathcal{F})(V)$$

这给出 $\tilde{\phi}: \mathcal{G} \to f_*\mathcal{F}$。

反之，给定 $\psi: \mathcal{G} \to f_*\mathcal{F}$。对 $X$ 中开集 $U$，及满足 $f(U) \subseteq V$ 的 $V$，有：

$$\mathcal{G}(V) \xrightarrow{\psi_V} \mathcal{F}(f^{-1}(V)) \xrightarrow{\text{res}} \mathcal{F}(U)$$

这族映射与 $V$ 的包含相容，故诱导到正向极限：

$$(f^{\text{pre}-1}\mathcal{G})(U) = \varinjlim_{f(U) \subseteq V} \mathcal{G}(V) \longrightarrow \mathcal{F}(U)$$

即预层同态 $\tilde{\psi}: f^{\text{pre}-1}\mathcal{G} \to \mathcal{F}$。这两个构造互逆。∎（预层层面）

**步骤 2：提升到层**。由于 $f^{-1}\mathcal{G} = (f^{\text{pre}-1}\mathcal{G})^+$ 是层化，而层化是遗忘函子的左伴随：

$$\operatorname{Hom}_{\mathbf{Sh}(X)}((f^{\text{pre}-1}\mathcal{G})^+, \mathcal{F}) \cong \operatorname{Hom}_{\mathbf{PSh}(X)}(f^{\text{pre}-1}\mathcal{G}, \mathcal{F})$$

对任意层 $\mathcal{F}$。结合步骤 1 的预层伴随，得：

$$\operatorname{Hom}_X(f^{-1}\mathcal{G}, \mathcal{F}) \cong \operatorname{Hom}_Y(\mathcal{G}, f_*\mathcal{F})$$

这就是逆像层的泛性质。∎

> **几何直觉**：正像 $f_*$ 是“把 $X$ 上的层推到 $Y$ 上”，逆像 $f^{-1}$ 则是“把 $Y$ 上的层拉回 $X$ 上”。伴随关系 $f^{-1} \dashv f_*$ 告诉我们：从拉回层到 $X$ 上层的数据，与从原层到推上层的数据，是一回事。这是层论中“推出-拉回对偶”的核心体现。

---

## Lean4 代码引用

以下代码展示了 Mathlib4 中 stalk 与层化的核心定义框架：

```lean4
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.Sheaves.Sheafify

open CategoryTheory TopCat TopologicalSpace

variable {X : TopCat} (F : Presheaf Ab X) (p : X)

/-- Stalk 作为正向极限 -/
def StalkExample : Ab :=
  F.stalk p

/-- 层化定理：伴随关系 -/
example (G : Sheaf Ab X) :
    (F.sheafify ⟶ G) ≃ (F ⟶ G.val) :=
  F.sheafifyHomEquiv G
```

对应文件：`FormalMath-Enhanced/lean4/FormalMath/FormalMath/CohomologyTheory.lean` 中亦使用了层上同调与 Čech 上同调的 stalk 基础。

---

**文档位置**: `docs/13-代数几何/习题/AG-VK-016-层的层化与stalk判定正合性.md`  
**创建日期**: 2026-04-17  
**最后更新**: 2026-04-17


## 习题

**习题 1.1**。证明：预层的层化 $\\mathcal{F}^+$ 满足泛性质：任意层 $\\mathcal{G}$ 和预层态射 $\\mathcal{F} \\to \\mathcal{G}$ 唯一通过 $\\mathcal{F}^+$ 分解。

*解答*：层化的构造保证了在每点的茎相同，且层化后的映射由茎上的映射诱导，唯一性由层的局部性质决定。$\square$

---

**习题 1.2**。举例说明：预层的茎正合不意味着层正合。

*解答*：考虑 $0 \\to \\mathcal{F} \\to \\mathcal{G} \\to \\mathcal{H} \\to 0$，其中 $\\mathcal{G} \\to \\mathcal{H}$ 是满射但在某开集上截面不满。层化后可恢复正合性。$\square$
