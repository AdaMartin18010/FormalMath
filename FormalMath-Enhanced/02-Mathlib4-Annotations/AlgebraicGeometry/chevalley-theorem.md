---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: Chevalley定理 (Chevalley's Theorem)
---
# Chevalley定理 (Chevalley's Theorem)

## Mathlib4 引用

```lean
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Topology.Constructible

namespace ChevalleyTheorem

variable {X Y : Type*} [Scheme X] [Scheme Y] {f : X → Y} [IsMorphismOfFiniteType f]

/-- Chevalley定理：有限型态射的像是可构造集 -/
theorem chevalley_theorem :
    IsConstructible (Set.range f) := by
  -- 分解为局部有限表现和Noether归纳
  sorry

/-- 开映射的判定 -/
theorem open_map_criterion (hf : IsFlat f) :
    IsOpenMap f := by
  -- 平坦开映射定理
  sorry

end ChevalleyTheorem
```

## 数学背景

Chevalley定理由法国数学家Claude Chevalley在20世纪50年代证明，是代数几何中关于有限型态射的一个基本结果。它深刻揭示了概形态射的拓扑性质与代数结构之间的内在联系，是证明代数几何中许多开映射性质的基础工具。

### 可构造集的定义

在拓扑空间 $X$ 中，一个子集被称为**局部闭集**（locally closed set），如果它可以表示为 $U \cap V$ 的形式，其中 $U$ 是开集，$V$ 是闭集。等价地，一个子集是局部闭集当且仅当它在自身中是开的（即它是某个开集与闭集的交）。

**定义（可构造集）**：拓扑空间 $X$ 中的**可构造集**（constructible set）是指有限个局部闭集的并集。等价地，可构造集是由拓扑空间的开集和闭集通过有限次并、交、补运算所能生成的集合族中的元素。

对于Noether拓扑空间（如概形的Zariski拓扑），可构造集有更简洁的描述：一个子集 $S \subseteq X$ 是可构造的当且仅当它可以写成有限不交并：
$$S = \bigcup_{i=1}^{n} U_i \cap V_i$$
其中每个 $U_i$ 是 $X$ 中的开集，每个 $V_i$ 是 $X$ 中的闭集。

### 有限型态射

**定义（有限型态射）**：设 $f: X \to Y$ 是概形态射。称 $f$ 是**有限型**（of finite type）的，如果 $Y$ 可以被仿射开集 $\{\text{Spec } B_i\}$ 覆盖，使得每个 $f^{-1}(\text{Spec } B_i)$ 可以被有限个仿射开集 $\{\text{Spec } A_{ij}\}$ 覆盖，其中每个 $A_{ij}$ 都是有限生成的 $B_i$-代数。

有限型态射是代数几何中最常见的一类态射。例如，拟射影概形到仿射概形的固有态射、仿射空间 $\mathbb{A}^n_Y \to Y$ 的投影等都是有限型态射。

## Chevalley定理的陈述

**定理（Chevalley）**：设 $f: X \to Y$ 是有限型概形态射，则 $f$ 的像 $f(X)$ 是 $Y$ 中的可构造集。更一般地，$X$ 中任意可构造集的像都是 $Y$ 中的可构造集。

形式化地，若 $S \subseteq X$ 是可构造集，则 $f(S) \subseteq Y$ 也是可构造集。

### Chevalley定理的推论：平坦开映射定理

**定理（平坦开映射定理，Grothendieck）**：设 $f: X \to Y$ 是平坦且有限型的概形态射，则 $f$ 是开映射，即 $f$ 将开集映为开集。

**证明思路**：由Chevalley定理，$f(X)$ 是可构造集。又因为平坦态射在Zariski拓扑下具有"一般开性"（going-down性质），结合Chevalley的结果可以证明 $f(X)$ 实际上是开的。对于一般的开集 $U \subseteq X$，限制态射 $f|_U: U \to Y$ 仍然是平坦有限型的，故 $f(U)$ 也是开的。 $\square$

## 证明概要

Chevalley定理的证明通常采用Noether归纳法，核心步骤如下：

**第一步：简化到仿射情形**

由于可构造性是局部性质，我们可以假设 $Y = \text{Spec } B$ 是仿射的，而 $X$ 可以被有限个仿射开集 $\{\text{Spec } A_i\}$ 覆盖，其中每个 $A_i$ 都是有限生成的 $B$-代数。由于有限个可构造集的并仍是可构造集，只需对每个 $A_i$ 证明即可。因此不妨设 $X = \text{Spec } A$，其中 $A$ 是有限生成的 $B$-代数。

**第二步：约化到整环情形**

利用Noether正规化引理，若 $A$ 是有限生成的 $B$-代数，可以找到 $B$ 上代数无关的元 $y_1, \ldots, y_n \in A$，使得 $A$ 在 $B[y_1, \ldots, y_n]$ 上是整的。这给出了有限满射：
$$\text{Spec } A \to \text{Spec } B[y_1, \ldots, y_n] \cong \mathbb{A}^n_B$$

**第三步：对仿射空间的投影使用Noether归纳**

关键情形是证明投影映射 $\pi: \mathbb{A}^1_Y \to Y$ 的像将可构造集映为可构造集。对 $\mathbb{A}^n_Y \to Y$ 可通过归纳完成。

设 $S \subseteq \mathbb{A}^1_Y$ 是可构造集，则 $S$ 可以表示为若干集合 $\{f = 0, g \neq 0\}$ 的有限并，其中 $f, g \in \mathcal{O}_Y(Y)[t]$ 是多项式。对每个不可约闭子集 $Z \subseteq Y$，考虑 $S$ 在 $Z$ 上的纤维。通过分析多项式在纤维上的根的存在性（利用代数闭包的性质），可以证明 $\pi(S)$ 与 $Z$ 的交要么包含 $Z$ 的一个非空开集，要么不包含 $Z$ 的任何非空开集。

**第四步：完成Noether归纳**

若 $\pi(S)$ 不包含任何不可约闭子集的非空开集，则由Noether归纳假设，$\pi(S)$ 是可构造的。若 $\pi(S)$ 包含某个不可约闭子集 $Z$ 的非空开集 $U$，则考虑 $Y \setminus U$ 上的情形，再次应用归纳。 $\square$

## 例子

### 例子1：多项式映射

设 $f: \mathbb{A}^2 \to \mathbb{A}^1$ 为投影 $(x, y) \mapsto x$。则 $f$ 是有限型态射（实际上是有限表现的）。$f$ 的像是整个 $\mathbb{A}^1$，当然是开的也是可构造的。

更一般地，考虑 $g: \mathbb{A}^2 \to \mathbb{A}^2$ 定义为 $g(x, y) = (x, xy)$。这不是开映射：点 $(0, 1)$ 不在像中，但任意包含 $(0, 1)$ 的开集中都包含形如 $(\epsilon, 1)$ 的点，而 $g(1, 1) = (1, 1)$ 等。实际上 $g(\mathbb{A}^2) = \{(a, b) : a \neq 0\} \cup \{(0, 0)\}$，这是一个可构造集但不是开集。这验证了Chevalley定理的精确性。

### 例子2：双有理态射

考虑吹起（blow-up）态射 $\pi: \tilde{\mathbb{A}}^2 \to \mathbb{A}^2$ 在点 $0$ 处。这是有限型态射，其像是整个 $\mathbb{A}^2$，是开的。例外除子 $E = \pi^{-1}(0)$ 被映为单点 $\{0\}$，是闭的（从而可构造）。

### 例子3：有限态射

若 $f: X \to Y$ 是有限态射（特别的，有限型），则 $f$ 是闭映射（proper implies closed），因此 $f$ 的像是闭集，当然是可构造集。Chevalley定理将此推广到了更一般的有限型情形。

## 应用

### 1. 平坦开映射定理

如前所述，Chevalley定理是证明平坦开映射定理的关键。平坦开映射定理在代数几何中有广泛应用，例如在证明概形的平坦族具有开的Hilbert函数、证明某些模空间的存在性等方面。

### 2. 泛平坦性结果（Generic Flatness）

Chevalley定理与平坦性结合，可以证明重要的泛平坦性定理：设 $f: X \to Y$ 是有限型态射，$Y$ 是整的Noether概形，则存在 $Y$ 的非空开集 $U$，使得 $f|_{f^{-1}(U)}: f^{-1}(U) \to U$ 是平坦的。

### 3. Hilbert概形理论

在构造Hilbert概形时，需要证明某些态射是开的。Chevalley定理和开映射定理提供了证明这类结果的基本工具。Hilbert概形参数化了射影空间中具有给定Hilbert多项式的闭子概形，是模空间理论的核心对象之一。

### 4. 构造性集合与力迫法（Forcing）

在数学逻辑中，可构造集的概念与力迫法有深刻联系。Chevalley定理从代数几何角度提供了可构造集在态射下的稳定性，这与模型论中型（type）的构造性描述相呼应。

### 5. 态射的像的闭包与支配性

Chevalley定理可以用来精确描述态射像的闭包。若 $f: X \to Y$ 是有限型态射且 $X$ 是不可约的，则 $\overline{f(X)}$ 包含一个与 $f(X)$  dense 相交的开集。特别地，若 $f$ 是支配的（dominant，即像稠密），则 $f(X)$ 包含 $Y$ 的一个稠密开集。

---

*最后更新：2026-04-03 | 版本：v1.0.0*
