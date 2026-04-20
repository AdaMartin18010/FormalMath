---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: Frobenius定理 (Frobenius Theorem)
---
# Frobenius定理 (Frobenius Theorem)

## Mathlib4 引用

```lean
import Mathlib.Geometry.Manifold.Distribution
import Mathlib.Geometry.Manifold.Frobenius

namespace FrobeniusTheorem

variable {M : Type*} [SmoothManifoldWithCorners (𝓡 n) M]
variable {D : Distribution M k} (hinvolutive : D.IsInvolutive)

/-- Frobenius定理：可积分布存在积分叶状结构 -/
theorem frobenius_theorem (x : M) :
    ∃ (U : OpenNhds x) (F : Foliation U k),
      ∀ y ∈ U, TangentSpace (Leaf F y) y = D y := by
  -- 归纳法和常秩定理
  sorry

/-- 全局形式 -/
theorem frobenius_global [M.Compact] :
    ∃ F : Foliation M k, ∀ x, TangentSpace (Leaf F x) x = D x := by
  -- 局部结果拼接
  sorry

end FrobeniusTheorem
```

## 数学背景

Frobenius定理由德国数学家Ferdinand Georg Frobenius于1877年证明，是微分几何中关于分布可积性的基本结果。它给出了流形上一个光滑分布能够"积分"为叶状结构的充分必要条件，即分布必须是对合的（involutive）。这一定理在偏微分方程理论、Lie群与Lie代数、控制理论以及现代物理的杨-Mills理论等领域都有深刻的应用。

### 分布的定义

**定义（分布）**：设 $M$ 是 $n$ 维光滑流形，$k$ 是满足 $1 \leq k \leq n$ 的整数。$M$ 上的一个**$k$维分布**（distribution，或称切子丛）是一个映射 $D$，它对每点 $x \in M$ 指定切空间的一个 $k$ 维子空间 $D_x \subseteq T_x M$，并且 $D$ 在局部上由 $k$ 个光滑向量场生成。

等价地，$D$ 是切丛 $TM$ 的一个秩为 $k$ 的光滑子丛。

**例子**：在 $\mathbb{R}^3$ 中，由向量场 $X_1 = \partial_x$，$X_2 = \partial_y$ 生成的二维分布在每点给出 $xy$-平面的切空间。

### 对合性

**定义（对合分布）**：分布 $D$ 称为**对合的**（involutive），如果对任意两个属于 $D$ 的光滑向量场 $X, Y$（即 $X_x, Y_x \in D_x$ 对所有 $x$），它们的Lie括号 $[X, Y]$ 也属于 $D$（即 $[X, Y]_x \in D_x$ 对所有 $x$）。

**Lie括号回顾**：在局部坐标下，若 $X = \sum a_i \partial_{x_i}$，$Y = \sum b_i \partial_{x_i}$，则：

$$[X, Y] = \sum_{i,j} \left(a_j \frac{\partial b_i}{\partial x_j} - b_j \frac{\partial a_i}{\partial x_j}\right) \frac{\partial}{\partial x_i}$$

对合性的直观含义是：分布 $D$ 在Lie括号下"封闭"。

### 可积性与叶状结构

**定义（积分流形）**：浸入子流形 $N \subseteq M$ 称为分布 $D$ 的**积分流形**（integral manifold），如果对所有 $x \in N$，有 $T_x N = D_x$。

**定义（叶状结构）**：$M$ 的一个**$k$维叶状结构**（foliation）是将 $M$ 分解为互不相交的 $k$ 维连通浸入子流形（称为**叶**或**叶片**，leaves）的分解，使得每点有坐标卡 $(U, \phi)$，其中 $\phi: U \to \mathbb{R}^n = \mathbb{R}^k \times \mathbb{R}^{n-k}$，且每个叶与 $U$ 的交是形如 $\phi^{-1}(\mathbb{R}^k \times \{c\})$ 的集合（即坐标卡将叶片映为 $\mathbb{R}^k$ 的平行拷贝）。

## Frobenius定理的陈述

**定理（Frobenius，局部形式）**：设 $M$ 是光滑流形，$D$ 是 $M$ 上的光滑 $k$ 维分布。则 $D$ 是可积的（即过每点存在积分流形）当且仅当 $D$ 是对合的。此外，若 $D$ 是对合的，则存在过每点的唯一极大连通积分流形，且这些积分流形构成 $M$ 的一个叶状结构。

形式化地，若 $D$ 对合，则对任意 $x \in M$，存在 $x$ 的邻域 $U$ 和 $U$ 上的坐标 $(x_1, \ldots, x_n)$，使得：

$$D|_U = \text{span}\left\{\frac{\partial}{\partial x_1}, \ldots, \frac{\partial}{\partial x_k}\right\}$$

即 $D$ 在适当坐标下由前 $k$ 个坐标偏导数生成。

**定理（Frobenius，全局形式）**：若 $M$ 是紧流形（或更一般地，满足适当完备性条件），$D$ 是对合分布，则 $M$ 被积分流形叶化。

## 证明概要

Frobenius定理的证明通常采用对维数 $k$ 的归纳法，核心思想是逐步构造积分流形。

### 证明（归纳法）

**$k = 1$ 的情形**：一维分布由单个非零向量场 $X$ 生成。由常微分方程的存在唯一性定理，过每点存在唯一的极大积分曲线，这正是一维积分流形。此时对合性是自动满足的（$[X, X] = 0$）。

**归纳步骤**：假设对 $k-1$ 维分布定理成立。设 $D$ 是 $k$ 维对合分布。在点 $p$ 附近，$D$ 由光滑向量场 $X_1, \ldots, X_k$ 生成。

**步骤1**：考虑由 $X_1$ 生成的流 $\phi_t$。利用 $D$ 的对合性，可以证明 $\phi_t$ 保持 $D$ 不变（在适当意义下）。

**步骤2**：在 $X_1$ 的横截面上，$D$ 诱导一个 $k-1$ 维分布。验证这个诱导分布仍然是对合的。

**步骤3**：由归纳假设，横截面上存在 $k-1$ 维积分流形。将 $X_1$ 的流作用在这些积分流形上，得到 $k$ 维积分流形。

**步骤4**：验证所得子流形确实是 $D$ 的积分流形，并且构成叶状结构。

### 坐标化的证明

另一种证明直接构造Frobenius坐标。设 $D$ 由对合向量场 $X_1, \ldots, X_k$ 生成。利用对合性 $[X_i, X_j] = \sum_l c_{ij}^l X_l$，可以逐步构造坐标函数 $x_1, \ldots, x_n$，使得 $X_i = \partial_{x_i}$（$i = 1, \ldots, k$）。

具体地，先选取坐标使得 $X_1 = \partial_{x_1}$。然后利用对合性证明可以在 $x_1 = \text{const}$ 的 slice 上递归地处理 $X_2, \ldots, X_k$。 $\square$

## 例子

### 例子1：可积的二维分布

在 $\mathbb{R}^3$ 中，考虑由 $X = \partial_x$，$Y = \partial_y + x\partial_z$ 生成的二维分布 $D$。

计算Lie括号：

$$[X, Y] = [\partial_x, \partial_y + x\partial_z] = \partial_z$$

这不属于 $D$（因为 $D$ 由 $X, Y$ 生成，而 $Y$ 的 $z$ 分量是 $x$，不是常数），所以 $D$ 不是对合的。由Frobenius定理，$D$ 不可积。

现在修改 $Y$ 为 $Y' = \partial_y$。则 $[X, Y'] = 0 \in D$，$D' = \text{span}\{\partial_x, \partial_y\}$ 是对合的。积分流形是水平平面 $z = \text{const}$，构成叶状结构。

### 例子2：接触分布（不可积）

在 $\mathbb{R}^3$ 的标准接触结构中，分布 $D = \ker(\alpha)$，其中 $\alpha = dz - x dy$ 是接触形式。$D$ 由 $X = \partial_x$，$Y = \partial_y + x\partial_z$ 生成。

计算：$[X, Y] = \partial_z \notin D$。因此 $D$ 不是对合的，不可积。这是接触几何的基本例子，与Frobenius定理形成鲜明对比。

### 例子3：Lie群上的左不变分布

设 $G$ 是Lie群，$\mathfrak{g}$ 是其Lie代数。任何李子代数 $\mathfrak{h} \subseteq \mathfrak{g}$ 对应 $G$ 上的一个左不变分布 $D$，由左平移 $\mathfrak{h}$ 得到。

由于 $\mathfrak{h}$ 对Lie括号封闭，$D$ 是对合的。由Frobenius定理，$D$ 可积，积分流形是 $G$ 的连通李子群 $H$（或其陪集）。这是Lie理论中Lie子群存在定理的核心。

### 例子4：可积方程组

考虑一阶偏微分方程组：

$$\frac{\partial u}{\partial x_i} = f_i(x, u), \quad i = 1, \ldots, n$$

可积条件要求 $\frac{\partial f_i}{\partial x_j} + \frac{\partial f_i}{\partial u} f_j = \frac{\partial f_j}{\partial x_i} + \frac{\partial f_j}{\partial u} f_i$（即混合偏导数相等）。这正是对应分布对合性的条件，由Frobenius定理保证了解的存在性。

## 应用

### 1. 偏微分方程的可积性条件

Frobenius定理为判断超定偏微分方程组是否有解提供了标准工具。给定方程组 $X_i(u) = f_i$，其中 $X_i$ 是向量场，可积的充分必要条件是分布 $\text{span}\{X_i\}$ 对合（在适当意义下）。这在微分几何、数学物理和工程中有广泛应用。

### 2. Lie群和Lie代数

Frobenius定理是Lie理论的基础工具之一。给定Lie群 $G$ 和其Lie代数 $\mathfrak{g}$ 的子代数 $\mathfrak{h}$，Frobenius定理保证存在唯一的连通Lie子群 $H \subseteq G$ 使得 $T_e H = \mathfrak{h}$。这是Lie对应（Lie groups $\leftrightarrow$ Lie algebras）的核心步骤。

### 3. 控制理论

在非线性控制理论中，系统的可达集（reachable set）可以通过分布的积分流形来描述。若控制向量场生成的分布是对合的，则系统具有某种"完全可控性"（在分布的积分流形内）。Frobenius定理用于分析系统的可积性和可分解性。

### 4. 杨-Mills理论

在现代理论物理中，杨-Mills理论的场方程与主丛上的联络曲率有关。Frobenius定理的一个版本（关于平坦联络的可积性）表明：曲率 $F = 0$ 当且仅当水平分布可积，即存在平行的局部截面。这是规范场论中理解真空解和对称性的基本工具。

### 5. 叶状结构的分类

Frobenius定理开启了叶状结构理论这一重要研究领域。虽然对合性是可积性的充分必要条件，但叶状结构的全局性质（如叶的拓扑、holonomy群等）仍然极其丰富。Haefliger、Thurston等数学家在叶状结构分类方面做出了奠基性工作。

---

*最后更新：2026-04-03 | 版本：v1.0.0*
