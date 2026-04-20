---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: 切除定理 (Excision Theorem)
---
# 切除定理 (Excision Theorem)

## Mathlib4 引用

```lean
import Mathlib.AlgebraicTopology.SingularHomology
import Mathlib.AlgebraicTopology.RelativeHomology

namespace ExcisionTheorem

variable {X : Type*} [TopologicalSpace X] {A U : Set X}
  (hU : IsOpen U) (hAclosed : IsClosed A) (hUA : U ⊆ A)

/-- 切除定理 -/
theorem excision (n : ℕ) :
    H_n (X \ U, A \ U) ≅ H_n (X, A) := by
  -- 小单纯形论证
  sorry

/-- 切除定理的等价形式 -/
theorem excision_equivalent {Z : Set X} (hZ : closure Z ⊆ interior A) (n : ℕ) :
    H_n (X \ Z, A \ Z) ≅ H_n (X, A) := by
  -- 由标准形式推出
  sorry

end ExcisionTheorem
```

## 数学背景

切除定理是同调代数代数拓扑中最基本、最重要的定理之一，它与同伦不变性、长正合列一起构成了整个同调论的公理化基础（Eilenberg-Steenrod公理）。切除定理表明在同调计算中可以"切除"某些内部子集而不改变相对同调群，这为计算复杂空间的同调群提供了强有力的工具，是证明Mayer-Vietoris序列、建立胞腔同调与奇异同调等价性等核心结果的关键步骤。

### 相对同调群

**定义（相对同调群）**：设 $X$ 是拓扑空间，$A \subseteq X$ 是子空间。相对奇异链复形 $C_*(X, A)$ 定义为商复形：

$$C_n(X, A) = C_n(X) / C_n(A)$$

其中 $C_n(X)$ 是 $X$ 上的 $n$ 维奇异链群（由奇异 $n$-单形的形式线性组合生成），边界算子 $\partial_n: C_n(X) \to C_{n-1}(X)$ 将 $A$ 中的链映到 $C_{n-1}(A)$，因此在商复形上诱导出良定义的边界算子。

**$n$ 维相对同调群**定义为：

$$H_n(X, A) = \ker(\partial_n: C_n(X, A) \to C_{n-1}(X, A)) / \text{im}(\partial_{n+1}: C_{n+1}(X, A) \to C_n(X, A))$$

几何上，$H_n(X, A)$ 捕获了 $X$ 中"相对 $A$ 的 $n$ 维洞"，即那些在 $X$ 中不是边界的 $n$ 维链模去那些在 $A$ 中是边界的部分。

### 切除的思想

"切除"（excision）一词的字面含义是"切除、挖去"。在同调论中，它指的是：如果要从 $(X, A)$ 的同调中移除某个子集 $U$，只要 $U$ "不太大"（即 $U$ 的闭包包含在 $A$ 的内部中），相对同调群保持不变。

## 切除定理的陈述

**定理（切除定理）**：设 $X$ 是拓扑空间，$A \subseteq X$ 是子空间。若子集 $U \subseteq A$ 满足 $\overline{U} \subseteq \text{int}(A)$（即 $U$ 的闭包包含在 $A$ 的内部中），则包含映射：

$$i: (X \setminus U, A \setminus U) \hookrightarrow (X, A)$$

诱导同调群的同构：

$$i_*: H_n(X \setminus U, A \setminus U) \xrightarrow{\cong} H_n(X, A)$$

对所有 $n \geq 0$ 成立。

**等价形式**：若 $Z \subseteq A$ 满足 $\overline{Z} \subseteq \text{int}(A)$，则：

$$H_n(X \setminus Z, A \setminus Z) \cong H_n(X, A)$$

## 证明概要

切除定理的证明是代数拓扑中最精巧的论证之一，核心思想是**细分（subdivision）**：任何相对同调类都可以由一个其单形"足够小"的链代表，使得每个单形要么完全在 $X \setminus U$ 中，要么完全在 $\text{int}(A)$ 中。

### 关键引理：小单纯形引理

**引理**：设 $\mathcal{U} = \{U_\alpha\}$ 是 $X$ 的开覆盖。记 $C_n^{\mathcal{U}}(X)$ 为所有奇异 $n$-单形的形式线性组合生成的子群，其中每个单形的像完全包含于某个 $U_\alpha$ 中。则包含映射：

$$C_*^{\mathcal{U}}(X) \hookrightarrow C_*(X)$$

是链同伦等价。特别地，它诱导同调群的同构。

### 切除定理的证明

**证明**：取开覆盖 $\mathcal{U} = \{X \setminus \overline{U}, \text{int}(A)\}$。由小单纯形引理，$H_n(X, A)$ 可以由相对于 $A$ 的"小" $n$-链代表。

考虑链复形的短正合列：

$$0 \to C_*(A) \to C_*(X) \to C_*(X, A) \to 0$$

对"小"链，有正合列：

$$0 \to C_*^{\mathcal{U}}(A) \to C_*^{\mathcal{U}}(X) \to C_*^{\mathcal{U}}(X, A) \to 0$$

注意到：
- 完全落在 $\text{int}(A)$ 中的单形在商 $C_*^{\mathcal{U}}(X, A)$ 中为零；
- 完全落在 $X \setminus \overline{U}$ 中的单形自然对应于 $C_*(X \setminus U, A \setminus U)$ 中的元素。

因此：

$$C_*^{\mathcal{U}}(X, A) \cong C_*(X \setminus U, A \setminus U)$$

由小单纯形引理，$H_n^{\mathcal{U}}(X, A) \cong H_n(X, A)$，而左边正是 $H_n(X \setminus U, A \setminus U)$。因此：

$$H_n(X \setminus U, A \setminus U) \cong H_n(X, A)$$

### 利用Mayer-Vietoris的替代证明

若已建立Mayer-Vietoris序列，也可以从公理化角度证明切除定理。在Eilenberg-Steenrod公理体系中，切除公理是基本公理之一，它与同伦公理、正合公理、维数公理一起刻画了同调理论。

实际上，对满足Eilenberg-Steenrod公理的理论，切除定理等价于正合列的长正合列的存在性。 $\square$

## 例子

### 例子1：球面的相对同调

设 $X = S^n$ 是 $n$ 维球面，$A = D_+^n$ 是上半球（闭集），$U = D_+^n \setminus \{\text{赤道}\}$。则 $X \setminus U \cong D_-^n$（下半闭球），$A \setminus U \cong S^{n-1}$（赤道）。

由切除：

$$H_k(D_-^n, S^{n-1}) \cong H_k(S^n, D_+^n)$$

而 $D_+^n$ 可缩，故 $H_k(S^n, D_+^n) \cong \tilde{H}_k(S^n)$（约化同调）。这与已知的 $H_k(D^n, S^{n-1}) \cong \tilde{H}_{k-1}(S^{n-1})$（由长正合列）一致，给出 $H_k(S^n) \cong H_{k-1}(S^{n-1})$。

### 例子2：挖去一点的平面

设 $X = \mathbb{R}^2$，$A = D^2$（单位闭圆盘），$U = D_{1/2}^2$（半径 $1/2$ 的闭圆盘）。$\overline{U} = U \subseteq \text{int}(A) = D^2$。

$X \setminus U = \mathbb{R}^2 \setminus D_{1/2}^2$（平面挖去小圆盘），$A \setminus U = D^2 \setminus D_{1/2}^2$（圆环）。

由切除：$H_k(\mathbb{R}^2 \setminus D_{1/2}^2, D^2 \setminus D_{1/2}^2) \cong H_k(\mathbb{R}^2, D^2)$。而 $H_k(\mathbb{R}^2, D^2) \cong \tilde{H}_k(S^1)$（因为 $\mathbb{R}^2/D^2 \simeq S^2$，更准确地说相对同调对应于商空间的约化同调）。

### 例子3：Mayer-Vietoris的应用前奏

考虑 $S^n = D_+^n \cup D_-^n$，交集为赤道 $S^{n-1}$。Mayer-Vietoris序列将 $S^n$ 的同调与 $D_+^n$、$D_-^n$ 和 $S^{n-1}$ 的同调联系起来。切除定理是建立Mayer-Vietoris序列的关键工具之一。

## 应用

### 1. Mayer-Vietoris序列

切除定理是推导Mayer-Vietoris序列的核心工具。若 $X = U \cup V$ 是两个开集的并，则对 $(U, U \cap V)$ 使用切除（切除 $U \setminus V$），可以将相对同调与 $V$ 的同调联系起来，从而建立长正合列：

$$\cdots \to H_n(U \cap V) \to H_n(U) \oplus H_n(V) \to H_n(X) \to H_{n-1}(U \cap V) \to \cdots$$

Mayer-Vietoris序列是计算复杂空间同调的最有力工具之一。

### 2. 球面的同调计算

利用切除和Mayer-Vietoris，可以归纳地计算球面的同调：

$$H_k(S^n) \cong \begin{cases} \mathbb{Z} & k = 0, n \\ 0 & \text{否则} \end{cases}$$

这是代数拓扑的基石性结果，切除定理在其中扮演关键角色。

### 3. 胞腔同调的等价性

切除定理用于证明胞腔同调（cellular homology）与奇异同调（singular homology）的等价性。对CW复形 $X$，胞腔链复形的构造依赖于对每个胞腔对 $(X^n, X^{n-1})$ 的相对同调的理解，而切除定理允许我们将这些相对同调与球面的约化同调等同。

### 4. Jordan曲线定理

Jordan曲线定理（平面上的简单闭曲线将平面分成两个连通分支）的证明可以使用同调论和切除定理。通过对 $(\mathbb{R}^2, C)$（$C$ 是Jordan曲线）的相对同调进行分析，利用切除将问题局部化。

---

*最后更新：2026-04-03 | 版本：v1.0.0*
