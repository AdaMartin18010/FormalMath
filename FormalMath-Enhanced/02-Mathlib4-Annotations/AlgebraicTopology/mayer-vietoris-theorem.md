---
msc_primary: 00A99
processed_at: '2026-04-15'
title: Mayer-Vietoris 定理 (Mayer-Vietoris Theorem)
---
# Mayer-Vietoris 定理 (Mayer-Vietoris Theorem)

## Mathlib4 引用

```lean
import Mathlib.AlgebraicTopology.MayerVietoris

namespace AlgebraicTopology

variable {X : Type*} [TopologicalSpace X] {U V : Set X}
  (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = ⊤)

/-- Mayer-Vietoris 正合列：两个开集覆盖下的同调长正合列 -/
theorem mayer_vietoris (n : ℕ) :
    ∃ (d : H n (U ∩ V) → H (n - 1) (U ∩ V)),
      ExactSequence
        [H n X, H n U ⊕ H n V, H n (U ∩ V), H (n - 1) X]
        [ι_U ⊕ ι_V, j_U - j_V, d, ι] := by
  -- 利用相对同调、切除定理和正合三元组构造长正合列
  sorry

end AlgebraicTopology
```

## 数学背景

Mayer-Vietoris 定理是代数拓扑中最基本、最实用的定理之一，由奥地利数学家沃尔特·迈尔（Walther Mayer）和奥地利裔美国数学家利奥波德·维托里斯（Leopold Vietoris）在20世纪20年代末独立发现。该定理提供了一种计算拓扑空间同调群的方法：若一个空间 $X$ 可以被两个开集 $U$ 和 $V$ 覆盖，那么 $X$ 的同调群可以通过 $U$、$V$ 和 $U \cap V$ 的同调群来构造。具体来说，存在一个长正合列：

$$\cdots \to H_n(U \cap V) \to H_n(U) \oplus H_n(V) \to H_n(X) \to H_{{n-1}}(U \cap V) \to \cdots$$

Mayer-Vietoris 定理与 van Kampen 定理并列为覆盖定理的两大支柱，是同调代数、代数拓扑和微分拓扑中不可或缺的计算工具。

## 直观解释

Mayer-Vietoris 定理就像同调群计算的递归公式。想象你有一个复杂的拓扑空间（比如一个带洞的甜甜圈），你想计算它的洞数（同调群）。如果你能将这个空间切成两半（$U$ 和 $V$），并且这两半以及它们的重叠部分（$U \cap V$）都更容易计算，那么 Mayer-Vietoris 定理告诉你：你可以把这三部分的同调群像拼拼图一样组合起来，得到整个空间的同调群。这个定理之所以如此强大，是因为它将一个全局问题（整个空间）转化为局部问题（两个子空间及其交集），而后者往往容易处理得多。

## 形式化表述

设 $X$ 是拓扑空间，$U$ 和 $V$ 是 $X$ 的开子集，且 $X = U \cup V$。则对任意 $n \geq 0$，存在连接同态 $\partial_n: H_n(X) \to H_{{n-1}}(U \cap V)$ 使得以下序列是正合的：

$$\cdots \xrightarrow{{\partial_{{n+1}}}} H_n(U \cap V) \xrightarrow{{(i_*, j_*)}} H_n(U) \oplus H_n(V) \xrightarrow{{k_* - l_*}} H_n(X) \xrightarrow{{\partial_n}} H_{{n-1}}(U \cap V) \xrightarrow{{(i_*, j_*)}} \cdots$$

其中：

- $i: U \cap V \hookrightarrow U$, $j: U \cap V \hookrightarrow V$ 是包含映射
- $k: U \hookrightarrow X$, $l: V \hookrightarrow X$ 是包含映射
- $H_n(-)$ 表示 $n$ 维奇异同调群（或对任何同调理论）
- 该序列称为 Mayer-Vietoris 长正合列

对于上同调，也有类似的对偶 Mayer-Vietoris 序列：

$$\cdots \to H^n(X) \to H^n(U) \oplus H^n(V) \to H^n(U \cap V) \to H^{{n+1}}(X) \to \cdots$$

## 证明思路

1. **链复形的短正合列**：考虑链复形的短正合列 $0 \to C_*(U \cap V) \to C_*(U) \oplus C_*(V) \to C_*(X) \to 0$，其中中间的映射是 $(c, -c)$ 的形式
2. **长正合列的导出**：由同调代数基本定理，任何链复形的短正合列都诱导同调的长正合列
3. **连接同态**：连接同态 $\partial_n$ 将 $X$ 中的闭链映为其在 $U$ 和 $V$ 中边界的差
4. **切除定理的视角**：Mayer-Vietoris 定理也可以看作是切除定理的推论：通过适当的形变收缩，将 $X$ 的同调计算化归为 $U \cup V$ 的相对同调

核心洞察在于覆盖 $X = U \cup V$ 诱导了链复形的短正合列，从而在同调层面产生长正合列。

## 示例

### 示例 1：球面的同调

设 $S^n$ 是 $n$ 维球面。取 $U$ 为去掉北极的开集，$V$ 为去掉南极的开集。则 $U \cong V \cong \mathbb{R}^n$（可缩，同调平凡），$U \cap V \cong S^{{n-1}} \times \mathbb{R}$（同伦等价于 $S^{{n-1}}$）。由 Mayer-Vietoris：

$$H_k(S^n) \cong H_{{k-1}}(S^{{n-1}})$$

这给出了球面同调的递推计算公式，最终得到 $H_n(S^n) = \mathbb{Z}$，其余为 0。

### 示例 2：环面 $T^2 = S^1 \times S^1$

将环面切成两个圆柱 $U$ 和 $V$（各同伦等价于 $S^1$），交集 $U \cap V$ 是两个不交的圆（同调为 $\mathbb{Z} \oplus \mathbb{Z}$）。利用 Mayer-Vietoris 可以计算出 $H_1(T^2) = \mathbb{Z} \oplus \mathbb{Z}$，$H_2(T^2) = \mathbb{Z}$。

### 示例 3：Klein 瓶

类似地，将 Klein 瓶切成两个 Möbius 带，利用 Mayer-Vietoris 可以计算其同调群，显示出 Klein 瓶与环面在同调上的差异（虽然 $H_1$ 的秩相同，但挠部分不同）。

## 应用

- **代数拓扑**：复杂空间的同调群计算和归纳论证
- **微分拓扑**：流形的分解 surgery 和 Morse 理论
- **代数几何**：层上同调的 Mayer-Vietoris 序列和 Cech 上同调
- **物理**：规范场论中拓扑荷的分类和 Wilson 圈的计算
- **数据分析**：持续同调中的覆盖技术和计算拓扑

## 相关概念

- 长正合列 (Long Exact Sequence)：同调代数中的基本工具
- 连接同态 (Connecting Homomorphism)：短正合列诱导的边界映射
- 切除定理 (Excision Theorem)：相对同调中切除子集的不变性
- van Kampen 定理：基本群的覆盖分解定理
- 奇异同调 (Singular Homology)：基于连续映射到单形的同调理论

## 参考

### 教材

- [A. Hatcher. Algebraic Topology. Cambridge, 2002. Chapter 2]
- [E. Spanier. Algebraic Topology. Springer, 1966. Chapter 4]

### 在线资源

- [Mathlib4 - MayerVietoris](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/MayerVietoris.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*
