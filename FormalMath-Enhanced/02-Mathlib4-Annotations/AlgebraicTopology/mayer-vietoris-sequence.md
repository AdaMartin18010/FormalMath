---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: Mayer-Vietoris 序列 (Mayer-Vietoris Sequence)
---
# Mayer-Vietoris 序列 (Mayer-Vietoris Sequence)

## Mathlib4 引用

```lean
import Mathlib.AlgebraicTopology.TopologyHomotopy
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

namespace MayerVietoris

-- 注：Mathlib4 中经典的奇异同调 Mayer-Vietoris 序列
-- 目前在核心 Mathlib 中尚未完整形式化。
-- 以下给出同调代数中的标准长正合序列框架，
-- 其代数形式（Abel 范畴中的拉回/推出图）已在 Mathlib 中建立。

variable {A : Type*} [Category A] [Abelian A]
  {X Y Z W : A}
  (f : Z ⟶ X) (g : Z ⟶ Y) (h : X ⟶ W) (k : Y ⟶ W)

/-- 导出范畴中的 Mayer-Vietoris 型 distinguished triangle -/
theorem distinguished_triangle_of_pullback_pushout
    (hc : IsPushout f g h k) :
    ∃ (T : Triangle (DerivedCategory A)),
      T.obj₁ = Z ∧ T.obj₂ = X ⊞ Y ∧ T.obj₃ = W := by
  -- 导出范畴中由拉回/推出图诱导的 distinguished triangle
  -- 参见同调代数相关形式化。
  sorry

end MayerVietoris
```

## 数学背景

Mayer-Vietoris 序列是代数拓扑中最强大的计算工具之一，由 Walther Mayer 和 Leopold Vietoris 在1929-1930年间引入。该序列将一个拓扑空间分解为两个开子集的并，从而把该空间的上同调/同调群与这两个子集及其交的上同调/同调群联系起来。这一定理类似于微积分中的“分部积分”或组合数学中的容斥原理，使得复杂空间的拓扑不变量可以通过简单子空间的拼接来计算。它在证明 de Rham 定理、研究纤维丛谱序列、计算流形的不变量等方面都有核心应用。

## 直观解释

Mayer-Vietoris 序列告诉我们：**一个复杂空间的“洞”的结构，可以从它如何被两个简单部分拼接而成来推断**。想象一个甜甜圈（环面）被纵向切成两半：每一半都是一个圆柱（拓扑上同胚于圆盘），本身没有“洞”；但它们的交是两个不交的圆柱侧面。Mayer-Vietoris 序列正是通过这两半及其交的拓扑信息，重构出整个甜甜圈有一个二维“洞”和一个一维“洞”的事实。

从同调的角度看，序列把空间 $X = U \cup V$ 的同调与其部分 $U, V$ 以及交集 $U \cap V$ 的同调通过一长串连接同态联系起来，形成了一个周期为 3 的正合序列。

## 形式化表述

设 $X$ 为拓扑空间，$U, V \subseteq X$ 为开子集（或更一般地，满足适当切除条件的子集）且 $X = U \cup V$。

**同调版本的 Mayer-Vietoris 序列**：

$$\cdots \to H_n(U \cap V) \xrightarrow{(i_*, j_*)} H_n(U) \oplus H_n(V) \xrightarrow{k_* - l_*} H_n(X) \xrightarrow{\partial} H_{n-1}(U \cap V) \to \cdots$$

其中 $i: U \cap V \hookrightarrow U$，$j: U \cap V \hookrightarrow V$，$k: U \hookrightarrow X$，$l: V \hookrightarrow X$ 为含入映射，$\partial$ 为连接同态（connecting homomorphism）。

**上同调版本**：

$$\cdots \to H^n(X) \xrightarrow{(k^*, l^*)} H^n(U) \oplus H^n(V) \xrightarrow{i^* - j^*} H^n(U \cap V) \xrightarrow{\delta} H^{n+1}(X) \to \cdots$$

## 证明思路

1. **链复形的短正合序列**：构造相对链复形（或奇异链复形）的短正合序列。例如，将 $C_*(X)$ 与 $C_*(U) + C_*(V)$ 等同
2. **切除定理**：利用切除定理证明 $C_*(U) + C_*(V) \to C_*(X)$ 诱导同调同构
3. **蛇引理**：对链复形的短正合序列应用蛇引理（snake lemma），得到同调的长正合序列
4. **识别映射**：验证长正合序列中的映射恰好就是含入映射和连接同态

核心在于链复形的代数拼接与拓扑拼接之间的对应。

## 示例

### 示例 1：球面 $S^n$ 的同调

取 $U$ 为 $S^n$ 去掉北极的开半球，$V$ 为去掉南极的开半球。则 $U, V \cong \mathbb{R}^n$（可缩），$U \cap V \cong S^{n-1} \times \mathbb{R}$（同伦等价于 $S^{n-1}$）。由 Mayer-Vietoris 序列可归纳证明：

$$H_k(S^n) = \begin{cases} \mathbb{Z} & k = 0, n \\ 0 & \text{其他} \end{cases}$$

### 示例 2：环面 $T^2 = S^1 \times S^1$

取 $U$ 为去掉一个圆周的补集，$V$ 为另一个方向去掉圆周的补集。利用 Mayer-Vietoris 序列可计算出 $H_0(T^2) = \mathbb{Z}$，$H_1(T^2) = \mathbb{Z}^2$，$H_2(T^2) = \mathbb{Z}$。

### 示例 3：de Rham 上同调中的计算

设 $M$ 为光滑流形，$U, V$ 为开覆盖。de Rham 上同调的 Mayer-Vietoris 序列可用来计算 $H^*_{dR}(S^n)$、$H^*_{dR}(T^n)$ 等。例如，利用 $S^n = U \cup V$（两个可缩开集，交同伦等价于 $S^{n-1}$）可归纳证明 $H^k_{dR}(S^n)$ 的维数。

## 应用

- **代数拓扑计算**：球面、环面、实/复射影空间的同调群
- **纤维丛理论**：Leray-Serre 谱序列的基础
- **微分几何**：de Rham 定理的证明与流形不变量计算
- **代数几何**：层上同调的谱序列与 Čech 上同调
- **K-理论**：Bott 周期性定理的证明

## 相关概念

- 长正合序列 (Long Exact Sequence)：由短正合序列诱导的同调序列
- 连接同态 (Connecting Homomorphism)：长正合序列中的边界映射 $\partial$
- 蛇引理 (Snake Lemma)：同调代数中的核心工具
- 切除定理 (Excision Theorem)：切除子集不改变相对同调
- 相对同调 (Relative Homology)：空间对 $(X, A)$ 的同调群

## 参考

### 教材

- [Hatcher. Algebraic Topology. Cambridge, 2002. Chapter 2.2]
- [Rotman. An Introduction to Algebraic Topology. Springer, 1988. Chapter 6]

### 在线资源

- [Mathlib4 文档 - AlgebraicTopology][https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology.html]
- **注意**：Mathlib4 中经典的奇异同调 Mayer-Vietoris 序列目前尚未在核心库中完整形式化，但相关同调代数基础（正合序列、导出范畴）已有大量形式化工作。

---

*最后更新：2026-04-15 | 版本：v1.0.0*
