---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: 纤维化长正合列
---
# 纤维化长正合列

## Mathlib4 引用

```lean
import Mathlib.AlgebraicTopology.Homotopy.LongExactSequence

namespace AlgebraicTopology

/-- 纤维化诱导的同伦群长正合列 -/
theorem fibration_long_exact_sequence
    {E B F : Type*} [TopologicalSpace E]
    [TopologicalSpace B] [TopologicalSpace F]
    (p : E → B) [IsFibration p]
    (b₀ : B) (F := p⁻¹' {b₀}) :
    ∀ (n : ℕ),
      ExactSequence (
        π_{n+1} B → π_n F → π_n E → π_n B) := by
  -- 纤维化的同伦群长正合列
  sorry

/-- 道路提升性质 -/
theorem homotopy_lifting_property
    {E B : Type*} [TopologicalSpace E]
    [TopologicalSpace B] (p : E → B)
    [IsFibration p] {X : Type*} [TopologicalSpace X]
    (H : X × I → B) (h₀ : X → E)
    (comm : p ∘ h₀ = H ∘ (fun x => (x, 0))) :
    ∃ (H̃ : X × I → E),
      p ∘ H̃ = H ∧ H̃ ∘ (fun x => (x, 0)) = h₀ := by
  -- 同伦提升性质
  sorry

end AlgebraicTopology
```

## 数学背景

纤维化（fibration）的同伦群长正合列是代数拓扑中最基本且强大的计算工具之一。纤维丛诱导的长正合列将总空间、基空间和纤维的同伦群联系起来，使我们能够从已知的两个空间的同伦群计算第三个。这一理论由J.-P. Serre在1950年代系统发展，成为同伦论革命的核心。道路提升性质是纤维化的定义特征，它是覆盖空间提升性质的推广。

## 直观解释

纤维化长正合列如同一个"望远镜"，让我们窥见三个空间之间的深层联系。想象一个纤维丛 $F \to E \to B$：总空间 $E$ 可以看作是基空间 $B$ 上每个点都"附着"一个纤维 $F$ 的几何结构。长正合列告诉我们：$E$ 的"洞"（同伦群）来自 $B$ 和 $F$ 的洞，以及它们如何"纠缠"在一起（连接同态）。这就像通过组装部件来理解整体，同时考虑组装过程中的"扭曲"。

## 形式化表述

设 $p: E \to B$ 是纤维化，$b_0 \in B$，$F = p^{-1}(b_0)$ 是纤维。

**长正合列**：
$$\cdots \to \pi_{n+1}(B) \xrightarrow{\partial} \pi_n(F) \xrightarrow{i_*} \pi_n(E) \xrightarrow{p_*} \pi_n(B) \xrightarrow{\partial} \pi_{n-1}(F) \to \cdots$$

终止于：
$$\cdots \to \pi_0(F) \to \pi_0(E) \to \pi_0(B)$$

**连接同态** $\partial$：从 $B$ 中的球面提升为 $E$ 中的圆盘，边界给出 $F$ 中的球面。

## 证明思路

1. **道路提升**：证明纤维化有道路提升性质
2. **同伦提升**：推广到参数化的道路（同伦）
3. **正合性**：验证像等于核在每一阶段
4. **边界映射**：构造连接同态
5. **自然性**：验证映射关于空间对的自然性

## 示例

### 示例 1：环路空间纤维化

**问题**：描述 $\Omega X \to PX \to X$ 的长正合列。

**解答**：

$PX$（基于道路空间）可缩，因此 $\pi_n(PX) = 0$。

长正合列给出：$\pi_n(X) \cong \pi_{n-1}(\Omega X)$。

这就是同伦群的"悬垂定理"：$\pi_n(X) = \pi_{n-1}(\Omega X) = \pi_{n-2}(\Omega^2 X) = \cdots$。

### 示例 2：Hopf纤维化

**问题**：计算Hopf纤维化 $S^1 \to S^3 \to S^2$ 的长正合列。

**解答**：

$$\cdots \to \pi_n(S^1) \to \pi_n(S^3) \to \pi_n(S^2) \to \pi_{n-1}(S^1) \to \cdots$$

由于 $\pi_k(S^1) = 0$ 对 $k \geq 2$：
$$\pi_n(S^3) \cong \pi_n(S^2) \text{ 对 } n \geq 3$$

特别地，$\pi_3(S^2) \cong \pi_3(S^3) = \mathbb{Z}$，由Hopf映射生成。

## 应用

- **球面同伦群**：Serre的计算方法
- **环路空间**：$\Omega X$ 的同伦群
- **Eilenberg-MacLane空间**：分类空间理论
- **surgery理论**：切割和粘贴的几何
- **谱序列**：Leray-Serre谱序列的基础

## 相关概念

- 纤维化：几何对象
- 同伦群：长正合列的对象
- 覆盖空间：离散纤维的特例
- 纤维丛：局部平凡的纤维化
- 谱序列：同调版本的工具

## 参考

### 教材

- Hatcher, A. Algebraic Topology. Cambridge, 2002. Chapter 4
- May, J.P. A Concise Course in Algebraic Topology. Chicago, 1999.

### 论文

- Serre, J-P. Homologie singulière des espaces fibrés. Ann. of Math., 54: 425-505, 1951.
- Hurewicz, W. On the concept of fiber space. Proc. Nat. Acad. Sci. USA, 41: 956-961, 1955.

### 在线资源

- [Fibration Wikipedia](https://en.wikipedia.org/wiki/Fibration)
- [nLab - Fibration](https://ncatlab.org/nlab/show/fibration)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
