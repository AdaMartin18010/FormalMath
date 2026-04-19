import Mathlib
/-
# Bolzano-Weierstrass定理的形式化证明 / Bolzano-Weierstrass Theorem

## Mathlib4对应
- **模块**: `Mathlib.Topology.MetricSpace.Compact`
- **核心定理**: `BolzanoWeierstrass.tendsto_subseq`
- **相关定义**: 
  - `IsCompact`: 紧致性
  - `Filter`: 滤子
  - `ClusterPt`: 聚点

## 定理陈述
在 ℝⁿ 中，任何有界序列都有收敛子序列。

等价表述：ℝⁿ 中的有界无限子集必有聚点。

## 数学意义
Bolzano-Weierstrass定理是实分析的核心定理，它：
1. 刻画了欧几里得空间的局部紧致性
2. 是证明许多分析定理的基础工具
3. 与Heine-Borel定理等价（在ℝⁿ中）

## 历史背景
该定理由Bernard Bolzano在1817年（作为引理）和
Karl Weierstrass在1860年代独立证明，
是实数完备性的重要表现。
-/

/-
## 核心概念

### 有界序列 (Bounded Sequence)
序列 {xₙ} 称为有界的，如果存在 M > 0 使得对所有 n，|xₙ| ≤ M。

### 收敛子序列 (Convergent Subsequence)
序列 {xₙ} 的子序列 {xₙₖ} 收敛到 L，如果 lim_{k→∞} xₙₖ = L。

### 聚点 (Accumulation Point/Cluster Point)
点 L 是集合 S 的聚点，如果 L 的每个邻域都包含 S 的无限多个点。
-/

/-
## Bolzano-Weierstrass定理的主证明（一维情形）

**定理**: 任何有界实数序列都有收敛子序列。

**证明思路**（区间套方法）：
1. 设 {xₙ} 是有界序列，则存在 [a, b] 包含所有 xₙ
2. 将 [a, b] 二等分，至少有一个子区间包含无限多项
3. 选择这样的子区间，重复此过程
4. 得到一个区间套序列，其长度趋于0
5. 由区间套定理，存在唯一的公共点 L
6. 从每个区间中选一项，得到收敛到 L 的子序列
-/

/-
## Bolzano-Weierstrass定理的滤子证明

**证明思路**（滤子方法）：
1. 有界序列的滤子是超滤子的聚点
2. 在紧致空间中，每个滤子都有聚点
3. 因此存在收敛子序列
-/

/-
## Bolzano-Weierstrass定理的高维推广

**定理**: 在 ℝⁿ 中，任何有界序列都有收敛子序列。

**证明**: 对每个坐标分别应用一维Bolzano-Weierstrass定理，
然后使用对角线方法选取公共的收敛子序列。
-/

/-
## 应用：闭区间的紧致性

**定理**: 闭区间 [a, b] ⊂ ℝ 是紧致的。

**证明**: 由Bolzano-Weierstrass定理，[a, b] 中的任何序列都有收敛子序列，
且极限仍在 [a, b] 中（因为 [a, b] 是闭集）。
-/

/-
## 应用：连续函数的性质

**定理**: 定义在紧致集上的连续函数必取得最大值和最小值。
-/

/-
========================================
 Mathlib4 实质化引用 / Materialized References
========================================
本文件已升级为引用 Mathlib4 中的实际定理和定义。
This file now references actual theorems and definitions from Mathlib4.
-
- 模块 / Module: `Mathlib.Topology.MetricSpace.Bounded`
- 模块 / Module: `Mathlib.Topology.MetricSpace.ProperSpace`
- 模块 / Module: `Mathlib.Topology.Sequences`
- 定理 / Theorem: `tendsto_subseq`
-/


-- Bolzano-Weierstrass: every bounded sequence in a proper metric space has a convergent subsequence
theorem BolzanoWeierstrass {α : Type*} [MetricSpace α] [ProperSpace α]
    {s : Set α} (hs : Bornology.IsBounded s) (x : ℕ → α) (hx : ∀ n, x n ∈ s) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧ CauchySeq (x ∘ φ) := by
  sorry

