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

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Compact
import Mathlib.Topology.Sequences
import Mathlib.Topology.Bases
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Data.Real.Basic

universe u v

namespace BolzanoWeierstrassTheorem

open Topology Filter Metric Set

/-
## 核心概念

### 有界序列 (Bounded Sequence)
序列 {xₙ} 称为有界的，如果存在 M > 0 使得对所有 n，|xₙ| ≤ M。

### 收敛子序列 (Convergent Subsequence)
序列 {xₙ} 的子序列 {xₙₖ} 收敛到 L，如果 lim_{k→∞} xₙₖ = L。

### 聚点 (Accumulation Point/Cluster Point)
点 L 是集合 S 的聚点，如果 L 的每个邻域都包含 S 的无限多个点。
-/

-- 序列有界的定义
def SeqBounded {X : Type*} [MetricSpace X] (x : ℕ → X) : Prop :=
  ∃ (M : ℝ), ∀ (n : ℕ), dist (x n) (x 0) ≤ M

-- 收敛子序列的定义
def HasConvergentSubseq {X : Type*} [MetricSpace X] [TopologicalSpace X]
    (x : ℕ → X) : Prop :=
  ∃ (φ : ℕ → ℕ), StrictMono φ ∧ ∃ (L : X), Tendsto (x ∘ φ) atTop (𝓝 L)

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

-- 区间套定理
theorem nested_intervals {a b : ℕ → ℝ} (ha : Monotone a) (hb : Antitone b)
    (hle : ∀ n, a n ≤ b n) (hlim : Tendsto (fun n => b n - a n) atTop (𝓝 0)) :
    ∃ (L : ℝ), ∀ n, a n ≤ L ∧ L ≤ b n := by
  /- 证明思路：
     1. {aₙ} 单调递增有上界（被 b₀ 限制），所以收敛
     2. {bₙ} 单调递减有下界（被 a₀ 限制），所以收敛
     3. 由于 bₙ - aₙ → 0，所以极限相同
  -/
  have ha_conv : ∃ La, Tendsto a atTop (𝓝 La) := by
    apply tendsto_atTop_ciSup
    · /- 证明 {aₙ} 有上界 -/
      use b 0
      intro n
      have : a n ≤ b n := hle n
      have : b n ≤ b 0 := hb (by linarith)
      linarith
    · /- 单调性 -/
      exact ha
  
  rcases ha_conv with ⟨La, ha_tendsto⟩
  
  have hb_conv : ∃ Lb, Tendsto b atTop (𝓝 Lb) := by
    apply tendsto_atTop_ciInf
    · /- 证明 {bₙ} 有下界 -/
      use a 0
      intro n
      have : a n ≤ b n := hle n
      have : a 0 ≤ a n := ha (by linarith)
      linarith
    · /- 单调性（递减） -/
      intro m n hmn
      exact hb hmn
  
  rcases hb_conv with ⟨Lb, hb_tendsto⟩
  
  /- 证明 La = Lb -/
  have h_La_eq_Lb : La = Lb := by
    have h_diff : Tendsto (fun n => b n - a n) atTop (𝓝 (Lb - La)) := by
      apply Tendsto.sub hb_tendsto ha_tendsto
    have h_zero : Lb - La = 0 := by
      exact tendsto_nhds_unique h_diff hlim
    linarith
  
  use La
  intro n
  constructor
  · /- La ≥ aₙ：因为 {aₙ} 递增且收敛到 La -/
    have : a n ≤ La := by
      apply le_of_tendsto_of_tendsto' ha_tendsto tendsto_const_nhds
      intro m hm
      exact ha hm
    exact this
  · /- La ≤ bₙ：因为 {bₙ} 递减且收敛到 Lb = La -/
    rw [← h_La_eq_Lb]
    have : b n ≥ Lb := by
      apply ge_of_tendsto_of_tendsto' hb_tendsto tendsto_const_nhds
      intro m hm
      exact hb hm
    linarith

-- Bolzano-Weierstrass定理（一维）- 使用Mathlib4的结果
theorem bolzano_weierstrass_1d (x : ℕ → ℝ) (hbounded : SeqBounded x) :
    HasConvergentSubseq x := by
  /- 证明思路（区间套方法）：
     1. 由有界性，存在 [a, b] 包含所有 xₙ
     2. 使用Mathlib4的紧致性结果
  -/
  rcases hbounded with ⟨M, hM⟩
  
  /- 证明范围在 [-M, M] 中 -/
  have h_range : ∀ n, x n ∈ Icc (-M) M := by
    intro n
    constructor
    · /- xₙ ≥ -M -/
      have h_dist : |x n - x 0| ≤ M := by
        apply le_of_lt
        apply dist_lt_of_dist_le
        exact hM n
        linarith [show M > 0 from by
          by_contra h
          push_neg at h
          have : |x 1 - x 0| ≤ M := by
            apply le_of_lt
            apply dist_lt_of_dist_le
            exact hM 1
            linarith
          have : |x 1 - x 0| ≤ 0 := by linarith
          have h_zero : x 1 = x 0 := by
            have h1 : x 1 - x 0 = 0 := by
              apply abs_nonpos.mp
              linarith
            linarith
          /- 此时 M = 0，序列是常数列，直接构造收敛子序列 -/
          have h_const : ∀ n, x n = x 0 := by
            intro n
            have h_dist : |x n - x 0| ≤ 0 := by
              have : |x n - x 0| ≤ M := by
                apply le_of_lt
                apply dist_lt_of_dist_le
                exact hM n
                linarith
              linarith
            have : x n - x 0 = 0 := by
              apply abs_nonpos.mp
              linarith
            linarith
          nlinarith]
      linarith [abs_le.mp h_dist]
    · /- xₙ ≤ M -/
      have h_dist : |x n - x 0| ≤ M := by
        apply le_of_lt
        apply dist_lt_of_dist_le
        exact hM n
        exact hM 0
      linarith [abs_le.mp h_dist]
  
  /- 使用闭区间 [-M, M] 的紧致性 -/
  have h_compact : IsCompact (Icc (-M) M) := by
    exact isCompact_Icc
  
  /- 序列在紧致集中，必有收敛子序列 -/
  have h_subseq : ∃ (φ : ℕ → ℕ), StrictMono φ ∧ ∃ (L : ℝ), Tendsto (x ∘ φ) atTop (𝓝 L) := by
    apply IsCompact.tendsto_subseq h_compact
    · intro n
      exact h_range n
    · use 0
  
  exact h_subseq

/-
## Bolzano-Weierstrass定理的滤子证明

**证明思路**（滤子方法）：
1. 有界序列的滤子是超滤子的聚点
2. 在紧致空间中，每个滤子都有聚点
3. 因此存在收敛子序列
-/

-- 滤子版本的Bolzano-Weierstrass定理
theorem bolzano_weierstrass_filter {X : Type*} [MetricSpace X] [CompactSpace X]
    (x : ℕ → X) :
    ∃ (L : X), ClusterPt L (atTop.map x) := by
  /- 在紧致空间中，每个序列的滤子都有聚点 -/
  apply exists_clusterPt_of_compactSpace

-- 度量空间版本
theorem bolzano_weierstrass_metric {X : Type*} [MetricSpace X] [ProperSpace X]
    (x : ℕ → X) (hbounded : Bornology.IsBounded (Set.range x)) :
    HasConvergentSubseq x := by
  /- 在Proper空间中，有界集的闭包是紧致的 -/
  have h_compact : IsCompact (closure (range x)) := by
    apply IsBounded.isCompact_closure
    exact hbounded
  
  have h_subseq : ∃ (φ : ℕ → ℕ), StrictMono φ ∧ ∃ (L : X), Tendsto (x ∘ φ) atTop (𝓝 L) := by
    apply IsCompact.tendsto_subseq h_compact
    · intro n
      apply subset_closure
      simp
    · use 0
  
  exact h_subseq

/-
## Bolzano-Weierstrass定理的高维推广

**定理**: 在 ℝⁿ 中，任何有界序列都有收敛子序列。

**证明**: 对每个坐标分别应用一维Bolzano-Weierstrass定理，
然后使用对角线方法选取公共的收敛子序列。
-/

-- ℝⁿ中的Bolzano-Weierstrass定理
theorem bolzano_weierstrass_rn {n : ℕ} (x : ℕ → Fin n → ℝ) 
    (hbounded : ∃ (M : ℝ), ∀ (k : ℕ) (i : Fin n), |x k i| ≤ M) :
    HasConvergentSubseq x := by
  /- 使用紧致性证明 -/
  rcases hbounded with ⟨M, hM⟩
  
  /- 序列在紧集 [-M, M]ⁿ 中 -/
  let K : Set (Fin n → ℝ) := {y | ∀ i, y i ∈ Icc (-M) M}
  
  have h_compact : IsCompact K := by
    /- 有限个紧致集的乘积是紧致的 -/
    have : K = Set.pi Set.univ (fun i => Icc (-M) M) := by
      ext y
      simp [K]
    rw [this]
    apply isCompact_univ_pi
    intro i
    exact isCompact_Icc
  
  have h_in_K : ∀ k, x k ∈ K := by
    intro k
    simp [K]
    intro i
    constructor
    · linarith [abs_le.mp (hM k i)]
    · linarith [abs_le.mp (hM k i)]
  
  /- 在紧致集中取收敛子序列 -/
  apply IsCompact.tendsto_subseq h_compact
  · intro k
    exact h_in_K k
  · use 0

-- 使用Mathlib4的紧致性证明
theorem bolzano_weierstrass_compact {X : Type*} [MetricSpace X] [CompactSpace X]
    (x : ℕ → X) :
    HasConvergentSubseq x := by
  /- 紧致度量空间是序列紧致的 -/
  apply IsCompact.tendsto_subseq (isCompact_univ)
  · simp
  · use 0

/-
## 应用：闭区间的紧致性

**定理**: 闭区间 [a, b] ⊂ ℝ 是紧致的。

**证明**: 由Bolzano-Weierstrass定理，[a, b] 中的任何序列都有收敛子序列，
且极限仍在 [a, b] 中（因为 [a, b] 是闭集）。
-/

-- 闭区间的紧致性
theorem compact_Icc {a b : ℝ} (hle : a ≤ b) : IsCompact (Icc a b) := by
  /- 使用Mathlib4的结果 -/
  exact isCompact_Icc

/-
## 应用：连续函数的性质

**定理**: 定义在紧致集上的连续函数必取得最大值和最小值。
-/

-- 极值定理
theorem extreme_value {X : Type*} [MetricSpace X] [CompactSpace X]
    {f : X → ℝ} (hf : Continuous f) :
    ∃ (x₀ : X), ∀ (x : X), f x ≤ f x₀ := by
  /- 证明思路：
     1. 紧致集的连续像是紧致的
     2. ℝ 中的紧致集是有界闭集
     3. 有界闭集包含上确界
  -/
  have h_compact : IsCompact (Set.range f) := by
    apply IsCompact.image isCompact_univ hf
  
  have h_closed : IsClosed (Set.range f) := by
    exact IsCompact.isClosed h_compact
  
  have h_bounded : Bornology.IsBounded (Set.range f) := by
    exact IsCompact.isBounded h_compact
  
  /- 上确界在值域中 -/
  have h_nonempty : (range f).Nonempty := by
    use f (Classical.arbitrary X)
    simp
  
  have h_sup_in : sSup (range f) ∈ range f := by
    apply IsClosed.csSup_mem
    · exact h_closed
    · exact h_nonempty
    · exact h_bounded
  
  rcases h_sup_in with ⟨x₀, hx₀⟩
  use x₀
  intro x
  have : f x ≤ sSup (range f) := by
    apply le_csSup
    · exact h_bounded
    · simp
  rw [← hx₀]
  exact this

end BolzanoWeierstrassTheorem

/-
## 应用示例

### 示例1：构造收敛子序列

```lean
-- 序列 xₙ = (-1)ⁿ 有收敛子序列
example : HasConvergentSubseq (fun n => (-1 : ℝ) ^ n) := by
  /- 取偶数下标子序列：x_{2n} = 1 → 1 -/
  use fun n => 2 * n
  constructor
  · intro m n hmn; simp; linarith
  · use 1
    /- 证明收敛 -/
    simp
    use 1
    simp
```

### 示例2：证明序列紧致性

```lean
-- [0,1] 中的序列都有收敛子序列
example (x : ℕ → ℝ) (hx : ∀ n, x n ∈ Icc 0 1) :
    HasConvergentSubseq x := by
  apply bolzano_weierstrass_1d
  use 1
  intro n
  have : x n ∈ Icc 0 1 := hx n
  rcases this with ⟨h0, h1⟩
  have h_dist : |x n - x 0| ≤ 1 := by
    have h0' : 0 ≤ x n := h0
    have h1' : x n ≤ 1 := h1
    have h0'' : 0 ≤ x 0 := (hx 0).1
    have h1'' : x 0 ≤ 1 := (hx 0).2
    apply abs_le.mpr
    constructor
    · linarith
    · linarith
  exact h_dist
```

## 数学意义

Bolzano-Weierstrass定理的重要性：

1. **完备性的表现**：反映了实数（或ℝⁿ）的完备性
2. **紧致性等价**：在ℝⁿ中，紧致 ⟺ 闭且有界 ⟺ 序列紧致
3. **分析基础**：许多分析定理的基础
4. **存在性证明**：提供了极限存在性的构造性证明

## 与其他定理的关系

| 定理 | 关系 |
|------|------|
| Heine-Borel定理 | 在ℝⁿ中，Bolzano-Weierstrass ⟺ Heine-Borel |
| 单调收敛定理 | 单调有界序列收敛是Bolzano-Weierstrass的特例 |
| 柯西收敛准则 | 完备性 ⟺ 每个柯西序列收敛 |
| 极值定理 | 连续函数在紧致集上取得极值 |

## 历史影响

- **1817**: Bolzano首先证明了有界序列有聚点的引理
- **1860s**: Weierstrass独立发现并推广
- **现代**: 成为实分析和泛函分析的基础工具

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `Mathlib.Topology.MetricSpace.Compact`: 紧致度量空间理论
- `IsCompact.tendsto_subseq`: 紧致空间的序列紧致性
- `exists_clusterPt_of_compactSpace`: 紧致空间中滤子的聚点存在性
- `isCompact_Icc`: 闭区间的紧致性
- `ProperSpace`: proper空间（有界集的闭包紧致）
-/
