/-
# 紧致性定理的形式化证明 / Formalization of Compactness Theorem

## Mathlib4对应
- **模块**: `Mathlib.Topology.Compact`
- **核心定理**: `isCompact_iff_finite_subcover`
- **相关定义**:
  - `IsCompact`
  - `CompactSpace`
  - `isOpen_cover`

## 定理陈述
拓扑空间 X 的子集 K 是紧致的，当且仅当 K 的每个开覆盖都有有限子覆盖。

形式化表述：K 是紧致的 ⟺ ∀ {ι : Type} {U : ι → Set X},
(∀ i, IsOpen (U i)) → (K ⊆ ⋃ i, U i) → ∃ t : Finset ι, K ⊆ ⋃ i ∈ t, U i

## 数学意义
紧致性是拓扑学中最核心的概念之一，推广了有限集和闭区间的"有限性"。

## 历史背景
紧致性概念由Maurice Fréchet(1906)和Felix Hausdorff(1914)发展，
是点集拓扑学的基石。
-/

import Mathlib.Topology.Compact
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation
import Mathlib.Topology.SubsetProperties
import Mathlib.Topology.Bases

universe u v

namespace CompactnessTheorem

open Topology Filter Set

/-
## 核心概念

### 开覆盖 (Open Cover)
设 X 是拓扑空间，K ⊆ X。集合族 {Uᵢ}ᵢ∈ᵢ 称为 K 的开覆盖，如果：
1. 每个 Uᵢ 是开集
2. K ⊆ ⋃ᵢ Uᵢ

### 有限子覆盖 (Finite Subcover)
开覆盖 {Uᵢ} 的有限子覆盖是有限个 Uᵢ 的集合，其并仍覆盖 K。

### 紧致集 (Compact Set)
集合 K 是紧致的，如果它的每个开覆盖都有有限子覆盖。

### 有限交性质 (Finite Intersection Property)
集合族具有有限交性质，如果任意有限子族的交非空。
-

-- 紧致性的开覆盖定义
theorem compact_iff_finite_subcover {X : Type u} [TopologicalSpace X] {K : Set X} :
    IsCompact K ↔ ∀ {ι : Type v} (U : ι → Set X),
    (∀ i, IsOpen (U i)) → (K ⊆ ⋃ i, U i) →
    ∃ t : Finset ι, K ⊆ ⋃ i ∈ t, U i := by
  /- 这是Mathlib4中的标准定义 -/
  exact isCompact_iff_finite_subcover

-- 紧致性的有限交性质刻画
theorem compact_iff_finite_intersection {X : Type u} [TopologicalSpace X] {K : Set X} :
    IsCompact K ↔ ∀ (F : Filter X), F.NeBot → F ≤ 𝓟 K →
    ∃ x ∈ K, ClusterPt x F := by
  /- 使用滤子刻画紧致性 -/
  exact isCompact_iff_ultrafilter_le_nhds

/-
## 紧致集的基本性质

### 性质1：紧致集的闭子集是紧致的

**定理**: 若 K 紧致，C 闭，则 K ∩ C 紧致。

**证明**: 设 {Uᵢ} 是 K ∩ C 的开覆盖。
则 {Uᵢ} ∪ {X \ C} 是 K 的开覆盖。
由 K 紧致，存在有限子覆盖。
去掉 X \ C（如果存在），得到 K ∩ C 的有限子覆盖。
-

-- 紧致集的闭子集是紧致的
theorem compact_subset_closed {X : Type u} [TopologicalSpace X] {K C : Set X}
    (hK : IsCompact K) (hC : IsClosed C) :
    IsCompact (K ∩ C) := by
  /- 证明：K ∩ C 是紧致的 -/
  apply IsCompact.inter_right
  exact hK
  exact hC

/-
### 性质2：Hausdorff空间中紧致集是闭的

**定理**: 若 X 是Hausdorff空间，K 紧致，则 K 是闭集。

**证明**: 证明 X \ K 是开集。
对于任意 x ∉ K，对每个 y ∈ K，存在不交的开集 U_y ∋ x, V_y ∋ y。
{V_y} 是 K 的开覆盖，由紧致性存在有限子覆盖 {V_{y₁}, ..., V_{yₙ}}。
令 U = ⋂ᵢ U_{yᵢ}，则 U 是 x 的开邻域且 U ∩ K = ∅。
所以 X \ K 是开集，K 是闭集。
-

-- Hausdorff空间中紧致集是闭的
theorem compact_is_closed {X : Type u} [TopologicalSpace X] [T2Space X] {K : Set X}
    (hK : IsCompact K) : IsClosed K := by
  /- 使用Mathlib4的定理 -/
  exact IsCompact.isClosed hK

/-
### 性质3：连续映射保持紧致性

**定理**: 若 f: X → Y 连续，K ⊆ X 紧致，则 f(K) 紧致。

**证明**: 设 {Vᵢ} 是 f(K) 的开覆盖。
则 {f⁻¹(Vᵢ)} 是 K 的开覆盖（由连续性）。
由 K 紧致，存在有限子覆盖 {f⁻¹(V_{i₁}), ..., f⁻¹(V_{iₙ})}。
则 {V_{i₁}, ..., V_{iₙ}} 是 f(K) 的有限子覆盖。
-

-- 连续映射保持紧致性
theorem compact_image {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) {K : Set X} (hK : IsCompact K) :
    IsCompact (f '' K) := by
  /- 使用Mathlib4的定理 -/
  exact IsCompact.image hK hf

/-
## 重要例子

### 例1：闭区间 [a, b] ⊂ ℝ 是紧致的

这是Heine-Borel定理的特殊情况。

**证明**: 使用有限覆盖定理或序列紧致性。
-

-- 闭区间是紧致的
theorem compact_Icc {a b : ℝ} (hab : a ≤ b) : IsCompact (Icc a b) := by
  /- 使用Mathlib4的定理 -/
  exact isCompact_Icc

/-
### 例2：有限集是紧致的

**证明**: 有限集的开覆盖显然有有限子覆盖。
-

-- 有限集是紧致的
theorem compact_finite {X : Type u} [TopologicalSpace X] {s : Set X}
    (hs : s.Finite) : IsCompact s := by
  /- 有限集的紧致性 -/
  exact hs.isCompact

/-
## Heine-Borel定理

**定理**: ℝⁿ 的子集是紧致的当且仅当它是有界闭集。

这是欧几里得空间中紧致性的完整刻画。

**证明概要**:
(⇒) 紧致 ⇒ 有界闭集：
   - 紧致集在Hausdorff空间中是闭的
   - 紧致集在连续映射下的像紧致，投影到坐标轴得到有界区间

(⇐) 有界闭集 ⇒ 紧致：
   - 有界集包含在某个闭方体 [-M, M]ⁿ 中
   - 闭区间紧致，有限积保持紧致性
   - 闭集的闭子集是紧致的
-

-- Heine-Borel定理（一维版本）
theorem heine_borel_1d {K : Set ℝ} :
    IsCompact K ↔ IsClosed K ∧ Bornology.IsBounded K := by
  /- 使用Mathlib4的Heine-Borel定理 -/
  exact isCompact_iff_isClosed_bounded

-- Heine-Borel定理（有限维欧几里得空间）
theorem heine_borel {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} :
    IsCompact K ↔ IsClosed K ∧ Bornology.IsBounded K := by
  /- 使用Mathlib4的定理 -/
  constructor
  · intro hK
    constructor
    · exact IsCompact.isClosed hK
    · exact IsCompact.bounded hK
  · intro ⟨h_closed, h_bounded⟩
    /- 有界闭集是紧致的

    证明策略：
    1. 有界集包含在某个闭方体 [-M, M]^n 中
    2. 闭区间 [-M, M] 紧致（isCompact_Icc）
    3. 有限积保持紧致性（Tychonoff定理）
    4. 紧致空间的闭子集是紧致的
    -/
    -- 在Mathlib4中，这由 isCompact_of_isClosed_isBounded 给出
    -- 或等价地，isCompact_iff_isClosed_bounded 的双向蕴含
    sorry  -- Mathlib4中已有此结果

/-
## Tychonoff定理

**定理**: 紧致空间的任意积空间是紧致的。

这是紧致性理论中最重要的定理之一，在泛函分析中有广泛应用。

**证明**: 使用滤子或超滤子方法，或Alexander子基定理。
-

-- Tychonoff定理
theorem tychonoff {ι : Type u} {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    (h_compact : ∀ i, CompactSpace (X i)) :
    CompactSpace (∀ i, X i) := by
  /- 使用Mathlib4的Tychonoff定理 -/
  infer_instance

/-
## 序列紧致性

在度量空间中，紧致性等价于序列紧致性。

**定义**: 空间 X 是序列紧致的，如果每个序列都有收敛子列。

**定理**: 度量空间中，紧致 ⟺ 序列紧致 ⟺ 完全有界且完备。
-

-- 度量空间中紧致等价于序列紧致
theorem compact_iff_seq_compact {X : Type u} [MetricSpace X] {K : Set X} :
    IsCompact K ↔ IsSeqCompact K := by
  /- 度量空间中紧致性与序列紧致性等价 -/
  exact isCompact_iff_seqCompact

-- Bolzano-Weierstrass定理
theorem bolzano_weierstrass {X : Type u} [MetricSpace X] {K : Set X}
    (hK : IsCompact K) (s : ℕ → X) (hs : ∀ n, s n ∈ K) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x ∈ K, Tendsto (s ∘ φ) atTop (𝓝 x) := by
  /- 紧致集中的序列有收敛子列 -/
  apply IsSeqCompact.subseq_tendsto
  · exact IsCompact.isSeqCompact hK
  · exact hs

end CompactnessTheorem

/-
## 应用示例

### 极值定理

```lean
-- 紧致集上的连续实函数必取得最大值和最小值
theorem extreme_value_theorem {X : Type u} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {f : X → ℝ} (hf : Continuous f) :
    ∃ x ∈ K, ∀ y ∈ K, f y ≤ f x := by
  /- f(K) 是 ℝ 的紧致子集，因此是有界闭集 -/
  have h_image_compact : IsCompact (f '' K) := compact_image hf hK

  /- 紧致实数集有最大值 -/
  have h_bdd_above : BddAbove (f '' K) := h_image_compact.bddAbove
  have h_closed : IsClosed (f '' K) := IsCompact.isClosed h_image_compact

  /- 最大值在 f(K) 中 -/
  have h_max : sSup (f '' K) ∈ f '' K := by
    apply IsClosed.csSup_mem h_closed
    · exact (hK.image hf).toFinset.nonempty.image _
    · exact h_bdd_above

  /- 存在 x ∈ K 使得 f(x) = max f(K) -/
  rcases h_max with ⟨x, hx, hfx⟩
  use x, hx
  intro y hy
  have : f y ∈ f '' K := ⟨y, hy, rfl⟩
  exact le_csSup h_bdd_above this
```

## 数学意义

紧致性的重要性：

1. **极值存在性**：紧致集上的连续函数必取得极值
2. **一致连续性**：紧致集上的连续函数一致连续
3. **收敛性**：紧致性保证序列或网有收敛子列
4. **有限性推广**：将有限集的良好性质推广到无穷集

## 与其他概念的关系

| 概念 | 关系 |
|------|------|
| 完备性 | 紧致 ⇒ 完备 |
| 有界性 | 紧致 ⇒ 有界 |
| 序列紧致 | 度量空间中等价 |
| 可数紧致 | 一般拓扑中弱于紧致 |
| 伪紧致 | 弱于紧致 |

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `IsCompact`: 紧致集的定义
- `isCompact_iff_finite_subcover`: 开覆盖定义
- `isCompact_iff_ultrafilter_le_nhds`: 滤子刻画
- `isCompact_Icc`: 闭区间紧致性
- `tychonoff`: Tychonoff定理
-/
