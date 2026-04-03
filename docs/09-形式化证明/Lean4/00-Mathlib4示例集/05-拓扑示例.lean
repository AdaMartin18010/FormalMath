import Mathlib.Topology.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.Baire.CompleteMetrizable

/-! 
# 拓扑学示例

对应的FormalMath文档：
- docs/05-拓扑学/01-点集拓扑-深度扩展版.md
- docs/05-拓扑学/01-点集拓扑.md

对应的Mathlib4模块：
- Mathlib.Topology.Basic
- Mathlib.Topology.Compactness.Compact
- Mathlib.Topology.Connected
- Mathlib.Topology.Constructions
- Mathlib.Topology.UrysohnsLemma
- Mathlib.Topology.Baire.CompleteMetrizable

## 核心定义
-/ 

/-! 
## 拓扑空间

拓扑空间是数学中基本的空间概念。
-/

section TopologicalSpace

-- 拓扑空间定义
#check TopologicalSpace

-- 开集
example {X : Type*} [TopologicalSpace X] (U : Set X) : Prop := IsOpen U

-- 闭集
example {X : Type*} [TopologicalSpace X] (F : Set X) : Prop := IsClosed F

-- 拓扑的基本公理
example {X : Type*} [TopologicalSpace X] : IsOpen (Set.univ : Set X) := 
  isOpen_univ

example {X : Type*} [TopologicalSpace X] : IsOpen (∅ : Set X) := 
  isOpen_empty

example {X : Type*} [TopologicalSpace X] {U V : Set X} 
    (hU : IsOpen U) (hV : IsOpen V) : IsOpen (U ∩ V) := 
  IsOpen.inter hU hV

example {X : Type*} [TopologicalSpace X] {ι : Type*} {s : ι → Set X} 
    (hs : ∀ i, IsOpen (s i)) : IsOpen (⋃ i, s i) := 
  isOpen_iUnion hs

-- 离散拓扑
example (X : Type*) : TopologicalSpace X := ⊥

-- 密着拓扑
example (X : Type*) : TopologicalSpace X := ⊤

end TopologicalSpace

/-! 
## 连续映射

拓扑空间之间的连续映射。
-/

section ContinuousMaps

-- 连续映射定义
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] 
    (f : X → Y) : Prop := Continuous f

-- 在一点连续
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] 
    (f : X → Y) (x : X) : Prop := ContinuousAt f x

-- 连续映射的复合
example {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] 
    [TopologicalSpace Z] {f : X → Y} {g : Y → Z} 
    (hf : Continuous f) (hg : Continuous g) : 
    Continuous (g ∘ f) := 
  Continuous.comp hg hf

-- 恒等映射连续
example {X : Type*} [TopologicalSpace X] : Continuous (id : X → X) := 
  continuous_id

-- 常值映射连续
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] 
    (y : Y) : Continuous (fun _ => y : X → Y) := 
  continuous_const

end ContinuousMaps

/-! 
## 紧致性

紧致性是拓扑空间的重要性质。
-/

section Compactness

-- 紧致集定义
example {X : Type*} [TopologicalSpace X] (K : Set X) : Prop := IsCompact K

-- 紧致集的基本性质
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] 
    {f : X → Y} (hf : Continuous f) {K : Set X} (hK : IsCompact K) : 
    IsCompact (f '' K) := 
  hK.image hf

-- 紧致集的闭子集紧致
example {X : Type*} [TopologicalSpace X] {K F : Set X} 
    (hK : IsCompact K) (hF : IsClosed F) (hFK : F ⊆ K) : 
    IsCompact F := 
  IsCompact.of_isClosed_subset hK hF hFK

-- 紧致集的有限交性质
example {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K) 
    {ι : Type*} [Finite ι] {s : ι → Set X} 
    (hs : ∀ i, IsClosed (s i)) (hKsub : K ⊆ ⋂ i, s i) : 
    IsCompact (K ∩ ⋂ i, s i) := by
  simpa using hK

-- Heine-Borel定理：ℝⁿ中的子集紧致当且仅当有界闭
example {K : Set ℝ} : IsCompact K ↔ Bornology.IsBounded K ∧ IsClosed K := by
  rw [isCompact_iff_isClosed_bounded]
  · rfl
  · exact Real.instProperSpace

-- 闭区间紧致
example (a b : ℝ) : IsCompact (Set.Icc a b) := 
  isCompact_Icc

end Compactness

/-! 
## 连通性

连通性和道路连通性。
-/

section Connectedness

-- 连通空间
example {X : Type*} [TopologicalSpace X] : Prop := ConnectedSpace X

-- 连通集
example {X : Type*} [TopologicalSpace X] (S : Set X) : Prop := IsConnected S

-- 道路连通
example {X : Type*} [TopologicalSpace X] : Prop := PathConnectedSpace X

-- 连通空间的连续像是连通的
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] 
    [ConnectedSpace X] {f : X → Y} (hf : Continuous f) (hsurj : Surjective f) : 
    ConnectedSpace Y := 
  connectedSpace_coe_iff.mpr (IsConnected.image isConnected_univ hf hsurj)

-- ℝ是连通的
example : ConnectedSpace ℝ := by
  infer_instance

-- 区间是连通的
example {a b : ℝ} (hab : a ≤ b) : IsConnected (Set.Icc a b) := 
  isConnected_Icc

-- 道路连通蕴含连通
example {X : Type*} [TopologicalSpace X] [PathConnectedSpace X] : 
    ConnectedSpace X := 
  PathConnectedSpace.connectedSpace

end Connectedness

/-! 
## 分离公理

拓扑空间的分离性质。
-/

section SeparationAxioms

-- T0空间（Kolmogorov）
example {X : Type*} [TopologicalSpace X] : Prop := T0Space X

-- T1空间
example {X : Type*} [TopologicalSpace X] : Prop := T1Space X

-- T2空间（Hausdorff）
example {X : Type*} [TopologicalSpace X] : Prop := T2Space X

-- 正规空间
example {X : Type*} [TopologicalSpace X] : Prop := NormalSpace X

-- 度量空间是T2（Hausdorff）
example {X : Type*} [MetricSpace X] : T2Space X := by
  infer_instance

-- Urysohn引理：正规空间中，不相交闭集可用连续函数分离
example {X : Type*} [TopologicalSpace X] [NormalSpace X] {s t : Set X} 
    (hs : IsClosed s) (ht : IsClosed t) (hst : Disjoint s t) :
    ∃ f : X → ℝ, Continuous f ∧ EqOn f 0 s ∧ EqOn f 1 t ∧ 
      ∀ x, f x ∈ Set.Icc 0 1 := by
  apply exists_continuous_zero_one_of_isClosed
  all_goals assumption

end SeparationAxioms

/-! 
## 乘积拓扑

拓扑空间的乘积。
-/

section ProductTopology

-- 乘积拓扑
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] : 
    TopologicalSpace (X × Y) := by
  infer_instance

-- 投影映射连续
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] : 
    Continuous (Prod.fst : X × Y → X) := 
  continuous_fst

example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] : 
    Continuous (Prod.snd : X × Y → Y) := 
  continuous_snd

-- Tychonoff定理：紧致空间的乘积是紧致的
example {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] 
    (h : ∀ i, CompactSpace (X i)) : CompactSpace (∀ i, X i) := by
  infer_instance

end ProductTopology

/-! 
## Baire纲定理

Baire空间的重要性质。
-/

section BaireCategory

-- Baire空间
example {X : Type*} [TopologicalSpace X] : Prop := BaireSpace X

-- 完备度量空间是Baire空间
example {X : Type*} [MetricSpace X] [CompleteSpace X] : BaireSpace X := by
  infer_instance

-- Baire纲定理：可数个稠密开集的交仍然稠密
example {X : Type*} [TopologicalSpace X] [BaireSpace X] {ι : Type*} 
    [Countable ι] {s : ι → Set X} (hs : ∀ i, IsOpen (s i)) 
    (hd : ∀ i, Dense (s i)) : Dense (⋂ i, s i) := 
  BaireSpace.baire_property s hs hd

end BaireCategory

/-! 
## 度量空间

度量空间是特殊的拓扑空间。
-/

section MetricSpaces

-- 度量空间定义
example {X : Type*} : Type _ := MetricSpace X

-- 开球
example {X : Type*} [MetricSpace X] (x : X) (r : ℝ) : Set X := 
  Metric.ball x r

-- 闭球
example {X : Type*} [MetricSpace X] (x : X) (r : ℝ) : Set X := 
  Metric.closedBall x r

-- 度量空间中的连续性
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} 
    {x : X} : 
    ContinuousAt f x ↔ ∀ ε > 0, ∃ δ > 0, ∀ y, dist y x < δ → 
      dist (f y) (f x) < ε := 
  Metric.continuousAt_iff

-- ℝ是度量空间
example : MetricSpace ℝ := by
  infer_instance

end MetricSpaces

/-! 
## 示例：实数线上的拓扑

实数线是最直观的拓扑空间例子。
-/

section RealLineTopology

-- 开区间是开集
example {a b : ℝ} : IsOpen (Set.Ioo a b) := 
  isOpen_Ioo

-- 闭区间是闭集
example {a b : ℝ} : IsClosed (Set.Icc a b) := 
  isClosed_Icc

-- ℝ中紧致集 = 有界闭集（Heine-Borel）
example {K : Set ℝ} : IsCompact K ↔ Bornology.IsBounded K ∧ IsClosed K := 
  isCompact_iff_isClosed_bounded

-- Bolzano-Weierstrass性质
example (K : Set ℝ) (hK : IsCompact K) (s : ℕ → ℝ) 
    (hs : ∀ n, s n ∈ K) : 
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x ∈ K, Tendsto (s ∘ φ) atTop (𝓝 x) := by
  apply IsCompact.tendsto_subseq hK hs

end RealLineTopology

/-! 
## 练习

1. 证明：离散拓扑空间中，每个子集都是开集。

2. 证明：如果f: X → Y是连续映射，且X是连通的，那么f(X)也是连通的。

3. 证明：有限个紧致集的并集是紧致的。

4. 证明：紧致Hausdorff空间是正规的。

5. 证明：闭区间[0,1]不能表示为两个不相交非空闭集的并。

-/ 

section Exercises
variable {X : Type*} [TopologicalSpace X]

-- 练习1的提示：离散拓扑中所有集合都是开集
example (S : Set X) [DiscreteTopology X] : IsOpen S := by
  apply isOpen_discrete

-- 练习3的提示
example {s t : Set X} (hs : IsCompact s) (ht : IsCompact t) : 
    IsCompact (s ∪ t) := by
  apply hs.union ht

end Exercises
