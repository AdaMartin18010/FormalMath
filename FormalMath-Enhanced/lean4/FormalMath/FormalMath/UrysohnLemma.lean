/-
# 乌雷松引理 (Urysohn's Lemma)

## 数学背景

乌雷松引理是正规空间理论的核心定理，它表明：
在正规拓扑空间中，任意两个不相交闭集可以被连续函数分离。

这是拓扑学中最重要、最美丽的定理之一，
深刻揭示了正规空间的分析性质。

## 定理陈述

设 X 是正规拓扑空间，A 和 B 是 X 中不相交的闭集。
则存在连续函数 f : X → [0,1] 使得：
- f(A) = {0}（在A上恒为0）
- f(B) = {1}（在B上恒为1）

形式地：
∀ A, B ⊆ X 闭, A ∩ B = ∅ → ∃ f ∈ C(X, [0,1]), f(A) = 0 ∧ f(B) = 1

## 历史背景

- 1925年：Pavel Urysohn (乌雷松) 首次证明
- Urysohn在26岁时不幸溺水身亡，这是他最重要的贡献之一
- 该引理是Urysohn度量化定理的基础

## 证明方法

经典证明利用二进有理数构造连续函数：
1. 利用正规性，构造一族开集 {U_r}，其中 r ∈ D ∩ [0,1]，D是二进有理数
2. 定义 f(x) = inf { r | x ∈ U_r }
3. 验证f是连续的且具有所需性质

## 应用

1. **Tietze扩张定理**：闭子集上的连续函数可扩张到全空间
2. **Urysohn度量化定理**：第二可数正规空间可度量化
3. **Riesz表示定理**：局部紧Hausdorff空间上的正线性泛函表示
4. **函数逼近理论**：连续函数的分段常数逼近

## 参考
- Urysohn, "Über die Mächtigkeit der zusammenhängenden Mengen" (1925)
- Munkres, "Topology"
- Kelley, "General Topology"
- 熊金城,《点集拓扑讲义》

## Mathlib4对应
- `Mathlib.Topology.UrysohnsLemma`
- `Mathlib.Topology.Separation`
- `Mathlib.Topology.Compactness`
-/

import Mathlib.Topology.Separation
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Real.Basic
import Mathlib.Order.Dense

namespace UrysohnLemma

open Topology Filter Set Classical

universe u

/-
## 基本概念

### 正规空间

拓扑空间X称为正规的，如果：
1. X是T₁空间（单点集是闭的）
2. 任意两个不相交闭集有不相交的邻域

即：∀ A, B ⊆ X 闭, A ∩ B = ∅ → ∃ U, V 开, A ⊆ U, B ⊆ V, U ∩ V = ∅
-/

/-- 正规空间的定义 -/
class NormalSpace (X : Type u) [TopologicalSpace X] : Prop where
  t1 : T1Space X
  normal : ∀ (A B : Set X), IsClosed A → IsClosed B → A ∩ B = ∅ →
    ∃ U V, IsOpen U ∧ IsOpen V ∧ A ⊆ U ∧ B ⊆ V ∧ U ∩ V = ∅

/-
## 乌雷松引理的陈述与证明

### 定理陈述
-/

variable {X : Type u} [TopologicalSpace X] [NormalSpace X]

/-- 乌雷松引理

正规空间中任意两个不相交闭集可以被连续函数分离。
-/
theorem urysohn_lemma {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (h_disjoint : A ∩ B = ∅) :
    ∃ f : X → ℝ, Continuous f ∧ Set.EqOn f (fun _ ↦ 0) A ∧ Set.EqOn f (fun _ ↦ 1) B ∧
      ∀ x, f x ∈ Set.Icc 0 1 := by
  -- 证明思路：
  -- 1. 构造二进有理数上的开集族 {U_r}
  -- 2. 定义 f(x) = inf { r | x ∈ U_r }
  -- 3. 验证f的连续性和边界条件

  -- 第一步：构造二进有理数集
  let D : Set ℚ := {r | ∃ (n : ℕ) (m : ℤ), r = m / 2^n}
  have hD_dense : Dense D := sorry -- 二进有理数在实数中稠密

  -- 第二步：利用正规性构造开集族
  -- 通过超限归纳法构造U_r，使得 r < s 蕴含 closure(U_r) ⊆ U_s
  let U : D → Set X := fun r ↦ sorry -- 需要递归构造

  -- 构造的关键性质：
  -- - A ⊆ U_0
  -- - U_1 ⊆ X \ B
  -- - r < s 蕴含 closure(U_r) ⊆ U_s

  -- 第三步：定义函数 f(x) = inf { r | x ∈ U_r }
  let f : X → ℝ := fun x ↦ sInf {r : D | x ∈ U r}

  -- 第四步：验证f的值域在[0,1]中
  have h_range (x : X) : f x ∈ Set.Icc 0 1 := by
    sorry

  -- 第五步：验证f在A上为0，在B上为1
  have h_f_A : Set.EqOn f (fun _ ↦ 0) A := by
    sorry -- A ⊆ U_0 且 U_0 是开集

  have h_f_B : Set.EqOn f (fun _ ↦ 1) B := by
    sorry -- B ∩ U_r = ∅ 对所有 r < 1

  -- 第六步：验证f连续
  have h_continuous : Continuous f := by
    -- 利用开集的逆像刻画连续性
    -- 对于 (a, ∞) 和 (-∞, b) 类型的开集
    sorry

  exact ⟨f, h_continuous, h_f_A, h_f_B, h_range⟩

/-
### 详细证明构造

构造的关键在于递归地定义开集族 {U_r}。

**递归步骤**：
- 基础：U_1 = X \ B
- 归纳：给定 U_s 对所有 s > r，利用正规性构造 U_r

使得对于任意 r < s，有 closure(U_r) ⊆ U_s。
-/

/-- 乌雷松开集族的构造 -/
def UrysohnOpenSets {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (h_disjoint : A ∩ B = ∅) : Set ℚ → Set X :=
  -- 利用超限递归构造
  fun r ↦ if r < 0 then ∅
          else if r > 1 then Set.univ
          else sorry -- 递归构造 [0,1] 内的开集

/-
## Tietze扩张定理

乌雷松引理的重要推论，关于连续函数的扩张。

**定理陈述**：
设 X 是正规空间，A ⊆ X 是闭子集，f : A → ℝ 是连续函数。
则存在连续扩张 F : X → ℝ 使得 F|_A = f。

如果 f(A) ⊆ [a,b]，则可要求 F(X) ⊆ [a,b]。
-/

/-- Tietze扩张定理 -/
theorem tietze_extension {A : Set X} (hA : IsClosed A) {f : A → ℝ}
    (hf : Continuous f) (h_bdd : ∃ a b, ∀ x, f x ∈ Set.Icc a b) :
    ∃ F : X → ℝ, Continuous F ∧ Set.EqOn F f A := by
  -- 证明思路：
  -- 1. 标准化到 f(A) ⊆ [-1,1]
  -- 2. 递归构造一列连续函数 g_n，在A上逼近f
  -- 3. 令 F = Σ g_n

  -- 第一步：标准化
  wlog h01 : ∀ x, f x ∈ Set.Icc (-1) 1
  · -- 对一般情况做线性变换
    sorry

  -- 第二步：递归构造函数列
  -- 对于每个n，构造g_n使得：
  -- - |g_n(x)| ≤ (2/3)^n / 3
  -- - |f(x) - Σ_{k=0}^{n-1} g_k(x)| ≤ (2/3)^n 对 x ∈ A

  let g : ℕ → (X → ℝ) := fun n ↦ sorry -- 递归构造

  -- 第三步：定义 F = Σ g_n
  let F : X → ℝ := fun x ↦ ∑' n : ℕ, g n x

  -- 第四步：验证F收敛且连续
  have h_F_conv : ∀ x, Summable (fun n ↦ g n x) := by
    sorry -- 几何级数收敛

  have h_F_continuous : Continuous F := by
    sorry -- 一致收敛保持连续性

  -- 第五步：验证 F|_A = f
  have h_F_extends : Set.EqOn F f A := by
    sorry -- 在A上，级数收敛到f

  exact ⟨F, h_F_continuous, h_F_extends⟩

/-
## Urysohn度量化定理

**定理陈述**：
第二可数正规空间是可度量化的。

这是拓扑学中最重要的度量化定理之一。
-/

/-- Urysohn度量化定理 -/
theorem urysohn_metrization [SecondCountableTopology X] :
    ∃ m : MetricSpace X, m.toTopologicalSpace = ‹TopologicalSpace X› := by
  -- 证明思路：
  -- 1. 利用第二可数性，得到可数基 {B_n}
  -- 2. 对每个 (B_m, B_n) 满足 closure(B_m) ⊆ B_n，
  --    利用乌雷松引理构造 f_{m,n} : X → [0,1]
  -- 3. 将这些函数对角嵌入到 Hilbert立方体 [0,1]^ℕ
  -- 4. 验证这是嵌入映射

  -- 第一步：获得可数基
  obtain ⟨b, hcountable, hbasis⟩ := TopologicalSpace.exists_countable_basis X

  -- 第二步：构造分离函数族
  let P := {p : ℕ × ℕ | closure (b p.1) ⊆ b p.2}
  have hP_countable : Countable P := by
    infer_instance

  -- 对每个 p ∈ P，构造 f_p : X → [0,1]
  let f : P → (X → ℝ) := fun p ↦
    Classical.choose (urysohn_lemma (isClosed_closure) (hbasis.isOpen _) sorry)

  -- 第三步：嵌入到Hilbert立方体
  let F : X → (P → ℝ) := fun x p ↦ f p x

  -- 第四步：验证F是嵌入
  have h_embedding : IsEmbedding F := by
    sorry -- 需要验证F是单射且是拓扑嵌入

  -- 第五步：拉回度量
  let d (x y : X) := ∑' p : P, |F x p - F y p| / 2 ^ (Encodable.encode p)

  have h_metric : MetricSpace X := by
    sorry -- 验证d是度量

  exact ⟨h_metric, sorry⟩ -- 验证度量诱导原拓扑

/-
## 连续函数空间

乌雷松引理揭示了正规空间上连续函数空间的丰富性。
-/

/-- 有界连续函数空间 -/
def BoundedContinuousFunctions (X : Type*) [TopologicalSpace X] : Type _ :=
  {f : X → ℝ | Continuous f ∧ ∃ M, ∀ x, |f x| ≤ M}

instance : MetricSpace (BoundedContinuousFunctions X) :=
  -- 上确界范数
  ⟨fun f g ↦ sSup { |f.1 x - g.1 x| | x : X }, sorry, sorry, sorry, sorry⟩

/-
### Stone-Weierstrass定理

连续函数代数在紧空间上的稠密性。

这是乌雷松引理思想的延伸。
-/

variable [CompactSpace X]

/-- 函数代数 -/
structure FunctionAlgebra where
  carrier : Set (X → ℝ)
  mul_mem' : ∀ f g ∈ carrier, f * g ∈ carrier
  add_mem' : ∀ f g ∈ carrier, f + g ∈ carrier
  smul_mem' : ∀ c : ℝ, ∀ f ∈ carrier, c • f ∈ carrier
  const_mem' : ∀ c : ℝ, (fun _ ↦ c) ∈ carrier

/-- 分离点 -/
def SeparatesPoints (A : FunctionAlgebra X) : Prop :=
  ∀ x y : X, x ≠ y → ∃ f ∈ A.carrier, f x ≠ f y

/-- Stone-Weierstrass定理 -/
theorem stone_weierstrass (A : FunctionAlgebra X) (h_separates : SeparatesPoints A) :
    Dense A.carrier := by
  -- 证明思路：
  -- 1. 利用乌雷松引理思想构造函数逼近
  -- 2. 证明分离点的代数可以逼近指示函数
  -- 3. 线性组合逼近任意连续函数
  sorry

/-
## 层论中的乌雷松引理

在层论中，乌雷松引理有自然的推广。
-/

/-- 单位分解的存在性 -/
theorem partition_of_unity {ι : Type*} [Fintype ι] {U : ι → Set X}
    (hU : (⋃ i, U i) = Set.univ) (hU_open : ∀ i, IsOpen (U i))
    (h_normal : ∀ i, NormalSpace {x // x ∈ closure (U i)}) :
    ∃ ρ : ι → (X → ℝ),
      (∀ i, Continuous (ρ i)) ∧
      (∀ i x, ρ i x ∈ Set.Icc 0 1) ∧
      (∀ i x, x ∉ U i → ρ i x = 0) ∧
      (∀ x, ∑ i, ρ i x = 1) := by
  -- 利用乌雷松引理构造函数 ρ_i
  -- 使得 ρ_i 在 U_i 上为正，在补集上为零
  -- 然后归一化
  sorry

/-
## 应用：Riesz表示定理的准备

乌雷松引理是证明Riesz表示定理的关键工具。

在局部紧Hausdorff空间上，乌雷松引理保证了足够多的连续函数存在。
-/

variable [LocallyCompactSpace X]

/-- 具有紧支集的连续函数 -/
def ContinuousMapWithCompactSupport : Type _ :=
  {f : X → ℝ | Continuous f ∧ IsCompact (closure {x | f x ≠ 0})}

notation "C_c(" X ", " R ")" => ContinuousMapWithCompactSupport X

/-- 乌雷松型函数的存在性 -/
theorem exists_urysohn_type {K U : Set X} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ f ∈ C_c(X, ℝ), Set.EqOn f (fun _ ↦ 1) K ∧ ∀ x ∉ U, f x = 0 := by
  -- 利用局部紧性和乌雷松引理
  -- 构造紧支集连续函数
  sorry

/-
## 总结

乌雷松引理是点集拓扑学的核心定理，它揭示了正规空间的深刻分析性质。

主要结论：
1. 正规空间中不相交闭集可被连续函数分离
2. 蕴含Tietze扩张定理
3. 蕴含Urysohn度量化定理
4. 是Riesz表示定理的关键工具

证明要点：
- 利用二进有理数的稠密性
- 递归构造开集族
- 利用inf定义连续函数
- 关键性质：closure(U_r) ⊆ U_s 当 r < s
-/

end UrysohnLemma
