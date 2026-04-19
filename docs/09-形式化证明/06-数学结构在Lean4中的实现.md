---
title: "数学结构在Lean4中的实现"
msc_primary: "03"
---

# 数学结构在 Lean4 中的实现

本文档详细介绍如何在 Lean4 中实现主要的数学结构，包括代数结构、拓扑结构和几何结构。

---

## 目录

1. [代数结构](#代数结构)
2. [拓扑结构](#拓扑结构)
3. [度量结构](#度量结构)
4. [流形结构](#流形结构)
5. [实例详解](#实例详解)

---

## 代数结构

### 群 (Group)

群是代数学中最基本的结构之一，由一个集合配备一个满足特定公理的二元运算组成。

```lean4
import Mathlib

-- 群的定义（来自 Mathlib）
class Group (G : Type u) extends DivInvMonoid G where
  inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1

-- 群的基本性质
theorem Group.mul_inv_cancel {G : Type u} [Group G] (a : G) : a * a⁻¹ = 1 := by
  have h : (a * a⁻¹)⁻¹ * (a * a⁻¹) = 1 := by
    apply inv_mul_cancel
  have h2 : (a * a⁻¹)⁻¹ = a * a⁻¹ := by
    -- 证明 (a * a⁻¹)⁻¹ = a * a⁻¹
    sorry
  sorry

-- 群的例子：整数加法群
instance Int.addGroup : AddGroup Int where
  add_assoc := Int.add_assoc
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  neg_add_cancel := Int.add_left_neg

-- 群的例子：置换群
def Perm (α : Type) : Type := α ≃ α

instance Perm.group {α : Type} : Group (Perm α) where
  mul f g := g.trans f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc f g h := by
    ext
    simp [mul]
  one_mul f := by
    ext
    simp [mul, one]
  mul_one f := by
    ext
    simp [mul, one]
  inv_mul_cancel f := by
    ext
    simp [mul, inv]
```

**群的公理**：

1. 封闭性：∀ a b ∈ G, a * b ∈ G
2. 结合律：∀ a b c ∈ G, (a *b)* c = a *(b* c)
3. 单位元：∃ e ∈ G, ∀ a ∈ G, e *a = a* e = a
4. 逆元：∀ a ∈ G, ∃ a⁻¹ ∈ G, a⁻¹ *a = a* a⁻¹ = e

### 环 (Ring)

环是配备两种运算（加法和乘法）的代数结构。

```lean4
import Mathlib

-- 环的定义（来自 Mathlib）
class Ring (R : Type u) extends Monoid R, AddCommGroup R where
  zero_mul : ∀ a : R, 0 * a = 0
  mul_zero : ∀ a : R, a * 0 = 0
  mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c
  add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c

-- 环的例子：整数环
#check (Int.instRing : Ring Int)

-- 在环中证明性质
theorem Ring.mul_neg {R : Type u} [Ring R] (a b : R) : a * (-b) = -(a * b) := by
  have h : a * (-b) + a * b = 0 := by
    rw [←mul_add]
    simp
  have h2 : -(a * b) + a * b = 0 := by
    apply neg_add_cancel
  have h3 : a * (-b) = -(a * b) := by
    rw [←h2] at h
    apply add_right_cancel h
  exact h3
```

**环的公理**：

1. (R, +) 是阿贝尔群
2. (R, *) 是半群（结合律）
3. 分配律：乘法对加法满足分配律

### 域 (Field)

域是乘法可交换且每个非零元都有逆元的环。

```lean4
import Mathlib

-- 域的定义（来自 Mathlib）
class Field (K : Type u) extends Ring K, DivInvMonoid K where
  mul_comm : ∀ a b : K, a * b = b * a
  mul_inv_cancel : ∀ a : K, a ≠ 0 → a * a⁻¹ = 1
  inv_zero : (0 : K)⁻¹ = 0

-- 域的例子：有理数域
#check (Rat.instField : Field Rat)

-- 域的例子：实数域
#check (Real.instFieldReal : Field Real)

-- 复数域
def Complex : Type := Real × Real

namespace Complex

def add (z w : Complex) : Complex := (z.1 + w.1, z.2 + w.2)
def mul (z w : Complex) : Complex :=
  (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)
def neg (z : Complex) : Complex := (-z.1, -z.2)
def inv (z : Complex) (hz : z ≠ (0, 0)) : Complex :=
  let denom := z.1^2 + z.2^2
  (z.1 / denom, -z.2 / denom)

instance : Field Complex where
  add := add
  mul := mul
  neg := neg
  zero := (0, 0)
  one := (1, 0)
  inv z := if hz : z = (0, 0) then (0, 0) else inv z hz
  -- 需要证明所有域公理
  -- ...
  sorry

end Complex
```

### 模 (Module) 与向量空间 (Vector Space)

模是环上的向量空间推广。

```lean4
import Mathlib

-- 模的定义（来自 Mathlib）
class Module (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M]
    extends DistribMulAction R M where
  add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x
  zero_smul : ∀ x : M, (0 : R) • x = 0

-- 向量空间是域上的模
abbrev VectorSpace (K : Type u) (V : Type v) [Field K] [AddCommGroup V] :=
  Module K V

-- 向量空间的例子：R^n
def RealVectorSpace (n : Nat) := Fin n → Real

instance {n : Nat} : VectorSpace Real (RealVectorSpace n) where
  smul c v := fun i => c * v i
  one_smul v := by
    funext i
    simp
  mul_smul c d v := by
    funext i
    simp [mul_assoc]
  smul_zero c := by
    funext i
    simp
  smul_add c v w := by
    funext i
    simp [mul_add]
  add_smul c d v := by
    funext i
    simp [add_mul]
  zero_smul v := by
    funext i
    simp
```

**向量空间的公理**：

1. (V, +) 是阿贝尔群
2. 数乘满足：1·v = v, a·(b·v) = (ab)·v
3. 分配律：a·(v+w) = a·v + a·w, (a+b)·v = a·v + b·v

### 子群与子环

```lean4
import Mathlib

-- 子群的定义
structure Subgroup (G : Type u) [Group G] where
  carrier : Set G
  one_mem' : 1 ∈ carrier
  mul_mem' {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  inv_mem' {a} : a ∈ carrier → a⁻¹ ∈ carrier

-- 子群是群
instance Subgroup.toGroup {G : Type u} [Group G] (H : Subgroup G) : Group H.carrier :=
  sorry

-- 子环的定义
structure Subring (R : Type u) [Ring R] where
  carrier : Set R
  add_mem' {a b} : a ∈ carrier → b ∈ carrier → a + b ∈ carrier
  zero_mem' : 0 ∈ carrier
  neg_mem' {a} : a ∈ carrier → -a ∈ carrier
  mul_mem' {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  one_mem' : 1 ∈ carrier
```

---

## 拓扑结构

### 拓扑空间 (Topological Space)

```lean4
import Mathlib

-- 拓扑空间的定义
class TopologicalSpace (X : Type u) where
  IsOpen : Set X → Prop
  isOpen_univ : IsOpen Set.univ
  isOpen_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
  isOpen_sUnion : ∀ s, (∀ t ∈ s, IsOpen t) → IsOpen (⋃₀ s)

-- 开集的性质
theorem TopologicalSpace.isOpen_union {X : Type u} [TopologicalSpace X]
    {s t : Set X} (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∪ t) := by
  have : s ∪ t = ⋃₀ {s, t} := by
    simp
  rw [this]
  apply isOpen_sUnion
  intro u hu
  simp at hu
  rcases hu with rfl | rfl
  · exact hs
  · exact ht

-- 拓扑空间的例子：离散拓扑
instance discreteTopology (X : Type u) : TopologicalSpace X where
  IsOpen _ := True
  isOpen_univ := trivial
  isOpen_inter _ _ _ _ := trivial
  isOpen_sUnion _ _ := trivial

-- 拓扑空间的例子：密着拓扑（平凡拓扑）
instance indiscreteTopology (X : Type u) : TopologicalSpace X where
  IsOpen s := s = Set.univ ∨ s = ∅
  isOpen_univ := Or.inl rfl
  isOpen_inter s t hs ht := by
    rcases hs with hs | hs <;> rcases ht with ht | ht <;> simp [hs, ht]
    <;> simp
  isOpen_sUnion s h := by
    by_cases huniv : Set.univ ∈ s
    · left
      rw [Set.sUnion_eq_univ_iff]
      intro x
      exact ⟨Set.univ, huniv, by simp⟩
    · right
      rw [Set.sUnion_eq_empty]
      intro t ht
      have := h t ht
      rcases this with h1 | h2
      · exfalso
        rw [h1] at ht
        exact huniv ht
      · exact h2

-- 连续映射
def Continuous {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop :=
  ∀ s, IsOpen s → IsOpen (f ⁻¹' s)

-- 连续映射的复合
theorem Continuous.comp {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {f : X → Y} {g : Y → Z}
    (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := by
  intro s hs
  rw [Set.preimage_comp]
  apply hf
  apply hg
  exact hs
```

### 紧致性

```lean4
import Mathlib

-- 开覆盖
def IsOpenCover {X : Type u} [TopologicalSpace X] (ι : Type v)
    (U : ι → Set X) : Prop :=
  ∀ i, IsOpen (U i) ∧ ⋃ i, U i = Set.univ

-- 紧致性
def IsCompact {X : Type u} [TopologicalSpace X] (K : Set X) : Prop :=
  ∀ {ι : Type v} (U : ι → Set X),
    (∀ i, IsOpen (U i)) → (K ⊆ ⋃ i, U i) →
    ∃ t : Finset ι, K ⊆ ⋃ i ∈ t, U i

-- Heine-Borel 定理在 R^n 中的形式
theorem isCompact_iff_closed_bounded {n : Nat} {K : Set (EuclideanSpace ℝ (Fin n))} :
    IsCompact K ↔ IsClosed K ∧ Bornology.IsBounded K := by
  rw [isCompact_iff_bounded_closed]
  · -- 证明等价性
    sorry
  · -- 选择适当的 UniformSpace 实例
    sorry
```

---

## 度量结构

### 度量空间 (Metric Space)

```lean4
import Mathlib

-- 度量空间的定义
class MetricSpace (α : Type u) extends PseudoMetricSpace α where
  eq_of_dist_eq_zero : ∀ {x y : α}, dist x y = 0 → x = y

-- 伪度量空间（允许距离为零的不同点）
class PseudoMetricSpace (α : Type u) where
  dist : α → α → ℝ
  dist_self : ∀ x, dist x x = 0
  dist_comm : ∀ x y, dist x y = dist y x
  dist_triangle : ∀ x y z, dist x z ≤ dist x y + dist y z

-- 度量空间的例子：实数
def Real.metricSpace : MetricSpace Real where
  dist x y := |x - y|
  dist_self x := by simp
  dist_comm x y := by simp [abs_sub_comm]
  dist_triangle x y z := by
    have h : x - z = (x - y) + (y - z) := by ring
    rw [h]
    apply abs_add
  eq_of_dist_eq_zero {x y} h := by
    simp at h
    linarith

-- 度量空间诱导拓扑
instance MetricSpace.toTopologicalSpace {α : Type u} [MetricSpace α] :
    TopologicalSpace α where
  IsOpen s := ∀ x ∈ s, ∃ ε > 0, ∀ y, dist y x < ε → y ∈ s
  isOpen_univ := by
    intro x _
    use 1
    simp
  isOpen_inter s t hs ht x hx := by
    rcases hx with ⟨hxs, hxt⟩
    rcases hs x hxs with ⟨ε1, hε1, h1⟩
    rcases ht x hxt with ⟨ε2, hε2, h2⟩
    use min ε1 ε2, by simp [hε1, hε2]
    intro y hy
    constructor
    · apply h1
      linarith [min_le_left ε1 ε2, hy]
    · apply h2
      linarith [min_le_right ε1 ε2, hy]
  isOpen_sUnion s h x hx := by
    rcases hx with ⟨t, ht, hxt⟩
    rcases h t ht x hxt with ⟨ε, hε, he⟩
    use ε, hε
    intro y hy
    refine ⟨t, ht, he y hy⟩

-- 完备度量空间
class CompleteSpace (α : Type u) [MetricSpace α] where
  complete : ∀ {f : Filter α}, Cauchy f → ∃ x, Tendsto f (𝓝 x)

-- 完备化
def Completion (α : Type u) [MetricSpace α] : Type u :=
  { f : Filter α // Cauchy f }
```

### 范数空间

```lean4
import Mathlib

-- 赋范向量空间
class NormedSpace (K : Type u) (V : Type v) [NormedField K] [SeminormedAddCommGroup V]
    extends Module K V where
  norm_smul_le : ∀ (c : K) (x : V), ‖c • x‖ ≤ ‖c‖ * ‖x‖

-- Banach 空间（完备的赋范空间）
class BanachSpace (K : Type u) (V : Type v) [NormedField K] [NormedAddCommGroup V]
    extends NormedSpace K V where
  complete : CompleteSpace V

-- Hilbert 空间（完备的内积空间）
class InnerProductSpace (K : Type u) (V : Type v) [RCLike K] [SeminormedAddCommGroup V]
    extends NormedSpace K V where
  inner : V → V → K
  conj_symm : ∀ x y, inner x y = star (inner y x)
  nonneg_re : ∀ x, 0 ≤ re (inner x x)
  definite : ∀ x, inner x x = 0 → x = 0
  add_left : ∀ x y z, inner (x + y) z = inner x z + inner y z
  smul_left : ∀ r x y, inner (r • x) y = r * inner x y
```

---

## 流形结构

### 拓扑流形

```lean4
import Mathlib

-- 图卡（Chart）
structure Chart (M : Type u) [TopologicalSpace M] (n : Nat) where
  source : Set M
  target : Set (EuclideanSpace ℝ (Fin n))
  toFun : source → target
  invFun : target → source
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y
  continuous_toFun : ContinuousOn toFun source
  continuous_invFun : ContinuousOn invFun target
  open_source : IsOpen source
  open_target : IsOpen target

-- 图册（Atlas）
structure Atlas (M : Type u) [TopologicalSpace M] (n : Nat) where
  charts : Set (Chart M n)
  covers : ⋃ c ∈ charts, c.source = Set.univ
  compatible : ∀ c1 ∈ charts, ∀ c2 ∈ charts,
    ContinuousOn (c2.toFun ∘ c1.invFun) (c1.toFun '' (c1.source ∩ c2.source))

-- 拓扑流形
typealias TopologicalManifold (n : Nat) (M : Type u) [TopologicalSpace M] :=
  { atlas : Atlas M n // atlas.covers = Set.univ }
```

### 光滑流形

```lean4
import Mathlib

-- 光滑映射
def Smooth (n m : Nat) {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (f : M → N) (atlasM : Atlas M n) (atlasN : Atlas N m) : Prop :=
  ∀ cM ∈ atlasM.charts, ∀ cN ∈ atlasN.charts,
    ContDiffOn ℝ ⊤ (cN.toFun ∘ f ∘ cM.invFun)
      (cM.toFun '' (cM.source ∩ f ⁻¹' cN.source))

-- 光滑流形
class SmoothManifold (n : Nat) (M : Type u) [TopologicalSpace M] where
  atlas : Atlas M n
  smooth_transition : ∀ c1 ∈ atlas.charts, ∀ c2 ∈ atlas.charts,
    Smooth n n (c2.toFun ∘ c1.invFun) atlas atlas

-- 切空间（在点 p 处）
def TangentSpace (M : Type u) [TopologicalSpace M] [SmoothManifold n M]
    (p : M) : Type u :=
  { v : (c : Chart M n) → c.target → ℝ //
    ∀ c1 c2, ∀ x ∈ c1.target,
      v c2 (c2.toFun (c1.invFun x)) =
        deriv (c2.toFun ∘ c1.invFun) x (v c1 x) }

-- 向量场
def VectorField (M : Type u) [TopologicalSpace M] [SmoothManifold n M] :=
  ∀ p : M, TangentSpace M p
```

### 张量丛

```lean4
import Mathlib

-- 张量空间
def TensorSpace (V : Type u) [AddCommGroup V] [Module ℝ V] (p q : Nat) : Type u :=
  (Fin p → V) → (Fin q → V) → ℝ

-- 张量丛
def TensorBundle (M : Type u) [TopologicalSpace M] [SmoothManifold n M]
    (p q : Nat) : Type u :=
  Σ x : M, TensorSpace (TangentSpace M x) p q

-- Riemann 度量
def RiemannianMetric (M : Type u) [TopologicalSpace M] [SmoothManifold n M] :=
  ∀ x : M, TensorSpace (TangentSpace M x) 0 2
```

---

## 实例详解

### 实例1：证明 ℤ/nℤ 是域（当 n 为素数）

```lean4
import Mathlib

-- 有限域 ZMod p
theorem ZMod.isField (p : Nat) (hp : Nat.Prime p) : IsField (ZMod p) := by
  have h1 : Fact p.Prime := ⟨hp⟩
  infer_instance

-- 另一种证明方式
theorem ZMod.mul_inv_cancel (p : Nat) (hp : Nat.Prime) (a : ZMod p) (ha : a ≠ 0) :
    a * a⁻¹ = 1 := by
  have h1 : a.val < p := a.val_lt
  have h2 : a.val ≠ 0 := by
    intro h
    have : a = 0 := by
      rw [← ZMod.val_zero p]
      apply ZMod.val_injective
      simp [h]
    contradiction

  have h3 : Nat.Coprime a.val p := by
    apply Nat.coprime_iff_gcd_eq_one.mpr
    have h4 : a.val.gcd p ∣ p := Nat.gcd_dvd_right a.val p
    have h5 : a.val.gcd p ∣ a.val := Nat.gcd_dvd_left a.val p
    have h6 : a.val.gcd p = 1 := by
      have h7 : Nat.Prime p := hp
      have h8 : a.val.gcd p = 1 ∨ a.val.gcd p = p := by
        apply (Nat.dvd_prime h7).mp h4
      rcases h8 with h9 | h9
      · exact h9
      · have h10 : p ∣ a.val := by
          rw [←h9]
          exact h5
        have h11 : a.val < p := h1
        have h12 : a.val = 0 := by
          linarith [Nat.le_of_dvd (by nlinarith) h10]
        contradiction
    exact h6

  -- 使用扩展欧几里得算法
  have h7 : ∃ x y, a.val * x + p * y = 1 := by
    apply Nat.gcd_eq_gcd_ab a.val p
    rw [Nat.coprime_iff_gcd_eq_one.mp h3]

  rcases h7 with ⟨x, y, hxy⟩
  -- 继续证明 a * a⁻¹ = 1
  sorry
```

### 实例2：证明单位圆是光滑流形

```lean4
import Mathlib

-- 单位圆 S^1
def S1 := { p : ℝ × ℝ // p.1^2 + p.2^2 = 1 }

namespace S1

-- 上半圆的图卡
def upperChart : Chart S1 1 where
  source := { p : S1 | p.1.2 > 0 }
  target := { x : EuclideanSpace ℝ (Fin 1) | x 0 > -1 ∧ x 0 < 1 }
  toFun p := fun _ => p.1.1
  invFun x := ⟨(x 0, Real.sqrt (1 - (x 0)^2)), by
    have h : (x 0)^2 + (Real.sqrt (1 - (x 0)^2))^2 = 1 := by
      rw [Real.sq_sqrt]
      · ring
      · have h1 : (x 0) > -1 := x.2.1
        have h2 : (x 0) < 1 := x.2.2
        nlinarith
    exact h
  ⟩
  left_inv p := by
    simp
    have h : p.1.2 > 0 := p.2
    have h2 : p.1.2 = Real.sqrt (1 - p.1.1^2) := by
      have h3 : p.1.1^2 + p.1.2^2 = 1 := p.1.2
      have h4 : p.1.2^2 = 1 - p.1.1^2 := by linarith
      have h5 : p.1.2 = Real.sqrt (p.1.2^2) := by
        rw [Real.sqrt_sq]
        linarith
      rw [h5, h4]
    rw [h2]
  right_inv x := by
    funext i
    simp
  continuous_toFun := by
    -- 证明连续性
    sorry
  continuous_invFun := by
    -- 证明连续性
    sorry
  open_source := by
    -- 证明开集
    sorry
  open_target := by
    -- 证明开集
    sorry

-- 类似定义其他图卡...

end S1
```

### 实例3：矩阵群 GL(n, ℝ)

```lean4
import Mathlib

-- 一般线性群
def GL (n : Nat) (R : Type u) [CommRing R] : Type u :=
  { A : Matrix (Fin n) (Fin n) R // IsUnit A.det }

namespace GL

variable {n : Nat} {R : Type u} [CommRing R]

-- 矩阵乘法
instance : Mul (GL n R) where
  mul A B := ⟨A.1 * B.1, by
    have h1 : IsUnit A.1.det := A.2
    have h2 : IsUnit B.1.det := B.2
    have h3 : (A.1 * B.1).det = A.1.det * B.1.det := by
      simp [Matrix.det_mul]
    rw [h3]
    apply IsUnit.mul h1 h2
  ⟩

-- 单位元
instance : One (GL n R) where
  one := ⟨1, by simp; infer_instance⟩

-- 逆元
instance : Inv (GL n R) where
  inv A := ⟨A.1⁻¹, by
    have h1 : IsUnit A.1.det := A.2
    have h2 : IsUnit A.1.det⁻¹ := h1.inv
    have h3 : (A.1⁻¹).det = A.1.det⁻¹ := by
      simp [Matrix.det_inv]
    rw [h3]
    exact h2
  ⟩

-- 证明这是群
instance : Group (GL n R) where
  mul_assoc A B C := by
    ext
    simp [mul_assoc]
  one_mul A := by
    ext
    simp
  mul_one A := by
    ext
    simp
  inv_mul_cancel A := by
    ext
    simp

end GL
```

---

## 类型类层次结构

Lean4 中数学结构的层次关系：

```
Groupoid
  └── Group
        ├── CommGroup
        └── Ring
              ├── CommRing
              │     └── Field
              └── LieRing

Module R M
  └── VectorSpace K V
        ├── NormedSpace K V
        │     └── BanachSpace K V
        │           └── HilbertSpace K V
        └── InnerProductSpace K V
              └── HilbertSpace K V

TopologicalSpace X
  └── MetricSpace X
        └── CompleteSpace X
              └── PolishSpace X

SmoothManifold n M
  └── RiemannianManifold n M
        └── SymplecticManifold n M
```

---

## 总结

本文档涵盖了 Lean4 中主要数学结构的实现：

| 结构 | Mathlib 类型类 | 关键特征 |
|------|---------------|----------|
| 群 | `Group` | 单位元、逆元、结合律 |
| 环 | `Ring` | 加法群 + 乘法半群 + 分配律 |
| 域 | `Field` | 可交换环 + 非零逆元 |
| 模 | `Module R M` | 环上的向量空间推广 |
| 向量空间 | `VectorSpace K V` | 域上的模 |
| 拓扑空间 | `TopologicalSpace` | 开集公理 |
| 度量空间 | `MetricSpace` | 距离函数 |
| 赋范空间 | `NormedSpace` | 范数 + 模结构 |
| 光滑流形 | `SmoothManifold` | 图册 + 光滑过渡 |

---

*本文档是 FormalMath 项目的一部分，详细介绍数学结构在 Lean4 中的实现方法。*
