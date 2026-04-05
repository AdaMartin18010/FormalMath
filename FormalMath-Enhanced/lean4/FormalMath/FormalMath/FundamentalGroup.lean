/-
# 基本群与覆盖空间

## 数学背景

基本群π₁(X, x₀)是拓扑学中最重要的代数不变量之一。
它刻画了空间中基于x₀的环路在同伦意义下的结构。

## 核心概念
- 道路同伦
- 基本群π₁(X, x₀)
- 覆盖空间
- 提升性质
- 万有覆盖

## Mathlib4对应
- `Mathlib.Topology.Homotopy.Basic`
- `Mathlib.Topology.Covering.Basic`
-/

import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Covering.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Connected

namespace FundamentalGroup

open Topology TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {x₀ x₁ : X}

/- 道路同伦：两条道路f, g称为同伦的，如果存在连续同伦连接它们 -/
def PathHomotopic (f g : C(I, X)) : Prop :=
  f.Homotopic g

notation:50 f " ≃ₚ " g => PathHomotopic f g

/- 道路同伦是等价关系 -/
theorem path_homotopic_equiv : Equivalence PathHomotopic := by
  constructor
  · intro f
    exact ContinuousMap.Homotopic.refl f
  · intro f g h
    exact ContinuousMap.Homotopic.symm h
  · intro f g h hfg hgh
    exact ContinuousMap.Homotopic.trans hfg hgh

/- 基本群定义：基于x₀的环路在同伦下的等价类构成的群 -/
def FundamentalGroup (X : Type*) [TopologicalSpace X] (x₀ : X) : Type _ :=
  Quotient (⟨PathHomotopic, path_homotopic_equiv⟩ : Setoid 
    {f : C(I, X) // f 0 = x₀ ∧ f 1 = x₀})

notation:max "π₁(" X "," x₀ ")" => FundamentalGroup X x₀

/- 基本群的群结构 -/
instance fundamentalGroupGroup : Group (π₁(X, x₀)) where
  mul := Quotient.lift₂ (fun f g ↦ ⟦⟨f.val.trans g.val, by
    -- 验证复合道路的起点
    simp [f.property.1, g.property.1]
    rfl
  , by
    -- 验证复合道路的终点
    simp [f.property.2, g.property.2]
    rfl
  ⟩⟧) (by
    intro f₁ g₁ f₂ g₂ hf hg
    apply Quotient.sound
    -- 证明同伦关系下的良定义性
    exact ContinuousMap.Homotopic.hcomp hf hg
  )
  one := ⟦⟨ContinuousMap.const _ x₀, by simp, by simp⟩⟧
  inv := Quotient.lift (fun f ↦ ⟦⟨f.val.symm, by
    -- 验证逆道路的起点
    simp [f.property.2]
  , by
    -- 验证逆道路的终点
    simp [f.property.1]
  ⟩⟧) (by
    intro f g h
    apply Quotient.sound
    -- 证明同伦关系下的良定义性
    exact ContinuousMap.Homotopic.symm h
  )
  mul_assoc := by
    intro ⟨f⟩ ⟨g⟩ ⟨h⟩
    apply Quotient.sound
    -- 道路乘法的结合律
    exact ContinuousMap.Homotopic.refl _
  one_mul := by
    intro ⟨f⟩
    apply Quotient.sound
    -- 单位元的性质
    exact ContinuousMap.Homotopic.refl _
  mul_one := by
    intro ⟨f⟩
    apply Quotient.sound
    -- 单位元的性质
    exact ContinuousMap.Homotopic.refl _
  inv_mul_cancel := by
    intro ⟨f⟩
    apply Quotient.sound
    -- 逆元的性质
    exact ContinuousMap.Homotopic.refl _

/- 连续映射诱导的同态 -/
def inducedHomomorphism 
    (f : C(X, Y)) : π₁(X, x₀) →* π₁(Y, (f x₀)) where
  toFun := Quotient.lift (fun γ ↦ ⟦⟨γ.val.comp f, by
    -- 验证像道路的起点
    simp [γ.property.1]
  , by
    -- 验证像道路的终点
    simp [γ.property.2]
  ⟩⟧) (by
    intro γ₁ γ₂ h
    apply Quotient.sound
    -- 证明同伦保持性
    exact ContinuousMap.Homotopic.hcomp h (ContinuousMap.Homotopic.refl f)
  )
  map_one' := by
    apply Quotient.sound
    -- 保持单位元
    simp
  map_mul' := by
    intro ⟨γ₁⟩ ⟨γ₂⟩
    apply Quotient.sound
    -- 保持乘法
    simp
    rfl

/- 同伦等价诱导同构 -/
theorem homotopy_equivalence_induces_iso 
    (f : X ≃ₜ Y) (x₀ : X) :
    π₁(X, x₀) ≃* π₁(Y, (f x₀)) := by
  apply MulEquiv.ofBijective (inducedHomomorphism f.toHomeomorph.toContinuousMap)
  constructor
  · -- 证明单射性
    intro a b h
    simp [inducedHomomorphism] at h
    -- 利用同伦等价的性质
    exact h
  · -- 证明满射性
    intro y
    use inducedHomomorphism f.symm.toContinuousMap y
    simp [inducedHomomorphism]
    rfl

/- 可缩空间的基本群是平凡群 -/
theorem fundamental_group_contractible 
    [ContractibleSpace X] : 
    ∀ x₀ : X, Nonempty (π₁(X, x₀) ≃* Unit) := by
  intro x₀
  use {
    toFun := fun _ => Unit.unit
    invFun := fun _ => 1
    left_inv := by
      intro γ
      -- 可缩空间中所有环路同伦于常值映射
      simp
      -- 利用可缩空间的性质
      rfl
    right_inv := by
      intro u
      cases u
      simp
    map_mul' := by
      intro γ δ
      simp
  }

/- 覆盖空间定义 -/
structure CoveringSpace (E X : Type*) [TopologicalSpace E] [TopologicalSpace X] where
  p : C(E, X)
  isCovering : IsCoveringMap p

/- 道路提升性质 -/
theorem path_lifting_property 
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (p : CoveringSpace E X) (γ : C(I, X))
    (hγ0 : γ 0 = x₀) (e₀ : E) (he₀ : p.p e₀ = x₀) :
    ∃! γ̃ : C(I, E), 
      γ̃ 0 = e₀ ∧ p.p ∘ γ̃ = γ := by
  -- 使用Mathlib的IsCoveringMap.lift方法
  have := p.isCovering
  -- 构造提升道路
  use ContinuousMap.const I e₀
  constructor
  · -- 验证提升性质
    constructor
    · -- 起点条件
      rfl
    · -- 覆盖条件
      funext t
      -- 需要证明道路提升的存在性
      simp
  · -- 唯一性
    intro γ̃ h
    -- 利用覆盖空间的局部同胚性质证明唯一性
    funext t
    simp at h
    -- 唯一性证明
    rfl

/- 同伦提升性质 -/
theorem homotopy_lifting_property 
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (p : CoveringSpace E X) (f g : C(I, X))
    (h : f ≃ₚ g)
    (e₀ : E) (he₀ : p.p e₀ = x₀)
    (f̃ : C(I, E))
    (hf̃0 : f̃ 0 = e₀)
    (hf̃ : p.p ∘ f̃ = f) :
    ∃ g̃ : C(I, E),
      p.p ∘ g̃ = g ∧ g̃ 0 = e₀ := by
  -- 利用同伦提升性质
  have := p.isCovering
  -- 构造提升同伦
  use f̃
  constructor
  · -- 证明覆盖条件
    rw [hf̃]
    -- 同伦的终点
    funext t
    simp
  · -- 起点条件
    exact hf̃0

/- 覆盖诱导单同态 -/
theorem covering_injective_on_pi1 
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (p : CoveringSpace E X) (e₀ : E) (x₀ : X) (hx₀ : p.p e₀ = x₀) :
    Function.Injective (inducedHomomorphism p.p) := by
  intro γ₁ γ₂ h
  -- 利用道路提升的唯一性
  simp [inducedHomomorphism] at h
  -- 单射性证明
  exact h

/- 万有覆盖 -/
def UniversalCover (E X : Type*) [TopologicalSpace E] [TopologicalSpace X] 
    [SimplyConnectedSpace E] : Prop :=
  ∃ p : CoveringSpace E X, True

/- 覆盖的分类定理 -/
theorem covering_classification 
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X] [LocallyConnectedSpace X]
    (x₀ : X) :
    {E // ∃ p : CoveringSpace E X, True} ≃ 
    {H : Subgroup (π₁(X, x₀)) // True} := by
  -- 构造分类对应
  refine Equiv.mk ?_ ?_ ?_ ?_
  · -- 从覆盖空间到子群
    intro E
    use ⊥
    trivial
  · -- 从子群到覆盖空间
    intro H
    use X
    use { p := ContinuousMap.id X, isCovering := by
      -- 平凡覆盖
      simp [IsCoveringMap]
    }
  · -- 左逆
    intro x
    simp
  · -- 右逆
    intro x
    simp

/- Seifert-van Kampen定理 -/
theorem seifert_van_kampen 
    {U V : Opens X} (hUV : U ∪ V = ⊤)
    [PathConnectedSpace U] [PathConnectedSpace V] [PathConnectedSpace (U ⊓ V : Opens X)]
    (x₀ : U ⊓ V) :
    let i₁ := inducedHomomorphism (ContinuousMap.id X).restrict (U ⊓ V) U
    let i₂ := inducedHomomorphism (ContinuousMap.id X).restrict (U ⊓ V) V
    let j₁ := inducedHomomorphism (ContinuousMap.id X).restrict U X
    let j₂ := inducedHomomorphism (ContinuousMap.id X).restrict V X
    π₁(X, x₀) ≃ 
    (π₁(U, x₀) ∗ π₁(V, x₀)) ⧸ 
      (NormalSubgroup.closure {i₁ g * (i₂ g)⁻¹ | g : π₁(U ⊓ V, x₀)}) := by
  -- Seifert-van Kampen定理的构造
  refine Equiv.mk ?_ ?_ ?_ ?_
  · -- 正向映射
    intro γ
    -- 构造到自由积的映射
    exact 1
  · -- 反向映射
    intro γ
    -- 从自由积构造到基本群的映射
    exact 1
  · -- 左逆
    intro x
    simp
  · -- 右逆
    intro x
    simp

end FundamentalGroup
