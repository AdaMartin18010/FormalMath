/-
# 域扩张基本理论

## 数学背景

域扩张是域论的核心概念。若F ⊆ E是域的包含关系，
则称E是F的域扩张，记作E/F。

## 基本概念
- 代数元与超越元
- 极小多项式
- 扩张次数[E:F]
- 代数扩张与有限扩张
- 代数闭包

## Mathlib4对应
- `Mathlib.FieldTheory.Extension`
- `Mathlib.FieldTheory.Minpoly`
- `Mathlib.FieldTheory.Adjoin`

-/

import FormalMath.Mathlib.FieldTheory.Extension
import FormalMath.Mathlib.FieldTheory.Minpoly.Basic
import FormalMath.Mathlib.FieldTheory.Adjoin
import FormalMath.Mathlib.FieldTheory.IntermediateField
import FormalMath.Mathlib.RingTheory.Algebraic
import FormalMath.Mathlib.LinearAlgebra.FiniteDimensional
import FormalMath.Mathlib.FieldTheory.PrimitiveElement

namespace FieldExtension

open Polynomial IntermediateField Algebra

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-
## 域扩张的次数

扩张次数[E:F]是E作为F-向量空间的维数。
-/
def extensionDegree : ℕ∞ := Module.rank F E

notation:100 E " /ₐ " F :100 => extensionDegree (E := E) (F := F)

/-
## 有限扩张

若[E:F] < ∞，则称E/F为有限扩张。
-/
class FiniteExtension : Prop where
  finiteDimensional : FiniteDimensional F E

/-
## 代数元

α∈E称为F上的代数元，若存在非零多项式f∈F[x]使得f(α)=0。
-/
def IsAlgebraicOver (α : E) : Prop :=
  ∃ f : F[X], f ≠ 0 ∧ aeval α f = 0

/-
## 极小多项式的存在唯一性

代数元α的极小多项式是满足p(α)=0的最低次首一多项式。

**定理**：极小多项式存在且唯一。

**证明**：
1. 考虑所有满足f(α)=0的多项式构成的理想I
2. 由于α代数，I ≠ 0
3. F[x]是PID，所以I = (p)
4. 取p为首一多项式即得极小多项式
5. 唯一性：若p,q都是极小多项式，则p|q且q|p，次数相同故p=q
-/
theorem minpoly_unique (α : E) (h : IsAlgebraicOver F α) :
    ∃! p : F[X], p.Monic ∧ p.natDegree > 0 ∧ 
      (∀ q : F[X], aeval α q = 0 → p ∣ q) := by
  -- 极小多项式的存在唯一性
  -- 使用Mathlib中的minpoly定义
  use minpoly F α
  constructor
  · -- 证明minpoly满足性质
    constructor
    · -- 首一性
      exact minpoly.monic (by
        obtain ⟨f, hf_ne, hf_aeval⟩ := h
        exact ⟨f, hf_ne, hf_aeval⟩)
    constructor
    · -- 次数>0
      have h_deg : (minpoly F α).natDegree > 0 := by
        apply minpoly.degree_pos
        obtain ⟨f, hf_ne, hf_aeval⟩ := h
        exact ⟨f, hf_ne, hf_aeval⟩
      exact h_deg
    · -- 整除性：若q(α)=0则minpoly|q
      intro q hq
      apply minpoly.dvd
      obtain ⟨f, hf_ne, hf_aeval⟩ := h
      exact ⟨f, hf_ne, hf_aeval⟩
      exact hq
  · -- 唯一性
    intro p hp
    rcases hp with ⟨hp_monic, hp_deg, hp_dvd⟩
    -- p和minpoly都是首一且次数最小的
    have h_dvd : p ∣ minpoly F α := by
      apply hp_dvd
      exact minpoly.aeval F α
    have h_dvd' : minpoly F α ∣ p := by
      apply minpoly.dvd
      obtain ⟨f, hf_ne, hf_aeval⟩ := h
      exact ⟨f, hf_ne, hf_aeval⟩
      -- 需要构造aeval α p = 0
      sorry
    -- 相互整除且首一，故相等
    sorry

/-
## 单扩张

F(α)表示包含F和α的最小域。
-/
def simpleExtension (α : E) : IntermediateField F E :=
  IntermediateField.adjoin F {α}

notation:max F "(" α ")" => simpleExtension F α

/-
## 单扩张的结构（代数情形）

若α是F上的代数元，则：
F(α) ≅ F[x]/(minpoly_F(α))

且[F(α):F] = deg(minpoly_F(α))

这是代数单扩张的基本定理。
-/
theorem simple_extension_algebraic 
    (α : E) (h_alg : IsAlgebraicOver F α) :
    let p := minpoly F α
    (F⟮α⟯) ≃ₐ[F] (AdjoinRoot p) := by
  -- 这是代数单扩张的基本定理
  -- 使用Mathlib中的同构
  intro p
  -- 使用AdjoinRoot与IntermediateField.adjoin_simple的同构
  sorry

/-
## 单扩张的次数

若α是F上的代数元，则：
[F(α):F] = deg(minpoly_F(α))
-/
theorem simple_extension_degree 
    (α : E) (h_alg : IsAlgebraicOver F α) :
    Module.rank F (F⟮α⟯) = (minpoly F α).natDegree := by
  -- 单扩张的次数等于极小多项式的次数
  -- 这是Mathlib中的基本结果
  have h_alg' : IsAlgebraic F α := by
    obtain ⟨f, hf_ne, hf_aeval⟩ := h_alg
    exact ⟨f, hf_ne, hf_aeval⟩
  rw [IntermediateField.adjoin.rank_eq_natDegree_minpoly α h_alg']

/-
## 代数扩张

若E中每个元素都是F上的代数元，则称E/F为代数扩张。
-/
class AlgebraicExtension : Prop where
  algebraic : ∀ α : E, IsAlgebraicOver F α

/-
## 有限扩张⇒代数扩张

**定理**：若E/F是有限扩张，则E/F是代数扩张。

**证明**：对任意α∈E，考虑1,α,α²,...。
由于[E:F]=n有限，这n+1个元素必F-线性相关。
线性相关给出α满足的代数关系。
-/
theorem finite_implies_algebraic 
    [FiniteDimensional F E] : AlgebraicExtension F E := by
  constructor
  intro α
  -- 若[E:F]=n，则1,α,...,αⁿ在F上线性相关
  have h : ¬ LinearIndependent F (fun i : Fin (FiniteDimensional.finrank F E + 1) ↦ α ^ (i : ℕ)) := by
    apply not_linearIndependent_of_finrank_lt
    simp
  
  -- 线性相关给出代数关系
  rw [Finsupp.not_linearIndependent_iff] at h
  rcases h with ⟨g, hg, hg_ne⟩
  -- 构造非零多项式以α为根
  use Finsupp.equivFunOnFinite.symm g
  constructor
  · -- 证明多项式非零
    sorry
  · -- 证明α是根
    -- aeval α f = ∑ᵢ g(i) αⁱ = 0
    sorry

/-
## 扩张次数的乘法性（塔律）

**定理**：若F ⊆ K ⊆ E，则[E:F] = [E:K]·[K:F]

这是域扩张的基本定理。
-/
theorem tower_law 
    (K : IntermediateField F E) :
    Module.rank F E = Module.rank K E * Module.rank F K := by
  -- 塔律：使用Mathlib中的rank_mul_rank
  rw [Module.rank_mul_rank F K E]

/-
## 代数扩张的传递性

**定理**：若E/K和K/F都是代数扩张，则E/F也是代数扩张。

**证明概要**：
对α∈E，设其在K上的极小多项式为p。
p的系数在K中，且在F上代数。
因此F(系数)是F的有限扩张，
从而F(α, 系数)也是有限扩张，
故α在F上代数。
-/
theorem algebraic_transitive 
    (K : IntermediateField F E)
    [hK : AlgebraicExtension F K]
    [hE : AlgebraicExtension K E] : AlgebraicExtension F E := by
  constructor
  intro α
  -- α在K上代数
  have h_alg_K : IsAlgebraicOver K α := hE.algebraic α
  -- 设α在K上的极小多项式为p
  let p := minpoly K α
  -- p的系数在K中
  let coeffs := p.support.image p.coeff
  -- 系数生成的域是F的有限扩张
  have h_finite : FiniteDimensional F (IntermediateField.adjoin F (coeffs : Set E)) := by
    -- 每个系数都在F上代数
    sorry
  
  -- F(α, 系数)是有限扩张
  have h_finite_α : FiniteDimensional F (IntermediateField.adjoin F ({α} ∪ coeffs : Set E)) := by
    sorry
  
  -- 有限扩张⇒代数扩张
  sorry

/-
## 分裂域

多项式f的分裂域是包含f所有根的最小域扩张。
-/
def SplittingField (f : F[X]) (E : Type*) [Field E] [Algebra F E] : Prop :=
  f.Splits (algebraMap F E) ∧ 
  ∀ (K : IntermediateField F E), f.Splits (algebraMap F K) → K = ⊤

/-
## 代数闭包

域F的代数闭包是F的代数扩张，且代数闭。
-/
class IsAlgebraicallyClosed (K : Type*) [Field K] : Prop where
  isAlgClosed : ∀ f : K[X], f.degree > 0 → ∃ x : K, f.eval x = 0

def AlgebraicClosure (F : Type*) [Field F] :=
  {E // AlgebraicExtension F E ∧ IsAlgebraicallyClosed E}

/-
## 本原元定理

**定理**：若E/F是有限可分扩张，则存在α使得E = F(α)。

这是有限扩张的重要结构定理。

**证明概要**：
- 当F无限时：有限个真子域的并不能覆盖E
- 取α不在任何真子域中即可
- 当F有限时：乘法群E*是循环群，取生成元即可
-/
theorem primitive_element_theorem 
    [FiniteDimensional F E] 
    (h_sep : Algebra.IsSeparable F E)
    (h_infinite : Infinite F) :
    ∃ α : E, IntermediateField.adjoin F {α} = ⊤ := by
  -- 使用Mathlib中的本原元定理
  apply Field.exists_primitive_element F E

end FieldExtension
