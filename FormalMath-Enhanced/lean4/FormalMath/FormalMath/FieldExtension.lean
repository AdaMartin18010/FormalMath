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

import Mathlib.FieldTheory.Extension
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.FieldTheory.Adjoin
import Mathlib.FieldTheory.IntermediateField
import Mathlib.RingTheory.Algebraic
import Mathlib.LinearAlgebra.FiniteDimensional

namespace FieldExtension

open Polynomial IntermediateField Algebra

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-
## 域扩张的次数

扩张次数[E:F]是E作为F-向量空间的维数。
-/
def extensionDegree : ℕ∞ := Module.rank F E

notation:100 E " / " F :100 => extensionDegree (E := E) (F := F)

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
## 极小多项式

代数元α的极小多项式是满足p(α)=0的最低次首一多项式。
-/
theorem minpoly_unique (α : E) (h : IsAlgebraicOver F α) :
    ∃! p : F[X], p.Monic ∧ p.natDegree > 0 ∧ 
      (∀ q : F[X], aeval α q = 0 → p ∣ q) := by
  -- 极小多项式的存在唯一性
  sorry -- 需要极小多项式的定义

/-
## 单扩张

F(α)表示包含F和α的最小域。
-/
def simpleExtension (α : E) : IntermediateField F E :=
  IntermediateField.adjoin F {α}

notation:max F "(" α ")" => simpleExtension F α

/-
## 单扩张的结构

若α是F上的代数元，则：
F(α) ≅ F[x]/(minpoly_F(α))

且[F(α):F] = deg(minpoly_F(α))
-/
theorem simple_extension_algebraic 
    (α : E) (h_alg : IsAlgebraicOver F α) :
    let p := minpoly F α
    (F(α) ⧸ (p.ideal : Ideal (F(α)))) ≃ₐ[F] F(α) := by
  -- 这是代数单扩张的基本定理
  sorry -- 需要商环的同构

theorem simple_extension_degree 
    (α : E) (h_alg : IsAlgebraicOver F α) :
    Module.rank F (F(α)) = (minpoly F α).natDegree := by
  -- 单扩张的次数等于极小多项式的次数
  sorry -- 需要向量空间基的描述

/-
## 代数扩张

若E中每个元素都是F上的代数元，则称E/F为代数扩张。
-/
class AlgebraicExtension : Prop where
  algebraic : ∀ α : E, IsAlgebraicOver F α

/-
## 有限扩张⇒代数扩张

**定理**：若E/F是有限扩张，则E/F是代数扩张。

**证明**：对任意α∈E，1,α,α²,...在F上线性相关。
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
  -- 构造非零多项式
  use fun i ↦ g i
  constructor
  · -- 证明多项式非零
    sorry -- 从线性相关提取
  · -- 证明α是根
    sorry -- 需要多项式求值

/-
## 扩张次数的乘法性

**塔律**：若F ⊆ K ⊆ E，则[E:F] = [E:K]·[K:F]
-/
theorem tower_law 
    (K : IntermediateField F E) :
    Module.rank F E = Module.rank K E * Module.rank F K := by
  -- 这是域扩张的基本定理
  rw [Module.rank_mul_rank F K E]

/-
## 代数扩张的传递性

**定理**：若E/K和K/F都是代数扩张，则E/F也是代数扩张。

**证明**：对α∈E，考虑F上的极小多项式系数在K中，
这些系数在F上代数，故F(系数)是有限扩张，
从而F(α)也是有限扩张。
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
  -- p的系数在K中，且在F上代数
  -- 设p的次数为n
  let coeffs := p.coeffs
  -- 系数生成的域是有限扩张
  have h_finite : FiniteDimensional F (IntermediateField.adjoin F (coeffs.toSet)) := by
    sorry -- 需要代数元的有限生成
  
  -- F(α, 系数)是有限扩张
  have h_finite_α : FiniteDimensional F (IntermediateField.adjoin F ({α} ∪ coeffs.toSet)) := by
    sorry -- 需要扩张的组合
  
  -- 有限扩张⇒代数扩张
  sorry -- 应用前面的定理

/-
## 分裂域

多项式f的分裂域是包含f所有根的最小域扩张。
-/
def SplittingField (f : F[X]) (E : Type*) [Field E] [Algebra F E] : Prop :=
  ∀ g : F[X], g ∣ f → ∃ x : E, aeval x g = 0

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
-/
theorem primitive_element_theorem 
    [FiniteDimensional F E] 
    (h_sep : Algebra.IsSeparable F E)
    (h_infinite : Infinite F) :
    ∃ α : E, IntermediateField.adjoin F {α} = ⊤ := by
  -- 本原元定理的证明
  -- 关键步骤：有限个真子域的并不能覆盖整个域（当F无限时）
  sorry -- 需要可分扩张和本原元的理论

end FieldExtension
