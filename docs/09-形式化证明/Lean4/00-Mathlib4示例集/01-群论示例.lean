import Mathlib.Algebra.Group.Basic
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.QuotientGroup
import Mathlib.GroupTheory.Coset
import Mathlib.GroupTheory.Sylow

/-! 
# 群论示例

对应的FormalMath文档：
- docs/02-代数结构/02-核心理论/群论/01-群论-国际标准深度扩展版.md
- docs/02-代数结构/02-核心理论/群论/01-群论-深度扩展版.md

对应的Mathlib4模块：
- Mathlib.Algebra.Group.Basic
- Mathlib.GroupTheory.Subgroup.Basic
- Mathlib.GroupTheory.QuotientGroup
- Mathlib.GroupTheory.Coset
- Mathlib.GroupTheory.Sylow

## 核心定义

在Mathlib4中，群是一个类型类（Type Class），定义了集合上的群结构。
-/ 

-- 查看群的定义
#check Group

-- 群的基本操作
section GroupOperations
variable {G : Type*} [Group G]

-- 单位元
example : G := (1 : G)

-- 乘法
example (a b : G) : G := a * b

-- 逆元
example (a : G) : G := a⁻¹

-- 群的公理
example (a b c : G) : (a * b) * c = a * (b * c) := by
  rw [mul_assoc]

example (a : G) : 1 * a = a := by
  rw [one_mul]

example (a : G) : a * 1 = a := by
  rw [mul_one]

example (a : G) : a⁻¹ * a = 1 := by
  rw [inv_mul_cancel]

example (a : G) : a * a⁻¹ = 1 := by
  rw [mul_inv_cancel]

end GroupOperations

/-! 
## 关键定理

### 逆元的性质

Mathlib4提供了丰富的群论定理库。
-/

section InverseProperties
variable {G : Type*} [Group G]

-- 逆元的逆元是自身
example (a : G) : (a⁻¹)⁻¹ = a := by
  rw [inv_inv]

-- 乘积的逆元
example (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  rw [mul_inv_rev]

-- 单位元的逆元
example : (1 : G)⁻¹ = 1 := by
  rw [inv_one]

end InverseProperties

/-! 
## 子群

子群是群的子集，自身也构成群结构。
-/

section Subgroups
variable {G : Type*} [Group G]

-- 子群定义检查
#check Subgroup G

-- 平凡子群 {1}
example : Subgroup G where
  carrier := {1}
  mul_mem' := by
    simp
    <;> tauto
  one_mem' := by simp
  inv_mem' := by
    simp
    <;> tauto

-- 整个群作为子群
example : Subgroup G where
  carrier := Set.univ
  mul_mem' := by
    simp
  one_mem' := by simp
  inv_mem' := by simp

-- 中心化子示例
example (a : G) : Subgroup G where
  carrier := {g : G | g * a = a * g}
  mul_mem' := by
    intro g h hg hh
    simp at hg hh ⊢
    calc
      (g * h) * a = g * (h * a) := by rw [mul_assoc]
      _           = g * (a * h) := by rw [hh]
      _           = (g * a) * h := by rw [← mul_assoc]
      _           = (a * g) * h := by rw [hg]
      _           = a * (g * h) := by rw [mul_assoc]
  one_mem' := by simp
  inv_mem' := by
    intro g hg
    simp at hg ⊢
    calc
      g⁻¹ * a = g⁻¹ * (a * g) * g⁻¹ := by
        simp [mul_assoc]
      _       = g⁻¹ * (g * a) * g⁻¹ := by rw [hg]
      _       = a * g⁻¹ := by
        simp [mul_assoc]

end Subgroups

/-! 
## 商群

商群是通过正规子群构造的新群。
-/

section QuotientGroups
variable {G : Type*} [Group G] (N : Subgroup G) [N.Normal]

-- 商群定义
#check G ⧸ N

-- 商群上的群结构
example : Group (G ⧸ N) := by
  infer_instance

-- 商映射
example : G →* G ⧸ N := QuotientGroup.mk' N

-- 第一同构定理的核心引理
example {H : Type*} [Group H] (f : G →* H) :
    G ⧸ f.ker ≃* f.range := by
  exact QuotientGroup.quotientKerEquivRange f

end QuotientGroups

/-! 
## Lagrange定理

有限群的子群的阶整除群的阶。
-/

section LagrangeTheorem
open Fintype
variable {G : Type*} [Group G] [Fintype G] (H : Subgroup G)

-- Lagrange定理
example : card H ∣ card G := by
  exact ⟨H.index, by rw [Subgroup.index_mul_card]⟩

-- 子群的指数
example : ℕ := H.index

-- 关系：|G| = [G:H] · |H|
example : card G = H.index * card H := by
  rw [Subgroup.index_mul_card]

end LagrangeTheorem

/-! 
## Sylow定理

Sylow定理是关于有限群p-子群的重要定理组。
-/

section SylowTheorems
variable {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : Nat.Prime p)

-- Sylow p-子群
example : Type _ := Sylow p G

-- Sylow定理：存在Sylow p-子群
example : Nonempty (Sylow p G) := by
  infer_instance

-- Sylow定理：所有Sylow p-子群共轭
example (P Q : Sylow p G) : ∃ g : G, Q = P.map (MulAut.conj g) := by
  apply Sylow.isConj

-- Sylow定理：Sylow p-子群的数量满足同余条件
example : card (Sylow p G) ≡ 1 [MOD p] := by
  apply Sylow.card_eq_one_mod_p

end SylowTheorems

/-! 
## 示例：对称群 S₃

三元素的对称群是最小的非交换群。
-/

section SymmetricGroup

-- 对称群 S₃
example : Type _ := Equiv.Perm (Fin 3)

-- S₃是群
example : Group (Equiv.Perm (Fin 3)) := by
  infer_instance

-- S₃的阶是6
open Fintype in
example : card (Equiv.Perm (Fin 3)) = 6 := by
  simp

-- S₃的轮换表示
example (a b c : Fin 3) (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c) :
    Equiv.Perm (Fin 3) :=
  Equiv.swap a b * Equiv.swap b c

end SymmetricGroup

/-! 
## 练习

1. 证明：群的任意两个子群的交集仍然是子群。
2. 证明：指数为2的子群一定是正规子群。
3. 证明：有限群G中，任意元素a满足 a^|G| = 1。
4. 在S₃中找出所有子群，并验证Lagrange定理。
5. 证明：如果G是交换群，那么对于任意n，映射 f(a) = a^n 是群同态。

-/ 

section Exercises
variable {G : Type*} [Group G]

-- 练习1：子群的交集
example (H K : Subgroup G) : Subgroup G := H ⊓ K

-- 练习2：指数为2的子群是正规子群（提示）
example (H : Subgroup G) (h : H.index = 2) : H.Normal := by
  have := Subgroup.normal_of_index_two H
  apply this
  exact h

-- 练习3：元素的阶整除群的阶（提示使用Lagrange定理）
example [Fintype G] (a : G) : orderOf a ∣ card G := by
  exact orderOf_dvd_card

end Exercises
