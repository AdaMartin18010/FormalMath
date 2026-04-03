import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.UniqueFactorizationDomain
import Mathlib.RingTheory.Polynomial.Basic

/-! 
# 环论示例

对应的FormalMath文档：
- docs/02-代数结构/02-核心理论/环论/01-环论-国际标准深度扩展版.md
- docs/02-代数结构/02-核心理论/环论/01-环论-深度扩展版.md

对应的Mathlib4模块：
- Mathlib.Algebra.Ring.Basic
- Mathlib.Algebra.Field.Basic
- Mathlib.RingTheory.Ideal.Basic
- Mathlib.RingTheory.Ideal.Quotient
- Mathlib.RingTheory.PrincipalIdealDomain
- Mathlib.RingTheory.UniqueFactorizationDomain

## 核心定义
-/ 

-- 查看环的定义
#check Ring
#check CommRing

-- 环的基本结构
section RingStructure
variable {R : Type*} [Ring R]

-- 加法结构
example : AddMonoid R := by infer_instance

-- 乘法结构
example : Monoid R := by infer_instance

-- 分配律
example (a b c : R) : a * (b + c) = a * b + a * c := by
  rw [mul_add]

example (a b c : R) : (a + b) * c = a * c + b * c := by
  rw [add_mul]

-- 零乘性质
example (a : R) : 0 * a = 0 := by
  rw [zero_mul]

example (a : R) : a * 0 = 0 := by
  rw [mul_zero]

end RingStructure

/-! 
## 交换环与整环

交换环是乘法可交换的环。整环是无零因子的交换环。
-/

section CommutativeRing
variable {R : Type*} [CommRing R]

-- 乘法交换
example (a b : R) : a * b = b * a := by
  rw [mul_comm]

-- 整环定义：无零因子
#check IsDomain

-- 整数是整环
example : IsDomain ℤ := by
  infer_instance

end CommutativeRing

/-! 
## 理想

理想是环的加法子群，对环中任意元素的乘法封闭。
-/

section Ideals
variable {R : Type*} [CommRing R]

-- 理想定义
#check Ideal R

-- 主理想：由单个元素生成的理想
example (a : R) : Ideal R := Ideal.span {a}

-- 理想的性质
example (I : Ideal R) (a b : R) (ha : a ∈ I) (hb : b ∈ I) : a + b ∈ I := by
  apply I.add_mem
  · exact ha
  · exact hb

-- 理想吸收乘法
example (I : Ideal R) (a : R) (b ∈ I) : a * b ∈ I := by
  apply Ideal.mul_mem_left
  exact b

-- 素理想：如果ab ∈ P，则a ∈ P或b ∈ P
example (P : Ideal R) : P.IsPrime ↔ 
    P ≠ ⊤ ∧ ∀ {a b : R}, a * b ∈ P → a ∈ P ∨ b ∈ P := by
  rw [Ideal.isPrime_iff]

-- 极大理想
example (M : Ideal R) : M.IsMaximal ↔ 
    M ≠ ⊤ ∧ ∀ (I : Ideal R), M < I → I = ⊤ := by
  rw [Ideal.isMaximal_def]

end Ideals

/-! 
## 商环

通过理想构造商环。
-/

section QuotientRing
variable {R : Type*} [CommRing R] (I : Ideal R)

-- 商环定义
#check R ⧸ I

-- 商映射
example : R →+* R ⧸ I := Ideal.Quotient.mk I

-- 第一同构定理的环版本
example {S : Type*} [CommRing S] (f : R →+* S) :
    R ⧸ (RingHom.ker f) ≃+* f.range := by
  exact Ideal.quotientKerEquivRange f

-- 素理想 ↔ 商环是整环
example (P : Ideal R) : P.IsPrime ↔ IsDomain (R ⧸ P) := by
  rw [Ideal.isPrime_iff]
  constructor
  · intro h
    exact { __ := (Ideal.Quotient.commRing P), 
            __ := no_zero_divisors_of_prime P h.2 }
  · intro h
    constructor
    · rintro rfl
      have := h.1
      contradiction
    · exact fun h' => by simpa using h'

-- 极大理想 ↔ 商环是域
example (M : Ideal R) : M.IsMaximal ↔ IsField (R ⧸ M) := by
  rw [Ideal.isMaximal_iff]

end QuotientRing

/-! 
## 主理想环 (PID)

主理想环是所有理想都是主理想的整环。
-/

section PrincipalIdealDomain
variable {R : Type*} [CommRing R] [IsDomain R]

-- PID定义
#check IsPrincipalIdealRing

-- 整数是PID
example : IsPrincipalIdealRing ℤ := by
  infer_instance

-- 在PID中，素理想 = 极大理想（非零情况）
example [IsPrincipalIdealRing R] (P : Ideal R) [P.IsPrime] (hP : P ≠ ⊥) : 
    P.IsMaximal := by
  apply IsPrime.to_maximal_ideal
  exact hP

end PrincipalIdealDomain

/-! 
## 唯一分解整环 (UFD)

唯一分解整环中每个非零元素可以唯一地分解为不可约元的乘积。
-/

section UniqueFactorizationDomain
variable {R : Type*} [CommRing R] [IsDomain R]

-- UFD定义
#check UniqueFactorizationMonoid

-- 整数是UFD
example : UniqueFactorizationMonoid ℤ := by
  infer_instance

-- 多项式环在UFD上也是UFD（高斯引理）
variable [UniqueFactorizationMonoid R]

example : UniqueFactorizationMonoid R[X] := by
  infer_instance

-- 在UFD中，素元 = 不可约元
example {a : R} (ha : Prime a) : Irreducible a := by
  exact Prime.irreducible ha

end UniqueFactorizationDomain

/-! 
## 域

域是交换环，其中每个非零元素都有乘法逆元。
-/

section Fields
variable {F : Type*} [Field F]

-- 域的基本性质
example (a : F) (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  rw [mul_inv_cancel ha]

example (a : F) (ha : a ≠ 0) : a⁻¹ * a = 1 := by
  rw [inv_mul_cancel ha]

-- 域的非零元构成交换群
example : CommGroup (Units F) := by
  infer_instance

-- 域一定是整环
example : IsDomain F := by
  infer_instance

end Fields

/-! 
## 多项式环

多项式环是环论的重要例子。
-/

section PolynomialRing
variable {R : Type*} [CommRing R]

-- 多项式环 R[X]
example : Type _ := R[X]

-- 多项式是环
example : CommRing R[X] := by
  infer_instance

-- 多项式求值
example (p : R[X]) (a : R) : R := p.eval a

-- 根的定义
example (p : R[X]) (a : R) : Prop := IsRoot p a

-- 多项式除法（在域上）
variable {F : Type*} [Field F]

example (p d : F[X]) (hd : d ≠ 0) : 
    ∃ q r, p = q * d + r ∧ degree r < degree d := by
  apply EDivMonoid.edivmod_unique
  exact hd

end PolynomialRing

/-! 
## 示例：Z/nZ

模n剩余类环是环论的经典例子。
-/

section ZMod
variable (n : ℕ)

-- Z/nZ
example : Type _ := ZMod n

-- Z/nZ是环
example : CommRing (ZMod n) := by
  infer_instance

-- 当n是素数时，Z/nZ是域
example (hp : Nat.Prime n) : Field (ZMod n) := by
  have : Fact n.Prime := ⟨hp⟩
  infer_instance

-- Z/5Z是域
example : Field (ZMod 5) := by
  infer_instance

end ZMod

/-! 
## 练习

1. 证明：在交换环中，两个理想的和仍然是理想。
2. 证明：整数环ℤ中，由6和9生成的理想等于由3生成的理想。
3. 证明：在整环中，零理想是素理想。
4. 在多项式环ℝ[X]中，理想(X² + 1)是极大理想吗？为什么？
5. 证明：如果R是PID，那么R也是UFD（提示：使用Mathlib中的实例推导）。

-/ 

section Exercises
variable {R : Type*} [CommRing R]

-- 练习1：理想的和
example (I J : Ideal R) : Ideal R := I + J

-- 练习2：理想相等的证明（提示）
example : Ideal.span ({6, 9} : Set ℤ) = Ideal.span {3} := by
  apply Ideal.ext
  intro x
  simp [Ideal.mem_span_singleton, Ideal.mem_span_pair]
  constructor
  · rintro ⟨a, b, h⟩
    use 2 * a + 3 * b
    linarith
  · intro ⟨k, hk⟩
    use 0, k
    linarith

-- 练习4：(X² + 1)在ℝ[X]中不是极大理想（提示：考虑复数域）
-- 实际上(X² + 1)是极大理想，因为ℝ[X]/(X²+1) ≅ ℂ是域

end Exercises
