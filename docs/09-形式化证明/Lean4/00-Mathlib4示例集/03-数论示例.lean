import Mathlib.NumberTheory.Primes
import Mathlib.NumberTheory.Eulerian
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factors

/-! 
# 数论示例

对应的FormalMath文档：
- docs/06-数论/01-初等数论-增强版.md
- docs/06-数论/02-代数数论.md

对应的Mathlib4模块：
- Mathlib.NumberTheory.Primes
- Mathlib.NumberTheory.Eulerian
- Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
- Mathlib.NumberTheory.Padics.PadicNumbers
- Mathlib.NumberTheory.NumberField.Basic
- Mathlib.Data.ZMod.Basic

## 核心定义
-/ 

/-! 
## 素数

素数是大于1的自然数，除了1和它本身外没有其他正因数。
-/

section Primes

-- 素数定义
#check Nat.Prime

-- 素数判定
example : Nat.Prime 7 := by
  norm_num

example : Nat.Prime 13 := by
  norm_num

-- 合数判定
example : ¬ Nat.Prime 10 := by
  norm_num

-- 欧几里得定理：素数无穷多
example : {p : ℕ | Nat.Prime p}.Infinite := by
  apply Nat.infinite_setOf_prime

-- 素数的基本性质
example (p : ℕ) (hp : Nat.Prime p) : p ≥ 2 := by
  exact Nat.Prime.two_le hp

example (p : ℕ) (hp : Nat.Prime p) {a b : ℕ} (hab : p ∣ a * b) : 
    p ∣ a ∨ p ∣ b := by
  exact (Nat.Prime.dvd_mul hp).mp hab

end Primes

/-! 
## 同余

同余是数论中的核心概念。
-/

section Congruence

-- 同余记号
example (a b n : ℕ) : Prop := a ≡ b [MOD n]

-- 同余的基本性质
example (a n : ℕ) : a ≡ a [MOD n] := by
  rfl

example (a b n : ℕ) (h : a ≡ b [MOD n]) : b ≡ a [MOD n] := by
  exact h.symm

example (a b c n : ℕ) (h1 : a ≡ b [MOD n]) (h2 : b ≡ c [MOD n]) : 
    a ≡ c [MOD n] := by
  exact h1.trans h2

-- 同余与算术运算
example (a b c d n : ℕ) (h1 : a ≡ b [MOD n]) (h2 : c ≡ d [MOD n]) : 
    a + c ≡ b + d [MOD n] := by
  exact Nat.ModEq.add h1 h2

example (a b c d n : ℕ) (h1 : a ≡ b [MOD n]) (h2 : c ≡ d [MOD n]) : 
    a * c ≡ b * d [MOD n] := by
  exact Nat.ModEq.mul h1 h2

-- ZMod n：模n剩余类
example (n : ℕ) : Type _ := ZMod n

-- ZMod n是环
example (n : ℕ) : CommRing (ZMod n) := by
  infer_instance

-- ZMod p是域（当p是素数时）
example (p : ℕ) [Fact p.Prime] : Field (ZMod p) := by
  infer_instance

end Congruence

/-! 
## 欧拉函数

欧拉函数φ(n)表示1到n中与n互质的整数的个数。
-/

section EulerTotient

-- 欧拉函数
#check Nat.totient

-- 计算欧拉函数
example : Nat.totient 10 = 4 := by
  norm_num [Nat.totient]

example : Nat.totient 12 = 4 := by
  norm_num [Nat.totient]

-- 欧拉定理：a^φ(n) ≡ 1 (mod n)（当gcd(a,n)=1时）
example (a n : ℕ) (ha : a.Coprime n) : 
    a ^ Nat.totient n ≡ 1 [MOD n] := by
  exact Nat.ModEq.pow_totient ha

-- 费马小定理：a^(p-1) ≡ 1 (mod p)（当p是素数且p不整除a时）
example (a p : ℕ) (hp : Nat.Prime p) (hpa : ¬ p ∣ a) : 
    a ^ (p - 1) ≡ 1 [MOD p] := by
  have h : a.Coprime p := by
    exact (Nat.coprime_comm).mpr (Nat.Prime.coprime_iff_not_dvd hp).mpr hpa
  apply Nat.ModEq.pow_totient
  exact h

-- 积性函数性质
example (m n : ℕ) (hmn : m.Coprime n) : 
    Nat.totient (m * n) = Nat.totient m * Nat.totient n := by
  rw [Nat.totient_mul]
  exact hmn

-- 素数幂的欧拉函数
example (p k : ℕ) (hp : Nat.Prime p) : 
    Nat.totient (p ^ k) = p ^ (k - 1) * (p - 1) := by
  rw [Nat.totient_prime_pow]
  · ring
  · exact hp
  · simp

end EulerTotient

/-! 
## 二次剩余与二次互反律

二次互反律是数论的皇冠明珠。
-/

section QuadraticReciprocity

-- Legendre符号
#check legendreSym

-- Legendre符号定义
example (p : ℕ) [Fact p.Prime] (a : ℤ) : ℤ := legendreSym p a

-- Legendre符号性质
example (p : ℕ) [Fact p.Prime] (a : ℤ) : 
    legendreSym p a = 1 ↔ IsSquare (a : ZMod p) ∧ (a : ZMod p) ≠ 0 := by
  rw [legendreSym.eq_one_iff]
  · rfl
  · intro h
    have := (ZMod.eq_iff_modEq_nat p).mp h
    simp at this
    -- 处理零情况
    all_goals omega

-- 二次互反律
example (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hp : p ≠ 2) (hq : q ≠ 2) 
    (hpq : p ≠ q) :
    legendreSym p q * legendreSym q p = (-1) ^ ((p - 1) / 2 * (q - 1) / 2) := by
  rw [quadratic_reciprocity']
  all_goals omega

-- 补充法则1：(-1/p) = (-1)^((p-1)/2)
example (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p (-1 : ℤ) = (-1) ^ ((p - 1) / 2) := by
  rw [legendreSym.at_neg_one]
  rfl

-- 补充法则2：(2/p) = (-1)^((p²-1)/8)
example (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p (2 : ℤ) = (-1) ^ ((p ^ 2 - 1) / 8) := by
  rw [legendreSym.two]
  rfl

end QuadraticReciprocity

/-! 
## p进数

p进数是数论中重要的完备化。
-/

section PAdicNumbers

-- p进数域
#check Padic

-- p进整数
#check PadicInt

-- p进数的完备性
example (p : ℕ) [Fact p.Prime] : CompleteSpace (Padic p) := by
  infer_instance

-- p进绝对值
example (p : ℕ) [Fact p.Prime] : Padic p → ℚ := Padic.norm

end PAdicNumbers

/-! 
## 代数数论

代数数域和代数整数。
-/

section AlgebraicNumberTheory

-- 数域
#check NumberField

-- 代数整数环
#check RingOfIntegers

-- 数域的判别式
#check NumberField.discr

-- 类数
#check NumberField.classNumber

end AlgebraicNumberTheory

/-! 
## 整除与因数分解

整除性质和唯一分解定理。
-/

section Divisibility

-- 整除
example (a b : ℕ) : Prop := a ∣ b

-- 最大公约数
example (a b : ℕ) : ℕ := a.gcd b

-- 最小公倍数
example (a b : ℕ) : ℕ := a.lcm b

-- Bézout恒等式
example (a b : ℕ) : 
    ∃ x y : ℤ, (a : ℤ) * x + (b : ℤ) * y = (a.gcd b : ℤ) := by
  exact Int.gcd_eq_gcd_ab a b

-- 素因数分解
example (n : ℕ) : n.primeFactorsList ~ n.primeFactorsList := by
  rfl

-- 唯一分解定理
example (n : ℕ) : n.factorization.prod (· ^ ·) = n := by
  exact Nat.factorization_prod_pow_eq_self (by linarith)

end Divisibility

/-! 
## 示例：RSA加密基础

数论在现代密码学中有重要应用。
-/

section RSACryptography

-- RSA密钥生成的基础：φ(pq) = (p-1)(q-1)
example (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) : 
    Nat.totient (p * q) = (p - 1) * (q - 1) := by
  rw [Nat.totient_mul]
  · rw [Nat.totient_prime hp, Nat.totient_prime hq]
  · exact (Nat.coprime_primes hp hq).mpr hpq

-- RSA解密正确性的关键：ed ≡ 1 (mod φ(n))
example (e d n : ℕ) (h : e * d ≡ 1 [MOD Nat.totient n]) (a : ℕ) 
    (ha : a.Coprime n) : 
    a ^ (e * d) ≡ a [MOD n] := by
  calc
    a ^ (e * d) ≡ a ^ 1 [MOD n] := by
      apply Nat.ModEq.pow
      exact h
    _ ≡ a [MOD n] := by simp

end RSACryptography

/-! 
## 练习

1. 证明：如果p是素数，那么(p-1)! ≡ -1 (mod p)（Wilson定理）。
2. 计算Legendre符号 (7/11) 和 (11/7)，验证二次互反律。
3. 证明：对于任意正整数n，Σ_{d|n} φ(d) = n。
4. 证明：如果a ≡ b (mod m) 且 a ≡ b (mod n)，且gcd(m,n)=1，则 a ≡ b (mod mn)。
5. 找出所有满足 φ(n) = 8 的正整数n。

-/ 

section Exercises

-- 练习2的提示：使用quadratic_reciprocity
example : legendreSym 7 11 * legendreSym 11 7 = (-1) ^ ((7 - 1) / 2 * (11 - 1) / 2) := by
  have hp : Fact 7.Prime := ⟨by norm_num⟩
  have hq : Fact 11.Prime := ⟨by norm_num⟩
  rw [quadratic_reciprocity']
  all_goals omega

-- 练习4的提示：使用中国剩余定理的思想
example (a b m n : ℕ) (h1 : a ≡ b [MOD m]) (h2 : a ≡ b [MOD n]) 
    (hmn : m.Coprime n) : a ≡ b [MOD m * n] := by
  exact Nat.ModEq.mul_right' hmn h1 h2

end Exercises
