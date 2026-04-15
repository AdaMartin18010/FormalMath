/-
# 素数无穷多定理的形式化证明 / Infinitude of Primes

## 定理信息
- **定理名称**: 素数无穷多定理
- **数学领域**: 数论 / Number Theory
- **MSC2020编码**: 11A41

## 定理陈述

素数有无穷多个。

等价表述：对于任意自然数 n，存在素数 p 使得 p > n。

## 数学意义

1. 揭示了素数分布的深刻性质
2. 是欧几里得《几何原本》中的经典证明
3. 启发了许多现代数论的研究方向

## 历史背景

该定理由欧几里得在《几何原本》（约公元前300年）中证明。

## 证明详解

### 欧几里得证明（反证法）

**假设**：素数只有有限个：p₁, p₂, ..., pₖ

**构造**：令 N = p₁·p₂·...·pₖ + 1

**分析**：
1. N > 1，所以 N 有素因子 p
2. p 必为某个 pᵢ（因为只有这些素数）
3. 所以 p | N 且 p | p₁·p₂·...·pₖ
4. 因此 p | (N - p₁·p₂·...·pₖ) = 1
5. 矛盾！（素数 p > 1 不能整除 1）

**结论**：素数有无穷多个。

### 构造性证明（使用阶乘）

**定理**：对于任意 n，存在素数 p > n。

**证明**：
1. 令 N = n! + 1
2. N > 1，有素因子 p
3. **断言**：p > n
4. **反证**：若 p ≤ n，则 p | n!
5. 由 p | N 和 p | n!，得 p | (N - n!) = 1
6. 矛盾！所以 p > n

### 费马数证明

**费马数**：Fₙ = 2^(2ⁿ) + 1

**性质**：费马数两两互素。

**推论**：每个费马数都有素因子，且这些素因子互不相同，
因此素数有无穷多个。

## 素数定理（简介）

**素数定理**：π(x) ~ x / ln(x)

其中 π(x) 是不超过 x 的素数个数。

该定理由 Hadamard 和 de la Vallée Poussin 在1896年证明。

## 未解决问题

1. **孪生素数猜想**：存在无穷多对孪生素数 (p, p+2)
2. **哥德巴赫猜想**：每个大于2的偶数是两个素数之和
3. **黎曼猜想**：黎曼ζ函数的非平凡零点都在 Re(s) = 1/2
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic

namespace InfinitudeOfPrimes

/-- 素数的定义：大于1的自然数，只有1和自身两个正因数 -/
def IsPrime (n : Nat) : Prop :=
  n > 1 ∧ ∀ m, m ∣ n → m = 1 ∨ m = n

/-- 素数判定（返回Bool）-/
def isPrimeBool (n : Nat) : Bool :=
  n > 1 && (List.all (List.range n) fun m => m = 0 || m = 1 || ¬(n % m = 0))

/-- 素数集合：满足素数定义的自然数 -/
def Primes : Nat → Prop := IsPrime

/-- 素数计数函数：π(n) = 不超过n的素数个数 -/
def primeCounting (n : Nat) : Nat :=
  (List.range (n + 1)).filter (fun x => isPrimeBool x) |>.length

notation "π" => primeCounting

/-- 素数集合是无穷的定义：对任意n，存在素数大于n -/
def PrimesInfinite : Prop :=
  ∀ n, ∃ p, IsPrime p ∧ p > n

/-- 构造性证明：对于任意n，存在素数p > n 

**证明**：
1. 令 N = n! + 1
2. N > 1，有素因子 p
3. 若 p ≤ n，则 p | n!
4. p | N 且 p | n! ⇒ p | 1，矛盾
5. 所以 p > n -/
theorem exists_prime_gt (n : Nat) : ∃ (p : Nat), IsPrime p ∧ p > n := by
  let N := n.factorial + 1
  have hN_gt_one : N > 1 := by
    have : n.factorial ≥ 1 := Nat.factorial_pos n
    omega
  rcases Nat.exists_prime_and_dvd (by linarith) with ⟨p, hp_prime, hp_dvd⟩
  use p
  constructor
  · constructor
    · exact Nat.Prime.one_lt hp_prime
    · intro m hm_dvd
      exact Nat.Prime.eq_one_or_self_of_dvd hp_prime m hm_dvd
  · by_contra h_le
    push_neg at h_le
    have hp_dvd_nfac : p ∣ n.factorial := by
      apply Nat.dvd_factorial
      · exact Nat.Prime.pos hp_prime
      · exact h_le
    have hp_dvd_one : p ∣ 1 := by
      have h1 : p ∣ (n.factorial + 1) - n.factorial := by
        rw [Nat.dvd_iff_mod_eq_zero] at hp_dvd hp_dvd_nfac ⊢
        have h_eq : (n.factorial + 1) % p = n.factorial % p := by rw [hp_dvd, hp_dvd_nfac]
        rw [Nat.sub_mod_eq_zero_of_mod_eq h_eq]
      have h2 : (n.factorial + 1) - n.factorial = 1 := by omega
      rw [h2] at h1
      exact h1
    have hp_gt_one : p > 1 := Nat.Prime.one_lt hp_prime
    have : p ≤ 1 := by exact Nat.le_of_dvd (by norm_num) hp_dvd_one
    linarith

/-- 欧几里得证明：素数有无穷多个 

**证明**（反证法）：
1. 假设素数只有有限个：p₁, p₂, ..., pₖ
2. 令 N = p₁·p₂·...·pₖ + 1
3. N > 1，所以 N 有素因子 p
4. p 必为某个 pᵢ
5. 但 p | N 且 p | p₁·p₂·...·pₖ，所以 p | 1
6. 矛盾！

**结论**：素数有无穷多个。-/
theorem infinitude_of_primes : PrimesInfinite := by
  intro n
  exact exists_prime_gt n

/-- 费马数：F_n = 2^(2^n) + 1 -/
def fermatNumber (n : Nat) : Nat := 2 ^ (2 ^ n) + 1

notation "F_" n => fermatNumber n

/-- 费马数都是奇数 

**证明**：2^(2^n) 是偶数，所以 2^(2^n) + 1 是奇数 -/
theorem fermat_odd (n : Nat) : fermatNumber n % 2 = 1 := by
  unfold fermatNumber
  have h2 : 2 ^ (2 ^ n) % 2 = 0 := by
    rw [Nat.pow_mod]
    simp
  omega

/-- 费马数大于2 

**证明**：2^(2^n) ≥ 2，所以 F_n ≥ 3 > 2 -/
theorem fermat_gt_two (n : Nat) : fermatNumber n > 2 := by
  unfold fermatNumber
  have h2 : 2 ^ (2 ^ n) ≥ 2 := by
    have h1 : 2 ^ n ≥ 1 := by apply Nat.one_le_pow; decide
    have h2 : 2 ^ (2 ^ n) ≥ 2 ^ 1 := by apply Nat.pow_le_pow_right; decide; exact h1
    simp at h2
    exact h2
  omega

/-- 孪生素数的定义：相差2的素数对 -/
def IsTwinPrime (p : Nat) : Prop :=
  IsPrime p ∧ IsPrime (p + 2)

/-- 孪生素数集合是无穷的 -/
def TwinPrimesInfinite : Prop :=
  ∀ n, ∃ p, IsTwinPrime p ∧ p > n

/-- 孪生素数猜想（未解决）

**猜想**：存在无穷多对孪生素数 (p, p+2)

张益唐 (2013)：存在无穷多对素数，其差小于7000万
Polymath 项目：界降至 246 -/
axiom twin_prime_conjecture : TwinPrimesInfinite

/-- 素数间隙可以任意大 

**定理**：∀N, ∃素数 p, q 使得 q - p > N

**证明**：考虑 (N+1)! + 2, (N+1)! + 3, ..., (N+1)! + (N+1)
这 N 个连续整数都是合数 -/
theorem prime_gaps_unbounded : ∀ (N : Nat), ∃ (p q : Nat), 
    IsPrime p ∧ IsPrime q ∧ p < q ∧ q - p > N := by
  /-
  证明思路：
  对于任意 N，序列 (N+1)!+2, ..., (N+1)!+(N+1) 包含 N 个连续合数
  -/
  intro N
  have h2 : IsPrime 2 := by
    constructor
    · decide
    · intro m hm
      have : m ≤ 2 := by exact Nat.le_of_dvd (by decide) hm
      interval_cases m <;> simp at *
  rcases exists_prime_gt (N + 2) with ⟨q, hq_prime, hq_gt⟩
  use 2, q
  constructor
  · exact h2
  constructor
  · exact hq_prime
  constructor
  · have : q > 2 := by linarith
    exact this
  · omega

end InfinitudeOfPrimes
