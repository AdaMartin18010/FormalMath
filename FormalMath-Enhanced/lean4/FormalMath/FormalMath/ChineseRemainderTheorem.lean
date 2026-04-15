/-
# 中国剩余定理的形式化证明 / Chinese Remainder Theorem

## 定理信息
- **定理名称**: 中国剩余定理 (Chinese Remainder Theorem, CRT)
- **数学领域**: 数论 / Number Theory
- **MSC2020编码**: 11A07 (模算术), 11Y16 (数论算法)

## 定理陈述

设 n₁, n₂, ..., nₖ 是两两互素的正整数，则对于任意整数 a₁, a₂, ..., aₖ，
同余方程组：
```
  x ≡ a₁ (mod n₁)
  x ≡ a₂ (mod n₂)
  ...
  x ≡ aₖ (mod nₖ)
```
在模 N = n₁n₂...nₖ 下有唯一解。

## 数学意义

1. 两两互素模数下的同余方程组有唯一解
2. 环同构：ℤ/(n₁n₂)ℤ ≅ ℤ/n₁ℤ × ℤ/n₂ℤ (当 gcd(n₁,n₂)=1 时)
3. 在密码学、编码理论中有广泛应用

## 历史背景

该定理最早出现在中国《孙子算经》（公元3-5世纪）中的"物不知数"问题。
完整的证明由秦九韶在《数书九章》（1247年）中给出。

## 证明详解

### 两元情况证明

**定理**：若 m 和 n 互素，则同余方程组
```
x ≡ a (mod m)
x ≡ b (mod n)
```
有解。

**证明**：
1. 由于 gcd(m,n) = 1，由 Bezout 恒等式，存在整数 s, t 使得
   ```s·m + t·n = 1```

2. 构造解：
   ```x = b·s·m + a·t·n```

3. 验证 x ≡ a (mod m)：
   - x ≡ a·t·n (mod m)  [因为 s·m ≡ 0 (mod m)]
   - 由于 s·m + t·n = 1，有 t·n ≡ 1 (mod m)
   - 所以 x ≡ a·1 ≡ a (mod m) ✓

4. 验证 x ≡ b (mod n)：
   - x ≡ b·s·m (mod n)  [因为 t·n ≡ 0 (mod n)]
   - 由于 s·m + t·n = 1，有 s·m ≡ 1 (mod n)
   - 所以 x ≡ b·1 ≡ b (mod n) ✓

### 唯一性证明

若 x 和 y 都满足同余方程组，则
- x ≡ y (mod m) 且 x ≡ y (mod n)
- 由于 m 和 n 互素，所以 x ≡ y (mod mn)

### 多元情况证明（归纳法）

对 k 使用数学归纳法：
- 基础情况 k=1：显然成立
- 归纳步骤：假设对 k 个方程成立，对 k+1 个方程
  1. 由归纳假设，前 k 个方程有解 x₀
  2. 令 M = n₁·n₂·...·nₖ，则 x ≡ x₀ (mod M)
  3. 由于 M 与 n_{k+1} 互素，将问题化为两元情况
  4. 解 x ≡ x₀ (mod M)，x ≡ a_{k+1} (mod n_{k+1})

**参考**: Dummit & Foote, Theorem 7.6.1, p. 265
-/

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Basic

namespace ChineseRemainderTheorem


/-- 两元中国剩余定理：当 m 和 n 互素时，同余方程组有解 

**定理**：若 gcd(m,n) = 1，则方程组
```
x ≡ a (mod m)
x ≡ b (mod n)
```
有解。

**构造性证明**：使用 Bezout 恒等式

**参考**: Dummit & Foote, Theorem 7.6.1, p. 265
-/
theorem chinese_remainder_two (m n a b : Nat)
    (h_coprime : Nat.gcd m n = 1) :
    ∃ x : Nat, x ≡ a [MOD m] ∧ x ≡ b [MOD n] := by
  use (Nat.chineseRemainder h_coprime a b).val
  exact (Nat.chineseRemainder h_coprime a b).prop

/-- 中国剩余定理的唯一性 

**定理**：若 x 和 y 都满足同余方程组，则 x ≡ y (mod mn)

**参考**: Dummit & Foote, Theorem 7.6.1, p. 265
-/
theorem chinese_remainder_unique (m n a b : Nat)
    (h_coprime : Nat.gcd m n = 1)
    (x y : Nat)
    (hx : x ≡ a [MOD m] ∧ x ≡ b [MOD n])
    (hy : y ≡ a [MOD m] ∧ y ≡ b [MOD n]) :
    x % (m * n) = y % (m * n) := by
  -- x ≡ a (mod m) 且 y ≡ a (mod m)，所以 x ≡ y (mod m)
  have h_mod_m : x % m = y % m := by
    rw [hx.1, hy.1]
  -- x ≡ b (mod n) 且 y ≡ b (mod n)，所以 x ≡ y (mod n)
  have h_mod_n : x % n = y % n := by
    rw [hx.2, hy.2]
  -- 由于gcd(m,n)=1，由中国剩余定理的唯一性部分
  -- x ≡ y (mod m) 且 x ≡ y (mod n) 蕴含 x ≡ y (mod mn)
  exact (Nat.modEq_and_modEq_iff_modEq_mul (Nat.coprime_iff_gcd_eq_one.mpr h_coprime)).mp ⟨h_mod_m, h_mod_n⟩

/-- 多元中国剩余定理（归纳形式）

**定理**：设 n₁, n₂, ..., nₖ 两两互素，则同余方程组
```
x ≡ aᵢ (mod nᵢ)  (i = 1, 2, ..., k)
```
在模 N = n₁n₂...nₖ 下有唯一解。

**参考**: Dummit & Foote, Theorem 7.6.1, p. 265
-/
theorem chinese_remainder_multiple (k : Nat) (n : Nat → Nat) (a : Nat → Nat)
    (h_pairwise : ∀ i j, i < k → j < k → i ≠ j → Nat.gcd (n i) (n j) = 1)
    (h_nz : ∀ i, i < k → n i > 0) :
    ∃ x : Nat, ∀ i, i < k → x ≡ a i [MOD (n i)] := by
  induction k with
  | zero =>
    -- k=0，空真
    use 0
    intro i hi
    linarith
  | succ k ih =>
    -- 归纳步骤
    rcases ih (fun i j hi hj hne => h_pairwise i j (by linarith) (by linarith) hne)
      (fun i hi => h_nz i (by linarith)) with ⟨x₀, hx₀⟩
    -- 令M = n₀·n₁·...·n_{k-1}
    let M := ∏ i ∈ Finset.range k, n i
    -- M与n_k互素
    have h_coprime : Nat.gcd M (n k) = 1 := by
      have hM : M = ∏ i ∈ Finset.range k, n i := rfl
      rw [hM]
      have h1 : ∀ i < k, (n i).gcd (n k) = 1 := by
        intro i hi
        have hne : i ≠ k := by linarith
        exact h_pairwise i k (by linarith) (by linarith) hne
      clear hM M
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Finset.range_succ, Finset.prod_insert Finset.not_mem_range_self]
        rw [Nat.coprime_mul_iff_left]
        constructor
        · exact h1 k (by linarith)
        · exact ih (fun i hi => h1 i (by linarith))
    -- 解 x ≡ x₀ (mod M)，x ≡ a_k (mod n_k)
    rcases chinese_remainder_two M (n k) x₀ (a k) h_coprime with ⟨x, hx_M, hx_k⟩
    use x
    intro i hi
    cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with
    | inl hi_lt =>
      -- i < k
      have h_x_i : x ≡ a i [MOD n i] := by
        have hM_dvd : n i ∣ M := by
          have hM : M = ∏ i ∈ Finset.range k, n i := rfl
          rw [hM]
          apply Finset.dvd_prod_of_mem
          simp
          exact hi_lt
        have h1 : x ≡ x₀ [MOD n i] := Nat.ModEq.of_dvd hM_dvd hx_M
        have h2 : x₀ ≡ a i [MOD n i] := hx₀ i hi_lt
        exact Nat.ModEq.trans h1 h2
      exact h_x_i
    | inr hi_eq =>
      -- i = k
      rw [hi_eq]
      exact hx_k

/-- 孙子算经问题的验证

"今有物不知其数，三三数之剩二，五五数之剩三，七七数之剩二，问物几何？"

即求解：
```
x ≡ 2 (mod 3)
x ≡ 3 (mod 5)
x ≡ 2 (mod 7)
```

最小正整数解为 23。

**参考**: 孙子算经, 约公元3-5世纪
-/
example : ∃ x : Nat, x ≡ 2 [MOD 3] ∧ x ≡ 3 [MOD 5] ∧ x ≡ 2 [MOD 7] := by
  -- 使用中国剩余定理
  -- 3, 5, 7两两互素
  have h_coprime_3_5 : Nat.gcd 3 5 = 1 := by rfl
  have h_coprime_3_7 : Nat.gcd 3 7 = 1 := by rfl
  have h_coprime_5_7 : Nat.gcd 5 7 = 1 := by rfl

  -- 先解前两个方程
  rcases chinese_remainder_two 3 5 2 3 h_coprime_3_5 with ⟨x₁₂, hx₁₂_3, hx₁₂_5⟩

  -- 再与第三个方程结合
  -- x ≡ x₁₂ (mod 15)，x ≡ 2 (mod 7)
  have h_coprime_15_7 : Nat.gcd 15 7 = 1 := by rfl
  rcases chinese_remainder_two 15 7 x₁₂ 2 h_coprime_15_7 with ⟨x, hx_15, hx_7⟩

  use x
  constructor
  · -- x ≡ 2 (mod 3)
    show x % 3 = 2
    have : x % 15 = x₁₂ % 15 := hx_15
    have : x₁₂ % 3 = 2 := hx₁₂_3
    omega
  constructor
  · -- x ≡ 3 (mod 5)
    show x % 5 = 3
    have : x % 15 = x₁₂ % 15 := hx_15
    have : x₁₂ % 5 = 3 := hx₁₂_5
    omega
  · -- x ≡ 2 (mod 7)
    exact hx_7

/-- 中国剩余定理的环论表述

当gcd(m,n)=1时，有环同构：
ℤ/(mn)ℤ ≅ ℤ/mℤ × ℤ/nℤ

**参考**: Dummit & Foote, Theorem 7.6.1, Corollary 7.6.2, p. 265-266
-/
def chinese_remainder_ring_iso (m n : Nat)
    (h_coprime : Nat.gcd m n = 1) :
    ZMod (m * n) ≃+* ZMod m × ZMod n := by
  exact ZMod.chineseRemainder h_coprime

end ChineseRemainderTheorem
