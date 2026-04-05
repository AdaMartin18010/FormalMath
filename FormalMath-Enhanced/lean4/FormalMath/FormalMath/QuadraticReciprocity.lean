/-
# 二次互反律 (Quadratic Reciprocity)

## 数学背景

二次互反律是数论中最优美的定理之一，由高斯首次严格证明。
它描述了不同素数模下二次剩余的相互关系。

## 基本概念

- **Legendre符号**: (a/p) = 
  * 1  若 a 是模 p 的二次剩余且 p ∤ a
  * -1 若 a 是模 p 的二次非剩余
  * 0  若 p | a

## 二次互反律陈述

对于不同的奇素数 p 和 q：
(p/q)(q/p) = (-1)^{((p-1)/2)((q-1)/2)}

等价表述：
- 若 p ≡ 1 (mod 4) 或 q ≡ 1 (mod 4)，则 (p/q) = (q/p)
- 若 p ≡ q ≡ 3 (mod 4)，则 (p/q) = -(q/p)

## 补充法则

1. **(-1/p) = (-1)^{(p-1)/2}**
   - (-1/p) = 1  当 p ≡ 1 (mod 4)
   - (-1/p) = -1 当 p ≡ 3 (mod 4)

2. **(2/p) = (-1)^{(p²-1)/8}**
   - (2/p) = 1  当 p ≡ ±1 (mod 8)
   - (2/p) = -1 当 p ≡ ±3 (mod 8)

## 应用

- 判断二次同余方程的可解性
- 计算Legendre符号
- 数论中的基本工具

## Mathlib4对应
- `Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity`

本文件建立二次互反律及其应用。
-/

import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Data.ZMod.Basic

namespace QuadraticReciprocity

open Nat Real

/-
## Legendre符号的定义

**定义**：对于奇素数 p 和整数 a，Legendre符号 (a/p) 定义为：

(a/p) = ⎧ 1   若 ∃x, x² ≡ a (mod p) 且 p ∤ a
        ⎨-1   若 ¬∃x, x² ≡ a (mod p)
        ⎩ 0   若 p | a

**数学意义**：Legendre符号提供了一种简洁的方式
来判断二次同余方程 x² ≡ a (mod p) 是否有解。
-/

/-- Legendre符号（使用Mathlib定义） -/
def legendreSymbol (p : ℕ) (hp : p.Prime) (a : ℤ) : ℤ :=
  @LegendreSymbol.legendreSym p (fact_iff.2 hp) a

notation:max "( " a " / " p " )" => legendreSymbol p (by apply_assumption) a

/-
## Legendre符号的基本性质

**性质1**：(a²/p) = 1，若 p ∤ a

**证明**：显然，x = a 就是 x² ≡ a² (mod p) 的解。
-/
theorem legendre_symbol_square (p : ℕ) (hp : p.Prime) (hp_odd : p > 2) (a : ℤ)
    (hpa : ¬(p : ℤ) ∣ a) : legendreSymbol p hp (a ^ 2) = 1 := by
  -- 利用Mathlib中的定理
  apply LegendreSymbol.sq_one_of_not_dvd
  exact hpa

/-
## 欧拉判别法

**定理**：(a/p) ≡ a^{(p-1)/2} (mod p)

这是计算Legendre符号的重要工具。

**证明**：
- 若 (a/p) = 1，则 ∃x, x² ≡ a (mod p)
  因此 a^{(p-1)/2} ≡ x^{p-1} ≡ 1 (mod p)（由Fermat小定理）
  
- 若 (a/p) = -1，考虑乘法群 (ℤ/pℤ)^×
  将元素配对 {x, ax^{-1}}，每组乘积为 a
  共有 (p-1)/2 组，因此全体乘积 ≡ a^{(p-1)/2} (mod p)
  但由Wilson定理，全体乘积 ≡ -1 (mod p)
-/
theorem euler_criterion (p : ℕ) (hp : p.Prime) (hp_odd : p > 2) (a : ℤ) :
    (legendreSymbol p hp a : ZMod p) = (a : ZMod p) ^ ((p - 1) / 2) := by
  -- 这是Mathlib中已证明的欧拉判别法
  apply LegendreSymbol.euler_criterion

/-
## 第一补充法则：(-1/p)

**定理**：(-1/p) = (-1)^{(p-1)/2}

等价表述：
- 若 p ≡ 1 (mod 4)，则 (-1/p) = 1
- 若 p ≡ 3 (mod 4)，则 (-1/p) = -1

**证明**：
由欧拉判别法，(-1/p) ≡ (-1)^{(p-1)/2} (mod p)

由于两边都是 ±1，且 p > 2，因此等式成立。
-/
theorem first_supplement (p : ℕ) (hp : p.Prime) (hp_odd : p > 2) :
    legendreSymbol p hp (-1) = (-1 : ℤ) ^ ((p - 1) / 2) := by
  -- 利用欧拉判别法和(-1)^{(p-1)/2}的性质
  rw [← Int.cast_inj (R := ZMod p)]
  have h1 : ((legendreSymbol p hp (-1) : ℤ) : ZMod p) = (-1 : ZMod p) ^ ((p - 1) / 2) := by
    apply LegendreSymbol.euler_criterion
  have h2 : (((-1 : ℤ) ^ ((p - 1) / 2) : ℤ) : ZMod p) = (-1 : ZMod p) ^ ((p - 1) / 2) := by simp
  rw [h1, h2]
  -- 两边在ZMod p中相等意味着整数相等（因为两边都是±1）
  have h3 : (-1 : ℤ) ^ ((p - 1) / 2) = 1 ∨ (-1 : ℤ) ^ ((p - 1) / 2) = -1 := by
    apply neg_one_pow_eq_or
  rcases h3 with h3 | h3
  · -- 偶数情况
    rw [h3]
    have : (-1 : ZMod p) ^ ((p - 1) / 2) = 1 := by
      rw [← h2, h3]
      simp
    rw [this]
    simp [h3]
  · -- 奇数情况
    rw [h3]
    have : (-1 : ZMod p) ^ ((p - 1) / 2) = -1 := by
      rw [← h2, h3]
      simp
    rw [this]
    simp [h3]

/-- 用模4分类表述第一补充法则 -/
theorem first_supplement_mod4 (p : ℕ) (hp : p.Prime) (hp_odd : p > 2) :
    (p % 4 = 1 → legendreSymbol p hp (-1) = 1) ∧
    (p % 4 = 3 → legendreSymbol p hp (-1) = -1) := by
  constructor
  · intro hp1
    -- p ≡ 1 (mod 4) 意味着 (p-1)/2 是偶数
    have h_even : ((p - 1) / 2) % 2 = 0 := by
      have h_p_mod_4 : p % 4 = 1 := hp1
      have h_p_eq : ∃ k, p = 4 * k + 1 := by
        refine ⟨p / 4, by omega⟩
      rcases h_p_eq with ⟨k, hk⟩
      rw [hk]
      ring_nf
      omega
    -- (-1)^{偶数} = 1
    have h_power : (-1 : ℤ) ^ ((p - 1) / 2) = 1 := by
      have h_even_exp : ∃ m, (p - 1) / 2 = 2 * m := by
        refine ⟨(p - 1) / 4, by omega⟩
      rcases h_even_exp with ⟨m, hm⟩
      rw [hm]
      rw [pow_mul]
      simp
    rw [first_supplement p hp hp_odd, h_power]
  · intro hp3
    -- p ≡ 3 (mod 4) 意味着 (p-1)/2 是奇数
    have h_odd : ((p - 1) / 2) % 2 = 1 := by
      have h_p_mod_4 : p % 4 = 3 := hp3
      have h_p_eq : ∃ k, p = 4 * k + 3 := by
        refine ⟨(p - 3) / 4, by omega⟩
      rcases h_p_eq with ⟨k, hk⟩
      rw [hk]
      ring_nf
      omega
    -- (-1)^{奇数} = -1
    have h_power : (-1 : ℤ) ^ ((p - 1) / 2) = -1 := by
      have h1 : ((p - 1) / 2) = 2 * ((p - 1) / 4) + 1 := by
        have h_p_mod_4 : p % 4 = 3 := hp3
        omega
      rw [h1]
      rw [pow_add, pow_mul]
      norm_num
    rw [first_supplement p hp hp_odd, h_power]

/-
## 第二补充法则：(2/p)

**定理**：(2/p) = (-1)^{(p²-1)/8}

等价表述：
- 若 p ≡ ±1 (mod 8)，则 (2/p) = 1
- 若 p ≡ ±3 (mod 8)，则 (2/p) = -1

**证明概要**（高斯引理）：
考虑 2, 4, 6, ..., p-1（即 2·1, 2·2, ..., 2·(p-1)/2）
模 p 的最小正剩余。设其中有 n 个大于 (p-1)/2，则 (2/p) = (-1)^n。

计算 n 的值，可以证明 n ≡ (p²-1)/8 (mod 2)。
-/
theorem second_supplement (p : ℕ) (hp : p.Prime) (hp_odd : p > 2) :
    legendreSymbol p hp 2 = (-1 : ℤ) ^ ((p ^ 2 - 1) / 8) := by
  -- 利用Mathlib中的定理
  have h : legendreSymbol p hp 2 = χ₈ p := by
    rw [legendreSymbol]
    exact LegendreSymbol.legendreSym.at_two (fact_iff.2 hp)
  rw [h]
  -- χ₈ p = (-1)^{(p²-1)/8}
  have h2 : χ₈ p = (-1 : ℤ) ^ ((p ^ 2 - 1) / 8) := by
    simp [χ₈, χ₈', Int.quotRem_eq_mod]
    have : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
      have h_odd : p % 2 = 1 := by
        by_contra h
        push_neg at h
        have : p % 2 = 0 := by omega
        have : ¬p.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
          all_goals omega
        contradiction
      omega
    rcases this with (h1 | h3 | h5 | h7)
    · -- p ≡ 1 (mod 8)
      simp [h1, pow_two, Nat.mul_mod, Nat.sub_mod_eq_zero_of_mod_eq]
      have : (p ^ 2 - 1) / 8 % 2 = 0 := by
        have : ∃ k, p = 8 * k + 1 := by
          refine ⟨p / 8, by omega⟩
        rcases this with ⟨k, hk⟩
        rw [hk]
        ring_nf
        omega
      rw [neg_one_pow_eq_pow_mod_two]
      simp [this]
    · -- p ≡ 3 (mod 8)
      simp [h3]
      have : (p ^ 2 - 1) / 8 % 2 = 1 := by
        have : ∃ k, p = 8 * k + 3 := by
          refine ⟨p / 8, by omega⟩
        rcases this with ⟨k, hk⟩
        rw [hk]
        ring_nf
        omega
      rw [neg_one_pow_eq_pow_mod_two]
      simp [this]
    · -- p ≡ 5 (mod 8)
      simp [h5]
      have : (p ^ 2 - 1) / 8 % 2 = 1 := by
        have : ∃ k, p = 8 * k + 5 := by
          refine ⟨p / 8, by omega⟩
        rcases this with ⟨k, hk⟩
        rw [hk]
        ring_nf
        omega
      rw [neg_one_pow_eq_pow_mod_two]
      simp [this]
    · -- p ≡ 7 (mod 8)
      simp [h7, pow_two, Nat.mul_mod, Nat.sub_mod_eq_zero_of_mod_eq]
      have : (p ^ 2 - 1) / 8 % 2 = 0 := by
        have : ∃ k, p = 8 * k + 7 := by
          refine ⟨p / 8, by omega⟩
        rcases this with ⟨k, hk⟩
        rw [hk]
        ring_nf
        omega
      rw [neg_one_pow_eq_pow_mod_two]
      simp [this]
  exact h2

/-- 用模8分类表述第二补充法则 -/
theorem second_supplement_mod8 (p : ℕ) (hp : p.Prime) (hp_odd : p > 2) :
    (p % 8 = 1 ∨ p % 8 = 7 → legendreSymbol p hp 2 = 1) ∧
    (p % 8 = 3 ∨ p % 8 = 5 → legendreSymbol p hp 2 = -1) := by
  constructor
  · -- 证明 p ≡ ±1 (mod 8) 时 (2/p) = 1
    intro h
    rcases h with (h1 | h7)
    · -- p ≡ 1 (mod 8)
      rw [second_supplement p hp hp_odd]
      have h_p_mod_8 : p % 8 = 1 := h1
      -- 此时 (p²-1)/8 是偶数
      have h_exp_even : ((p ^ 2 - 1) / 8) % 2 = 0 := by
        have : ∃ k, p = 8 * k + 1 := by
          refine ⟨p / 8, by omega⟩
        rcases this with ⟨k, hk⟩
        rw [hk]
        ring_nf
        omega
      have h_power : (-1 : ℤ) ^ ((p ^ 2 - 1) / 8) = 1 := by
        have h_exp : ∃ m, (p ^ 2 - 1) / 8 = 2 * m := by
          refine ⟨(p ^ 2 - 1) / 16, by omega⟩
        rcases h_exp with ⟨m, hm⟩
        rw [hm]
        rw [pow_mul]
        simp
      exact h_power
    · -- p ≡ 7 (mod 8)
      rw [second_supplement p hp hp_odd]
      have h_p_mod_8 : p % 8 = 7 := h7
      -- 此时 (p²-1)/8 也是偶数
      have h_exp_even : ((p ^ 2 - 1) / 8) % 2 = 0 := by
        have : ∃ k, p = 8 * k + 7 := by
          refine ⟨p / 8, by omega⟩
        rcases this with ⟨k, hk⟩
        rw [hk]
        ring_nf
        omega
      have h_power : (-1 : ℤ) ^ ((p ^ 2 - 1) / 8) = 1 := by
        have h_exp : ∃ m, (p ^ 2 - 1) / 8 = 2 * m := by
          refine ⟨(p ^ 2 - 1) / 16, by omega⟩
        rcases h_exp with ⟨m, hm⟩
        rw [hm]
        rw [pow_mul]
        simp
      exact h_power
  · -- 证明 p ≡ ±3 (mod 8) 时 (2/p) = -1
    intro h
    rcases h with (h3 | h5)
    · -- p ≡ 3 (mod 8)
      rw [second_supplement p hp hp_odd]
      have h_p_mod_8 : p % 8 = 3 := h3
      -- 此时 (p²-1)/8 是奇数
      have h_exp_odd : ((p ^ 2 - 1) / 8) % 2 = 1 := by
        have : ∃ k, p = 8 * k + 3 := by
          refine ⟨p / 8, by omega⟩
        rcases this with ⟨k, hk⟩
        rw [hk]
        ring_nf
        omega
      have h_power : (-1 : ℤ) ^ ((p ^ 2 - 1) / 8) = -1 := by
        have h_exp : ∃ m, (p ^ 2 - 1) / 8 = 2 * m + 1 := by
          refine ⟨(p ^ 2 - 9) / 16, by omega⟩
        rcases h_exp with ⟨m, hm⟩
        rw [hm]
        rw [pow_add, pow_mul]
        simp
      exact h_power
    · -- p ≡ 5 (mod 8)
      rw [second_supplement p hp hp_odd]
      have h_p_mod_8 : p % 8 = 5 := h5
      -- 此时 (p²-1)/8 是奇数
      have h_exp_odd : ((p ^ 2 - 1) / 8) % 2 = 1 := by
        have : ∃ k, p = 8 * k + 5 := by
          refine ⟨p / 8, by omega⟩
        rcases this with ⟨k, hk⟩
        rw [hk]
        ring_nf
        omega
      have h_power : (-1 : ℤ) ^ ((p ^ 2 - 1) / 8) = -1 := by
        have h_exp : ∃ m, (p ^ 2 - 1) / 8 = 2 * m + 1 := by
          refine ⟨(p ^ 2 - 25) / 16, by omega⟩
        rcases h_exp with ⟨m, hm⟩
        rw [hm]
        rw [pow_add, pow_mul]
        simp
      exact h_power

/-
## 二次互反律

**定理**：对于不同的奇素数 p 和 q：
(p/q)(q/p) = (-1)^{((p-1)/2)((q-1)/2)}

等价表述：
- 若 p ≡ 1 (mod 4) 或 q ≡ 1 (mod 4)，则 (p/q) = (q/p)
- 若 p ≡ q ≡ 3 (mod 4)，则 (p/q) = -(q/p)

**数学意义**：
- 这是数论中最优美的定理之一
- 建立了不同素数模下二次剩余的深刻联系
- 是代数数论的起点（Hilbert第9问题相关）

**证明思路**（高斯和的证明）：
考虑高斯和：G = ∑_{a=0}^{p-1} (a/p) e^{2πia/p}

可以证明：G² = (-1)^{(p-1)/2} p

因此 G^{q-1} = ((-1)^{(p-1)/2} p)^{(q-1)/2}
            ≡ ((-1)^{(p-1)/2})^{(q-1)/2} (p/q) (mod q)
            = (-1)^{((p-1)/2)((q-1)/2)} (p/q) (mod q)

另一方面，G^q ≡ (q/p) G (mod q)（通过直接计算）

比较两式即得二次互反律。
-/
theorem quadratic_reciprocity (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp_odd : p > 2) (hq_odd : q > 2) (hpq : p ≠ q) :
    legendreSymbol q hp p * legendreSymbol p hq q = 
    (-1 : ℤ) ^ (((p - 1) / 2) * ((q - 1) / 2)) := by
  -- 调用Mathlib的二次互反律
  rw [legendreSymbol, legendreSymbol]
  have h1 := @LegendreSym.quadratic_reciprocity p (fact_iff.2 hp) q (fact_iff.2 hq) hpq
  -- 将LegendreSym的结果转换为ℤ
  simp only [legendreSym, ZMod.χ] at h1
  -- 使用欧拉准则转换
  have h2 : ((p : ℤ) : ZMod q) ^ ((q - 1) / 2) * ((q : ℤ) : ZMod p) ^ ((p - 1) / 2) = 
            (-1 : ZMod (q * p)) ^ (((p - 1) / 2) * ((q - 1) / 2)) := by
    -- 这里使用Mathlib中的二次互反律
    sorry -- 需要更精细地处理类型转换
  sorry -- 需要进一步的工作来连接Mathlib的结果

/-- 二次互反律的等价表述 -/
theorem quadratic_reciprocity_alt (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp_odd : p > 2) (hq_odd : q > 2) (hpq : p ≠ q) :
    (p % 4 = 1 ∨ q % 4 = 1 → legendreSymbol q hp p = legendreSymbol p hq q) ∧
    (p % 4 = 3 ∧ q % 4 = 3 → legendreSymbol q hp p = -legendreSymbol p hq q) := by
  constructor
  · -- 若 p ≡ 1 (mod 4) 或 q ≡ 1 (mod 4)
    intro h
    rcases h with (hp1 | hq1)
    · -- p ≡ 1 (mod 4)，则 (p-1)/2 是偶数
      have h_even : ((p - 1) / 2) % 2 = 0 := by
        have h_p_mod_4 : p % 4 = 1 := hp1
        have h_p_eq : ∃ k, p = 4 * k + 1 := by
          refine ⟨p / 4, by omega⟩
        rcases h_p_eq with ⟨k, hk⟩
        rw [hk]
        ring_nf
        omega
      -- 因此指数为偶数，右边为1
      have h_exp : (((p - 1) / 2) * ((q - 1) / 2)) % 2 = 0 := by
        simp [Nat.mul_mod, h_even]
      -- 利用二次互反律
      have h_main : legendreSymbol q hp p * legendreSymbol p hq q = 
                    (-1 : ℤ) ^ (((p - 1) / 2) * ((q - 1) / 2)) := by
        sorry -- 应用二次互反律
      sorry -- 需要完成证明
    · -- q ≡ 1 (mod 4)，则 (q-1)/2 是偶数
      have h_even : ((q - 1) / 2) % 2 = 0 := by
        have h_q_mod_4 : q % 4 = 1 := hq1
        have h_q_eq : ∃ k, q = 4 * k + 1 := by
          refine ⟨q / 4, by omega⟩
        rcases h_q_eq with ⟨k, hk⟩
        rw [hk]
        ring_nf
        omega
      -- 因此指数为偶数，右边为1
      have h_exp : (((p - 1) / 2) * ((q - 1) / 2)) % 2 = 0 := by
        simp [Nat.mul_mod, h_even]
      sorry -- 需要完成证明
  · -- 若 p ≡ q ≡ 3 (mod 4)
    intro h
    rcases h with ⟨hp3, hq3⟩
    -- 两个 (p-1)/2 和 (q-1)/2 都是奇数
    have h_odd1 : ((p - 1) / 2) % 2 = 1 := by
      have h_p_mod_4 : p % 4 = 3 := hp3
      have h_p_eq : ∃ k, p = 4 * k + 3 := by
        refine ⟨(p - 3) / 4, by omega⟩
      rcases h_p_eq with ⟨k, hk⟩
      rw [hk]
      ring_nf
      omega
    have h_odd2 : ((q - 1) / 2) % 2 = 1 := by
      have h_q_mod_4 : q % 4 = 3 := hq3
      have h_q_eq : ∃ k, q = 4 * k + 3 := by
        refine ⟨(q - 3) / 4, by omega⟩
      rcases h_q_eq with ⟨k, hk⟩
      rw [hk]
      ring_nf
      omega
    -- 因此指数为奇数，右边为-1
    have h_exp : (((p - 1) / 2) * ((q - 1) / 2)) % 2 = 1 := by
      simp [Nat.mul_mod, h_odd1, h_odd2]
    sorry -- 需要完成证明

/-
## 二次互反律的应用：计算Legendre符号

**例**：计算 (17/103)

利用二次互反律：
(17/103) = (103/17) · (-1)^{((17-1)/2)((103-1)/2)}
         = (103/17) · (-1)^{8·51}
         = (103/17)
         = (1/17)  （因为 103 ≡ 1 (mod 17)）
         = 1

因此 17 是模 103 的二次剩余。
-/
theorem example_calculation :
    -- 计算 (17/103) = 1
    legendreSymbol 103 (by norm_num) 17 = 1 := by
  -- 利用二次互反律
  -- 17和103都是奇素数
  -- (17/103) = (103/17) * (-1)^{((17-1)/2)((103-1)/2)}
  -- (17-1)/2 = 8, (103-1)/2 = 51, 都是偶数，所以指数为偶数
  -- (17/103) = (103/17) = (1/17) = 1
  -- 因为 103 = 6*17 + 1，所以 103 ≡ 1 (mod 17)
  -- 1是任何素数的二次剩余
  sorry -- 需要实际计算Legendre符号

/-
## Jacobi符号的推广

**定义**：对于正奇数 n = p₁^{e₁}···pₖ^{eₖ}，定义：
(a/n) = (a/p₁)^{e₁} ··· (a/pₖ)^{eₖ}

Jacobi符号是Legendre符号的推广，但(a/n)=1不保证a是模n的二次剩余
（除非n是素数）。
-/
def jacobiSymbol (n : ℕ) (a : ℤ) : ℤ :=
  -- Jacobi符号的定义：使用素因数分解
  if n = 0 then 0
  else if n = 1 then 1
  else 
    let factors := n.primeFactorsList
    factors.foldl (fun acc p => acc * legendreSymbol p (by apply Nat.prime_of_mem_primeFactorsList; assumption) a) 1

/-
## 二次互反律在Jacobi符号下的推广

对于互素的正奇数 m 和 n：
(m/n)(n/m) = (-1)^{((m-1)/2)((n-1)/2)}

这与Legendre符号的形式相同。
-/
theorem jacobi_reciprocity (m n : ℕ) (hm : m > 0) (hn : n > 0)
    (hm_odd : Odd m) (hn_odd : Odd n) (hmn : m.Coprime n) :
    jacobiSymbol n m * jacobiSymbol m n = 
    (-1 : ℤ) ^ (((m - 1) / 2) * ((n - 1) / 2)) := by
  -- Jacobi符号的二次互反律
  -- 证明思路：利用素因数分解和Legendre符号的互反律
  unfold jacobiSymbol
  -- 需要处理m=0或n=0的情况（已由前提排除）
  -- 需要处理m=1或n=1的情况（平凡情况）
  -- 对一般的奇数，使用素因数分解
  sorry -- 需要利用素因数分解和Legendre符号的互反律

end QuadraticReciprocity
