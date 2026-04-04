/-
# 中国剩余定理的形式化证明 / Chinese Remainder Theorem

## 定理信息
- **定理名称**: 中国剩余定理 (Chinese Remainder Theorem, CRT)
- **数学领域**: 数论 / Number Theory
- **MSC2020编码**: 11A07 (模算术), 11Y16 (数论算法)
- **对齐课程**: 初等数论、抽象代数

## Mathlib4对应
- **模块**: `Mathlib.Data.ZMod.Basic`, `Mathlib.RingTheory.Ideal.Quotient`
- **核心定理**: `ZMod.chineseRemainder`
- **相关定义**: 
  - `ZMod`: 模n整数环
  - `Ideal.Quotient`: 商环
  - `IsCoprime`: 互素理想

## 定理陈述
设 n₁, n₂, ..., nₖ 是两两互素的正整数，则对于任意整数 a₁, a₂, ..., aₖ，
同余方程组：
  x ≡ a₁ (mod n₁)
  x ≡ a₂ (mod n₂)
  ...
  x ≡ aₖ (mod nₖ)
在模 N = n₁n₂...nₖ 下有唯一解。

## 数学意义
中国剩余定理是数论中最基本的定理之一，它表明：
1. 两两互素模数下的同余方程组有唯一解
2. 环同构：ℤ/(n₁n₂)ℤ ≅ ℤ/n₁ℤ × ℤ/n₂ℤ (当gcd(n₁,n₂)=1时)
3. 在密码学、编码理论中有广泛应用

## 历史背景
该定理最早出现在中国《孙子算经》（公元3-5世纪）中的"物不知数"问题。
完整的证明由秦九韶在《数书九章》（1247年）中给出。
-/ 

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.Algebra.Ring.Prod
import Mathlib.Tactic

universe u

namespace ChineseRemainderTheorem

open ZMod Nat BigOperators

/-
## 核心概念

### 互素 (Coprime)
两个整数 m 和 n 互素，如果 gcd(m, n) = 1。

### 同余方程组
形如 x ≡ aᵢ (mod nᵢ) 的方程组。

### 中国剩余定理
当模数两两互素时，同余方程组有唯一解。
-/

-- 两元中国剩余定理：当 m 和 n 互素时，同余方程组有解
theorem chinese_remainder_two {m n : ℕ} (h : m.Coprime n) (a b : ℕ) :
    ∃ x : ℕ, x ≡ a [MOD m] ∧ x ≡ b [MOD n] := by
  /- 证明思路：
     1. 由于 gcd(m,n)=1，存在整数 s, t 使得 sm + tn = 1（Bezout等式）
     2. 取 x = b·s·m + a·t·n
     3. 验证 x ≡ a (mod m) 和 x ≡ b (mod n)
  -/
  
  -- 使用Bezout引理，存在 s, t 使得 s·m + t·n = gcd(m,n) = 1
  rcases h with ⟨s, t, h_bezout⟩
  
  -- 构造解
  let x := b * s * m + a * t * n
  
  -- 验证 x ≡ a (mod m)
  have h1 : x ≡ a [MOD m] := by
    simp [x, Nat.ModEq]
    have : (b * s * m + a * t * n) % m = (a * t * n) % m := by
      simp [Nat.mul_mod, Nat.add_mod]
    rw [this]
    have htn : t * n ≡ 1 [MOD m] := by
      rw [Nat.ModEq]
      have : (s * m + t * n) % m = 1 % m := by
        rw [h_bezout]
      simp [Nat.add_mod, Nat.mul_mod] at this
      exact this
    have : (a * t * n) % m = a % m := by
      have htn' : (t * n) % m = 1 % m := by
        rw [Nat.ModEq] at htn
        exact htn
      calc
        (a * t * n) % m = (a * ((t * n) % m)) % m := by simp [Nat.mul_mod]
        _ = (a * (1 % m)) % m := by rw [htn']
        _ = a % m := by simp [Nat.mul_mod]
    exact this
  
  -- 验证 x ≡ b (mod n)
  have h2 : x ≡ b [MOD n] := by
    simp [x, Nat.ModEq]
    have : (b * s * m + a * t * n) % n = (b * s * m) % n := by
      simp [Nat.mul_mod, Nat.add_mod]
    rw [this]
    have hsm : s * m ≡ 1 [MOD n] := by
      rw [Nat.ModEq]
      have : (s * m + t * n) % n = 1 % n := by
        rw [h_bezout]
      simp [Nat.add_mod, Nat.mul_mod] at this
      exact this
    have : (b * s * m) % n = b % n := by
      have hsm' : (s * m) % n = 1 % n := by
        rw [Nat.ModEq] at hsm
        exact hsm
      calc
        (b * s * m) % n = (b * ((s * m) % n)) % n := by simp [Nat.mul_mod]
        _ = (b * (1 % n)) % n := by rw [hsm']
        _ = b % n := by simp [Nat.mul_mod]
    exact this
  
  exact ⟨x, h1, h2⟩

-- 中国剩余定理：环同构版本
theorem chinese_remainder_ring_iso {m n : ℕ} (h : m.Coprime n) :
    ZMod (m * n) ≃+* ZMod m × ZMod n := by
  /- 使用Mathlib4的中国剩余定理 -/
  exact ZMod.chineseRemainder h

-- 中国剩余定理的逆：如果同构成立，则 m 和 n 互素
theorem chinese_remainder_converse {m n : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (h : Nonempty (ZMod (m * n) ≃+* ZMod m × ZMod n)) :
    m.Coprime n := by
  /- 证明思路：如果 ℤ/(mn)ℤ ≅ ℤ/mℤ × ℤ/nℤ，则两个环的单位群同构
     ℤ/(mn)ℤ 的单位群阶为 φ(mn)
     ℤ/mℤ × ℤ/nℤ 的单位群阶为 φ(m)·φ(n)
     所以 φ(mn) = φ(m)·φ(n)，这要求 m 和 n 互素
  -/
  rcases h with ⟨f⟩
  -- 使用 Mathlib 的已有结果：若 ZMod(mn) ≅ ZMod(m) × ZMod(n)，则 m 和 n 互素
  have h_iso : ZMod (m * n) ≃+* ZMod m × ZMod n := f
  -- 利用单位群的同构：单位群的阶必须相等
  have h_units : Fintype.card ((ZMod (m * n))ˣ) = Fintype.card ((ZMod m × ZMod n)ˣ) := by
    rw [ZMod.card_units_eq_totient]
    rw [Fintype.prod_units]
    rw [ZMod.card_units_eq_totient]
    rw [ZMod.card_units_eq_totient]
  -- φ(mn) = φ(m)φ(n) 当且仅当 m 和 n 互素
  rw [Nat.totient_mul (by assumption)] at h_units
  · -- 若 m 和 n 互素，则 φ(mn) = φ(m)φ(n) 成立
    exact Nat.coprime_iff_gcd_eq_one.mpr (by assumption)
  · -- 证明 m 和 n 互素
    exact Nat.coprime_iff_gcd_eq_one.mpr (by assumption)

-- 多元中国剩余定理
theorem chinese_remainder_multiple {k : ℕ} {n : Fin k → ℕ} 
    (h_pairwise : ∀ i j, i ≠ j → (n i).Coprime (n j)) 
    (hn : ∀ i, n i ≠ 0) (a : Fin k → ℕ) :
    ∃ x : ℕ, ∀ i, x ≡ a i [MOD n i] := by
  /- 对 k 使用归纳法 -/
  induction k with
  | zero =>
    -- k = 0：空同余方程组，任意 x 都是解
    use 0
    intro i
    exact Fin.elim0 i
  | succ k ih =>
    -- k = k' + 1：将前 k' 个方程与第 k' 个方程合并
    have h_k_le_n : k ≤ n := by linarith
    -- 使用前 k 个模数和中国剩余定理得到解
    have h_coprime : ∀ i j : Fin k, i ≠ j → (n i).Coprime (n j) := by
      intro i j hij
      exact h_pairwise i j hij
    have h_nz : ∀ i : Fin k, n i ≠ 0 := by
      intro i
      exact hn i
    -- 应用归纳假设得到前 k 个方程的解
    rcases ih h_k_le_n with ⟨x_k, hx_k⟩
    -- 令 M = ∏_{i < k} n i，需要将 x_k ≡ a k (mod n k) 与 x_k 的解合并
    let M := ∏ i : Fin k, n i
    have h_coprime_M : M.Coprime (n k) := by
      apply Nat.coprime_prod_left
      intro i _
      exact h_pairwise i (by simp) (by intro h; simp [h] at *)
    -- 构造新的同余方程组并求解
    have h_solution : ∃ x : ℕ, x ≡ x_k [MOD M] ∧ x ≡ a k [MOD (n k)] := by
      apply chinese_remainder_two h_coprime_M x_k (a k)
    rcases h_solution with ⟨x, hx_M, hx_k⟩
    use x
    intro i
    by_cases hi : i < k
    · -- i < k：利用归纳假设
      have h_i : i = ⟨i.val, by simp⟩ := by simp
      have h_mod : x ≡ a i [MOD n i] := by
        have h_xk : x_k ≡ a i [MOD n i] := hx_k ⟨i.val, by simp⟩
        have h_M : n i ∣ M := by
          apply Finset.dvd_prod_of_mem
          simp
        have h_x : x ≡ x_k [MOD n i] := by
          apply Nat.ModEq.of_dvd h_M
          exact hx_M
        exact Nat.ModEq.trans h_x h_xk
      exact h_mod
    · -- i = k
      have h_i : i = k := by
        apply Fin.eq_of_val_eq
        simp at hi ⊢
        omega
      rw [h_i]
      exact hx_k

-- 中国剩余定理的唯一性
theorem chinese_remainder_unique {m n : ℕ} (h : m.Coprime n) (a b : ℕ) 
    (x y : ℕ) (hx : x ≡ a [MOD m] ∧ x ≡ b [MOD n]) 
    (hy : y ≡ a [MOD m] ∧ y ≡ b [MOD n]) :
    x ≡ y [MOD (m * n)] := by
  /- 证明：如果 x 和 y 都满足同余方程组，则 x ≡ y (mod mn) -/
  rcases hx with ⟨hxm, hxn⟩
  rcases hy with ⟨hym, hyn⟩
  
  -- x ≡ y (mod m)
  have h1 : x ≡ y [MOD m] := by
    exact Nat.ModEq.trans hxm (Nat.ModEq.symm hym)
  
  -- x ≡ y (mod n)
  have h2 : x ≡ y [MOD n] := by
    exact Nat.ModEq.trans hxn (Nat.ModEq.symm hyn)
  
  -- 由于 m 和 n 互素，所以 x ≡ y (mod mn)
  exact Nat.ModEq.mul h1 h2

-- 中国剩余定理的显式构造（使用扩展欧几里得算法）
theorem chinese_remainder_constructive {m n : ℕ} (h : m.Coprime n) (a b : ℕ) :
    let g := m.gcdA n * m + m.gcdB n * n  -- g = gcd(m,n) = 1
    let M := n / g
    let N := m / g
    let x := b * m.gcdA n * m + a * m.gcdB n * n
    x ≡ a [MOD m] ∧ x ≡ b [MOD n] := by
  /- 使用扩展欧几里得算法构造解 -/
  intro g M N x
  have hg : g = 1 := by
    simp [g]
    exact h
  
  -- 验证同余条件
  constructor
  · -- x ≡ a (mod m)
    simp [x, Nat.ModEq]
    have h1 : (b * m.gcdA n * m + a * m.gcdB n * n) % m = (a * m.gcdB n * n) % m := by
      simp [Nat.mul_mod, Nat.add_mod]
    rw [h1]
    -- 使用扩展欧几里得算法的性质：gcdA n * m + gcdB n * n = gcd(m,n) = 1
    have h_bezout : m.gcdB n * n ≡ 1 [MOD m] := by
      rw [Nat.ModEq]
      have h : m.gcdA n * m + m.gcdB n * n = m.gcd n := by
        rw [Nat.gcd_eq_gcd_ab m n]
      rw [h] at *
      have h_gcd : m.gcd n = 1 := h
      simp [h_gcd, Nat.add_mod, Nat.mul_mod] at *
    have : (a * m.gcdB n * n) % m = a % m := by
      have hbn : (m.gcdB n * n) % m = 1 % m := by
        rw [Nat.ModEq] at h_bezout
        exact h_bezout
      calc
        (a * m.gcdB n * n) % m = (a * ((m.gcdB n * n) % m)) % m := by simp [Nat.mul_mod]
        _ = (a * (1 % m)) % m := by rw [hbn]
        _ = a % m := by simp [Nat.mul_mod]
    exact this
  · -- x ≡ b (mod n)
    simp [x, Nat.ModEq]
    have h2 : (b * m.gcdA n * m + a * m.gcdB n * n) % n = (b * m.gcdA n * m) % n := by
      simp [Nat.mul_mod, Nat.add_mod]
    rw [h2]
    -- 类似地证明
    have h_bezout : m.gcdA n * m ≡ 1 [MOD n] := by
      rw [Nat.ModEq]
      have h : m.gcdA n * m + m.gcdB n * n = m.gcd n := by
        rw [Nat.gcd_eq_gcd_ab m n]
      rw [h] at *
      have h_gcd : m.gcd n = 1 := h
      simp [h_gcd, Nat.add_mod, Nat.mul_mod] at *
    have : (b * m.gcdA n * m) % n = b % n := by
      have ham : (m.gcdA n * m) % n = 1 % n := by
        rw [Nat.ModEq] at h_bezout
        exact h_bezout
      calc
        (b * m.gcdA n * m) % n = (b * ((m.gcdA n * m) % n)) % n := by simp [Nat.mul_mod]
        _ = (b * (1 % n)) % n := by rw [ham]
        _ = b % n := by simp [Nat.mul_mod]
    exact this

end ChineseRemainderTheorem

/-
## 应用示例

### 示例1：《孙子算经》中的"物不知数"问题

"今有物不知其数，三三数之剩二，五五数之剩三，七七数之剩二，问物几何？"

解：求 x 使得
  x ≡ 2 (mod 3)
  x ≡ 3 (mod 5)
  x ≡ 2 (mod 7)

最小正整数解为 23。

```lean
example : ∃ x : ℕ, x ≡ 2 [MOD 3] ∧ x ≡ 3 [MOD 5] ∧ x ≡ 2 [MOD 7] := by
  use 23
  constructor
  · norm_num [Nat.ModEq]
  constructor
  · norm_num [Nat.ModEq]
  · norm_num [Nat.ModEq]
```

### 示例2：环同构的应用

ℤ/15ℤ ≅ ℤ/3ℤ × ℤ/5ℤ

这给出单位群同构：
(ℤ/15ℤ)* ≅ (ℤ/3ℤ)* × (ℤ/5ℤ)*
φ(15) = φ(3)·φ(5) = 2·4 = 8

## 数学意义

中国剩余定理的重要性：

1. **算法应用**: 大数运算可以分解为小模数运算
2. **密码学**: RSA算法中的重要工具
3. **编码理论**: 纠错码的设计
4. **代数结构**: 揭示模算术的乘积结构

## 推广

1. **交换环**: 对互素理想 I, J，有 R/(I∩J) ≅ R/I × R/J
2. **主理想整环**: 对两两互素元素 a₁, ..., aₙ，有类似的同构
3. **代数几何**: 在层论和概形理论中的应用

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `Mathlib.Data.ZMod.Basic`: 模n整数环
- `Mathlib.RingTheory.Ideal.Quotient`: 商环理论
- `ZMod.chineseRemainder`: 中国剩余定理的核心实现
- `Nat.ModEq`: 模同余关系
- `Nat.Coprime`: 互素整数的性质
-/
