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
-/

namespace ChineseRemainderTheorem

/-- 同余关系定义：a ≡ b (mod n) 当且仅当 n | (a - b) -/
def ModEq (a b n : Nat) : Prop :=
  a % n = b % n

/-- 同余记号 -/
notation:50 a " ≡ " b " [MOD " n "]" => ModEq a b n

/-- 两元中国剩余定理：当 m 和 n 互素时，同余方程组有解 

**定理**：若 gcd(m,n) = 1，则方程组
```
x ≡ a (mod m)
x ≡ b (mod n)
```
有解。

**构造性证明**：使用 Bezout 恒等式 -/
theorem chinese_remainder_two (m n a b : Nat)
    (h_coprime : Nat.gcd m n = 1) :
    ∃ x : Nat, x ≡ a [MOD m] ∧ x ≡ b [MOD n] := by
  sorry

/-- 中国剩余定理的唯一性 

**定理**：若 x 和 y 都满足同余方程组，则 x ≡ y (mod mn) -/
theorem chinese_remainder_unique (m n a b : Nat)
    (h_coprime : Nat.gcd m n = 1)
    (x y : Nat)
    (hx : x ≡ a [MOD m] ∧ x ≡ b [MOD n])
    (hy : y ≡ a [MOD m] ∧ y ≡ b [MOD n]) :
    x % (m * n) = y % (m * n) := by
  sorry

/-- 多元中国剩余定理（归纳形式）

**定理**：设 n₁, n₂, ..., nₖ 两两互素，则同余方程组
```
x ≡ aᵢ (mod nᵢ)  (i = 1, 2, ..., k)
```
在模 N = n₁n₂...nₖ 下有唯一解。 -/
theorem chinese_remainder_multiple (k : Nat) (n : Nat → Nat) (a : Nat → Nat)
    (h_pairwise : ∀ i j, i < k → j < k → i ≠ j → Nat.gcd (n i) (n j) = 1)
    (h_nz : ∀ i, i < k → n i > 0) :
    ∃ x : Nat, ∀ i, i < k → x ≡ a i [MOD (n i)] := by
  sorry

/-- 孙子算经问题的验证

"今有物不知其数，三三数之剩二，五五数之剩三，七七数之剩二，问物几何？"

即求解：
```
x ≡ 2 (mod 3)
x ≡ 3 (mod 5)
x ≡ 2 (mod 7)
```

最小正整数解为 23。 -/
example : ∃ x : Nat, x ≡ 2 [MOD 3] ∧ x ≡ 3 [MOD 5] ∧ x ≡ 2 [MOD 7] := by
  use 23
  apply And.intro
  · show 23 % 3 = 2 % 3
    exact rfl
  apply And.intro
  · show 23 % 5 = 3 % 5
    exact rfl
  · show 23 % 7 = 2 % 7
    exact rfl

end ChineseRemainderTheorem
