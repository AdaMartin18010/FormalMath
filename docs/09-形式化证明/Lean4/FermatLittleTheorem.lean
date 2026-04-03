/-
# 费马小定理的形式化证明 / Formalization of Fermat's Little Theorem

## Mathlib4对应
- **模块**: `Mathlib.NumberTheory.Fermat`
- **核心定理**: `ZMod.pow_card`
- **相关定义**: 
  - `ZMod`: 模n整数环
  - `Units`: 单位群
  - `Fintype.card`: 有限类型基数

## 定理陈述
若 p 是素数，a 是不被 p 整除的整数，则：

    a^(p-1) ≡ 1 (mod p)

等价表述：对于任意整数 a，
    a^p ≡ a (mod p)

## 数学意义
费马小定理是初等数论的基石，在密码学（特别是RSA算法）中有核心应用。

## 历史背景
该定理由皮埃尔·德·费马在1640年提出，是数论中最著名的定理之一。
欧拉在1736年给出了第一个证明，并推广为欧拉定理。
-/

import Mathlib.NumberTheory.Fermat
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Group.Basic

universe u

namespace FermatLittleTheorem

open Nat ZMod Fintype

/-
## 群论证明（欧拉证明的现代形式）

**证明思路**:
1. 考虑乘法群 (ℤ/pℤ)* = {1, 2, ..., p-1}，其阶为 p-1
2. 对于 a ≢ 0 (mod p)，ā ∈ (ℤ/pℤ)*
3. 由拉格朗日定理，元素的阶整除群的阶
4. 所以 ord(ā) | (p-1)
5. 因此 ā^(p-1) = 1 在 ℤ/pℤ 中
6. 即 a^(p-1) ≡ 1 (mod p)
-

-- 模p乘法群的定义
def UnitsZMod (p : ℕ) [Fact p.Prime] : Type := (ZMod p)ˣ

-- 模p乘法群的阶为 p-1
theorem units_zmod_card (p : ℕ) [Fact p.Prime] :
    card ((ZMod p)ˣ) = p - 1 := by
  /- (ℤ/pℤ)* 的元素是 1, 2, ..., p-1 -/
  rw [ZMod.card_units_eq_totient]
  rw [Nat.totient_prime]
  infer_instance

-- 费马小定理（群论版本）
theorem fermat_little_theorem_group {p : ℕ} [Fact p.Prime] (a : (ZMod p)ˣ) :
    a ^ (p - 1) = 1 := by
  /- 应用拉格朗日定理：元素的阶整除群的阶 -/
  have h_order_dvd : orderOf a ∣ p - 1 := by
    rw [← units_zmod_card p]
    apply orderOf_dvd_card
  
  /- 设 orderOf a = d，则 d | (p-1)，所以存在 k 使得 p-1 = d·k -/
  rcases h_order_dvd with ⟨k, hk⟩
  
  /- a^(p-1) = a^(d·k) = (a^d)^k = 1^k = 1 -/
  calc
    a ^ (p - 1) = a ^ (orderOf a * k) := by rw [hk]
    _ = (a ^ orderOf a) ^ k := by rw [pow_mul]
    _ = 1 ^ k := by rw [pow_orderOf_eq_one a]
    _ = 1 := by simp

-- 费马小定理的标准形式
theorem fermat_little_theorem {p : ℕ} [Fact p.Prime] (a : ℕ) (hpa : ¬p ∣ a) :
    a ^ (p - 1) ≡ 1 [MOD p] := by
  /- 将 a 视为 (ℤ/pℤ)* 的元素 -/
  let a_unit : (ZMod p)ˣ := ZMod.unitOfCoprime a (by
    apply Nat.coprime_iff_not_dvd.mpr
    exact hpa
  )
  
  /- 应用群论版本的定理 -/
  have h : a_unit ^ (p - 1) = 1 := fermat_little_theorem_group a_unit
  
  /- 转换回模运算表述 -/
  rw [← ZMod.eq_iff_modEq_nat p]
  simpa [a_unit] using h

-- 费马小定理的等价形式：a^p ≡ a (mod p)
theorem fermat_little_theorem' {p : ℕ} [Fact p.Prime] (a : ℕ) :
    a ^ p ≡ a [MOD p] := by
  by_cases hpa : p ∣ a
  · /- 若 p | a，则 a ≡ 0 (mod p)，显然 a^p ≡ 0 (mod p) -/
    have h_a : a ≡ 0 [MOD p] := by
      exact Nat.modEq_zero_iff_dvd.mpr hpa
    have h_ap : a ^ p ≡ 0 [MOD p] := by
      rw [Nat.modEq_zero_iff_dvd]
      apply dvd_pow
      exact hpa
      exact Nat.Prime.pos (Fact.elim (inferInstance))
    exact Nat.ModEq.trans h_ap h_a.symm
  
  · /- 若 p ∤ a，应用费马小定理 -/
    have h : a ^ (p - 1) ≡ 1 [MOD p] := fermat_little_theorem a hpa
    /- a^p = a·a^(p-1) ≡ a·1 = a (mod p) -/
    calc
      a ^ p = a * a ^ (p - 1) := by
        cases p
        · contradiction
        · rw [Nat.succ_sub_one, pow_succ]
      _ ≡ a * 1 [MOD p] := by
        apply Nat.ModEq.mul_left
        exact h
      _ = a := by simp

/-
## 欧拉定理（费马小定理的推广）

**定理**: 若 gcd(a, n) = 1，则 a^φ(n) ≡ 1 (mod n)

其中 φ(n) 是欧拉函数，表示小于n且与n互素的正整数的个数。

**证明**: 类似费马小定理，使用群 (ℤ/nℤ)* 的阶为 φ(n)。
-

-- 欧拉定理
theorem euler_theorem {n a : ℕ} (hcoprime : Nat.Coprime a n) (hn : n > 0) :
    a ^ (Nat.totient n) ≡ 1 [MOD n] := by
  /- 将 a 视为 (ℤ/nℤ)* 的元素 -/
  let a_unit : (ZMod n)ˣ := ZMod.unitOfCoprime a hcoprime
  
  /- (ℤ/nℤ)* 的阶为 φ(n) -/
  have h_card : card ((ZMod n)ˣ) = Nat.totient n := by
    rw [ZMod.card_units_eq_totient]
  
  /- 应用拉格朗日定理 -/
  have h_order_dvd : orderOf a_unit ∣ card ((ZMod n)ˣ) := by
    apply orderOf_dvd_card
  
  /- 证明 a^φ(n) ≡ 1 (mod n) -/
  rw [← h_card] at h_order_dvd
  rcases h_order_dvd with ⟨k, hk⟩
  have h : a_unit ^ (Nat.totient n) = 1 := by
    calc
      a_unit ^ (Nat.totient n) = a_unit ^ (orderOf a_unit * k) := by rw [hk]
      _ = (a_unit ^ orderOf a_unit) ^ k := by rw [pow_mul]
      _ = 1 ^ k := by rw [pow_orderOf_eq_one]
      _ = 1 := by simp
  
  rw [← ZMod.eq_iff_modEq_nat n]
  simpa [a_unit] using h

/-
## 威尔逊定理

**定理**: 若 p 是素数，则 (p-1)! ≡ -1 (mod p)

这是与费马小定理相关的重要定理。

**证明思路**:
在 (ℤ/pℤ)* 中，每个元素 a 有唯一的逆元 a⁻¹。
若 a = a⁻¹，则 a² = 1，所以 a = 1 或 a = p-1。
其他元素可以配对为 (a, a⁻¹)，每对的乘积为1。
所以 (p-1)! = 1·(p-1)·(其他配对的乘积) = p-1 ≡ -1 (mod p)。
-

-- 威尔逊定理
theorem wilson_theorem {p : ℕ} [Fact p.Prime] :
    Nat.factorial (p - 1) ≡ p - 1 [MOD p] := by
  /- 使用Mathlib4的威尔逊定理 -/
  sorry  -- Mathlib4可能有现成的定理

/-
## 原根

**定义**: 若 g 是 (ℤ/pℤ)* 的生成元，则称 g 为模 p 的原根。

**存在性定理**: 对每个素数 p，存在模 p 的原根。

这意味着 (ℤ/pℤ)* 是循环群。
-

-- 原根存在性定理
theorem primitive_root_exists {p : ℕ} [Fact p.Prime] :
    ∃ g : (ZMod p)ˣ, IsPrimitiveRoot g (p - 1) := by
  /- (ℤ/pℤ)* 是循环群 -/
  have h_cyclic : IsCyclic (ZMod p)ˣ := by
    infer_instance
  
  /- 循环群有生成元 -/
  rcases h_cyclic with ⟨g, hg⟩
  use g
  sorry  -- 需要证明 g 的阶为 p-1

/-
## 计算应用

### 模幂运算

费马小定理可以简化大数的模幂运算。

**例子**: 计算 3^100 mod 7
- 由费马小定理，3^6 ≡ 1 (mod 7)
- 3^100 = 3^(6·16 + 4) = (3^6)^16 · 3^4 ≡ 1^16 · 3^4 ≡ 81 ≡ 4 (mod 7)
-

-- 快速模幂运算（利用费马小定理优化）
def fast_mod_exp (a p e : ℕ) [Fact p.Prime] (hpa : ¬p ∣ a) : ℕ :=
  /- 计算 a^e mod p，利用 a^(p-1) ≡ 1 (mod p) -/
  let e' := e % (p - 1)
  a ^ e' % p

theorem fast_mod_exp_correct {a p e : ℕ} [Fact p.Prime] (hpa : ¬p ∣ a) :
    fast_mod_exp a p e hpa ≡ a ^ e [MOD p] := by
  /- 证明优化后的计算是正确的 -/
  dsimp [fast_mod_exp]
  have h_fermat : a ^ (p - 1) ≡ 1 [MOD p] := fermat_little_theorem a hpa
  /- 使用幂的周期性 -/
  sorry

end FermatLittleTheorem

/-
## 应用示例

### RSA加密算法

费马小定理是RSA算法正确性的数学基础。

**RSA密钥生成**:
1. 选择两个大素数 p, q
2. 计算 n = pq, φ(n) = (p-1)(q-1)
3. 选择 e 使得 gcd(e, φ(n)) = 1
4. 计算 d 使得 ed ≡ 1 (mod φ(n))

**加密**: c = m^e mod n
**解密**: m = c^d mod n

**正确性**: 由欧拉定理，(m^e)^d = m^(ed) = m^(k·φ(n)+1) = (m^φ(n))^k · m ≡ 1^k · m = m (mod n)

```lean
-- RSA解密的正确性（简化版）
example {p q e d m : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (h_e_coprime : Nat.Coprime e ((p-1)*(q-1)))
    (h_ed : e * d ≡ 1 [MOD (p-1)*(q-1)]) :
    (m ^ e) ^ d ≡ m [MOD p * q] := by
  sorry  -- 需要完整的RSA正确性证明
```

## 数学意义

费马小定理的重要性：

1. **数论基础**：连接了幂运算和模运算
2. **密码学应用**：RSA、Diffie-Hellman等算法的基础
3. **素数测试**：费马素性测试的理论基础
4. **群论联系**：展示了数论和群论的深刻联系

## 历史发展

| 年份 | 数学家 | 贡献 |
|------|--------|------|
| 1640 | 费马 | 提出定理 |
| 1736 | 欧拉 | 给出第一个证明，推广为欧拉定理 |
| 1801 | 高斯 | 在《算术研究》中系统化 |
| 现代 | - | 应用于密码学和计算机科学 |

## 与其他定理的关系

- **欧拉定理**：费马小定理的推广
- **拉格朗日定理**：群论证明的基础
- **威尔逊定理**：相关的同余定理
- **二次互反律**：更深层次的数论定理

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `ZMod.pow_card`: 费马小定理的核心实现
- `Nat.ModEq`: 模同余的定义和性质
- `ZMod.unitOfCoprime`: 构造单位元
- `Nat.totient`: 欧拉函数
- `IsPrimitiveRoot`: 原根的定义
-/
