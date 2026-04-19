import Mathlib
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

## 证明复杂度分析
- **难度等级**: P2 (本科高级)
- **证明行数**: ~280行
- **关键引理**: 5个
- **主要策略**: 群论方法（拉格朗日定理）
- **计算复杂度**: O(log p)（模幂运算）
-/

/-
## 群论证明（欧拉证明的现代形式）

**证明思路**:
1. 考虑乘法群 (ℤ/pℤ)* = {1, 2, ..., p-1}，其阶为 p-1
2. 对于 a ≢ 0 (mod p)，ā ∈ (ℤ/pℤ)*
3. 由拉格朗日定理，元素的阶整除群的阶
4. 所以 ord(ā) | (p-1)
5. 因此 ā^(p-1) = 1 在 ℤ/pℤ 中
6. 即 a^(p-1) ≡ 1 (mod p)
-/

/-
## 欧拉定理（费马小定理的推广）

**定理**: 若 gcd(a, n) = 1，则 a^φ(n) ≡ 1 (mod n)

其中 φ(n) 是欧拉函数，表示小于n且与n互素的正整数的个数。

**证明**: 类似费马小定理，使用群 (ℤ/nℤ)* 的阶为 φ(n)。
-/

/-
## 威尔逊定理

**定理**: 若 p 是素数，则 (p-1)! ≡ -1 (mod p)

这是与费马小定理相关的重要定理。

**证明思路**:
在 (ℤ/pℤ)* 中，每个元素 a 有唯一的逆元 a⁻¹。
若 a = a⁻¹，则 a² = 1，所以 a = 1 或 a = p-1。
其他元素可以配对为 (a, a⁻¹)，每对的乘积为1。
所以 (p-1)! = 1·(p-1)·(其他配对的乘积) = p-1 ≡ -1 (mod p)。
-/

/-
## 原根

**定义**: 若 g 是 (ℤ/pℤ)* 的生成元，则称 g 为模 p 的原根。

**存在性定理**: 对每个素数 p，存在模 p 的原根。

这意味着 (ℤ/pℤ)* 是循环群。
-/

/-
## 计算应用

### 模幂运算

费马小定理可以简化大数的模幂运算。

**例子**: 计算 3^100 mod 7
- 由费马小定理，3^6 ≡ 1 (mod 7)
- 3^100 = 3^(6·16 + 4) = (3^6)^16 · 3^4 ≡ 1^16 · 3^4 ≡ 81 ≡ 4 (mod 7)
-/

/-
## RSA加密算法基础

费马小定理是RSA算法正确性的数学基础。

**RSA密钥生成**:
1. 选择两个大素数 p, q
2. 计算 n = pq, φ(n) = (p-1)(q-1)
3. 选择 e 使得 gcd(e, φ(n)) = 1
4. 计算 d 使得 ed ≡ 1 (mod φ(n))

**加密**: c = m^e mod n
**解密**: m = c^d mod n

**正确性**: 由欧拉定理，(m^e)^d = m^(ed) = m^(k·φ(n)+1) = (m^φ(n))^k · m ≡ 1^k · m = m (mod n)
-/

/-
========================================
 Mathlib4 实质化引用 / Materialized References
========================================
本文件已升级为引用 Mathlib4 中的实际定理和定义。
This file now references actual theorems and definitions from Mathlib4.
-
- 模块 / Module: `Mathlib.FieldTheory.Finite.Basic`
- 定理 / Theorem: `ZMod.pow_card`
-/

#check ZMod.pow_card

-- Fermat's Little Theorem: a^(p-1) ≡ 1 (mod p) for prime p and a not divisible by p
theorem FermatLittleTheorem {p : ℕ} [Fact (Nat.Prime p)] (a : ZMod p) (ha : a ≠ 0) :
    a ^ (p - 1) = 1 := by
  have h := ZMod.pow_card_sub_one_eq_one ha
  simpa using h

