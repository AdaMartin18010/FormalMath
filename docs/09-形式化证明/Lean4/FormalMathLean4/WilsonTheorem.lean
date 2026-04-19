import Mathlib
/-
# 威尔逊定理的形式化证明 / Wilson's Theorem

## 领域
初等数论 (Elementary Number Theory)

## Mathlib4对应
- **模块**: `Mathlib.NumberTheory.Wilson`
- **核心定理**: `Nat.wilsons_lemma`
- **相关定义**:
  - `Nat.factorial`
  - `ZMod`
  - `Nat.Prime`

## MSC2020编码
- **Primary**: 11A41
- **Secondary**: 11A51

## 对齐课程
- MIT 18.781 (Theory of Numbers)
- Harvard Math 223a (Algebraic Number Theory)
- Princeton MAT 214 (Numbers, Equations, and Proofs)
- ETH 401-3052-05L (Algebraic Number Theory)

## 定理陈述
设 p 为素数，则 (p-1)! ≡ -1 (mod p)。

等价表述：在有限域 ℤ/pℤ 中，所有非零元素的乘积等于 -1。

## 数学意义
威尔逊定理提供了素数的一个充分必要条件，在组合数论和有限域理论中有重要应用。

## 历史背景
由John Wilson在1770年提出猜想，Lagrange在1771年首次证明，Gauss在《算术研究》中给出了更简洁的证明。
-/

/-
## 核心概念

### 阶乘 (Factorial)
n! = 1 × 2 × 3 × ... × n

### 威尔逊定理
p 是素数 ⟺ (p-1)! ≡ -1 (mod p)

### 证明思路
1. 在 ℤ/pℤ 中，每个非零元素 a 都有唯一的逆元 a⁻¹
2. 若 a = a⁻¹，则 a² ≡ 1 (mod p)，即 a ≡ ±1 (mod p)
3. 其余元素可以配对为 (a, a⁻¹)，每对的乘积为 1
4. 因此所有非零元素的乘积 ≡ 1 · (-1) ≡ -1 (mod p)
-/

/-
## 应用：素性测试

威尔逊定理给出了素数的精确刻画，但由于计算阶乘的复杂度，不适合大数的素性测试。

**例子**:
- p = 5: 4! = 24 ≡ -1 ≡ 4 (mod 5) ✓
- p = 7: 6! = 720 ≡ -1 ≡ 6 (mod 7) ✓
- p = 11: 10! = 3628800 ≡ -1 ≡ 10 (mod 11) ✓
-/

/-
## 威尔逊素数

威尔逊素数是指满足 p² | (p-1)! + 1 的素数。
已知的威尔逊素数：5, 13, 563。

这是一个著名的未解决问题：是否存在无穷多个威尔逊素数？
-/

/-
## 数学意义

威尔逊定理的重要性：

1. **素数刻画**: (n-1)! ≡ -1 (mod n) ⟺ n 是素数
2. **有限域结构**: 揭示了乘法群 (ℤ/pℤ)* 的循环性质
3. **组合应用**: 在组合设计和编码理论中有应用
4. **理论价值**: 素性测试的理论基础之一

## 与其他定理的关系

- **费马小定理**: 同为有限域 ℤ/pℤ 的基本性质
- **欧拉定理**: 威尔逊定理可视为欧拉定理在 φ(p)=p-1 时的特例
- **中国剩余定理**: 可用于推广到合数模的情形

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `Mathlib.NumberTheory.Wilson`: 威尔逊定理的核心实现
- `Nat.wilsons_lemma`: 自然数版本的威尔逊定理
- `ZMod.wilsons_lemma`: 有限域 ℤ/pℤ 版本的威尔逊定理
- `Nat.prime_of_fac_equiv_neg_one`: 威尔逊定理的逆
-/

/-
========================================
 Mathlib4 实质化引用 / Materialized References
========================================
本文件已升级为引用 Mathlib4 中的实际定理和定义。
This file now references actual theorems and definitions from Mathlib4.
-
- 模块 / Module: `Mathlib.NumberTheory.Wilson`
- 定理 / Theorem: `ZMod.wilsons_lemma`
-/

#check ZMod.wilsons_lemma

-- Wilson's Theorem: (p-1)! ≡ -1 (mod p) for prime p
theorem WilsonTheorem {p : ℕ} [Fact (Nat.Prime p)] :
    ((p - 1).factorial : ZMod p) = -1 := by
  exact ZMod.wilsons_lemma p

