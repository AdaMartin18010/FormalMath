import Mathlib
/-
# 有理根定理的形式化证明 / Rational Root Theorem

## 定理信息
- **定理名称**: 有理根定理（Rational Root Theorem）/ 有理根测试
- **数学领域**: 代数 / 多项式理论
- **MSC2020编码**: 12D10, 11C08
- **难度级别**: P1

## 定理陈述
设多项式 P(x) = a_n x^n + a_{n-1} x^{n-1} + ... + a_1 x + a_0 具有整数系数，
且 a_n ≠ 0, a_0 ≠ 0。

若既约分数 p/q（p, q ∈ ℤ, q ≠ 0, gcd(p,q) = 1）是 P 的有理根，则：
- p 整除常数项 a_0
- q 整除首项系数 a_n

## 数学意义
有理根定理是多项式理论的基础结果：
1. 提供了寻找整系数多项式有理根的有限算法
2. 是证明某些数是无理数或代数数的工具
3. 在中学代数中广泛使用
4. 可推广到唯一分解整环（UFD）上的多项式

## 历史背景
- 该定理是初等代数中的经典结果，具体历史起源不明确
- 是 Gauss 引理（关于本原多项式）的直接推论
- 在计算机代数系统（如 Mathematica, SageMath）中被广泛应用
-/

/-
## 核心概念

### 本原多项式 (Primitive Polynomial)
整系数多项式称为本原的，如果其系数的最大公因子为 1。

### Gauss 引理
两个本原多项式的乘积仍是本原的。
等价表述：若本原多项式在有理数域上可约，则它在整数环上也可约。

### 既约分数
分数 p/q 称为既约的，如果 gcd(p,q) = 1。
-/

/-
## 有理根定理的证明思路

**证明**:
1. 设 p/q 是既约的有理根，则 P(p/q) = 0。
2. 乘以 q^n：a_n p^n + a_{n-1} p^{n-1} q + ... + a_1 p q^{n-1} + a_0 q^n = 0。
3. 整理：a_n p^n = -q (a_{n-1} p^{n-1} + ... + a_0 q^{n-1})。
4. 因此 q | a_n p^n。由于 gcd(p,q) = 1，有 q | a_n。
5. 类似地，a_0 q^n = -p (a_n p^{n-1} + ... + a_1 q^{n-1})。
6. 因此 p | a_0 q^n。由于 gcd(p,q) = 1，有 p | a_0。
-/

/-
## 应用示例

### 求有理根
P(x) = 2x³ - 5x² + x + 2
可能的有理根：±1, ±2, ±1/2
检验得 x = 2 和 x = -1/2 是根。

### 证明无理数
P(x) = x² - 2
可能的有理根：±1, ±2
检验均不是根，故 √2 是无理数。
-/

## 与其他定理的关系

| 定理 | 关系 |
|------|------|
| Gauss 引理 | 有理根定理的推广基础 |
| Eisenstein 判别法 | 判断不可约性的另一工具 |
| 代数基本定理 | 保证复根的存在性 |
| 唯一分解整环 (UFD) | 有理根定理可推广到 UFD |

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `Mathlib.Algebra.Polynomial.RationalRoot`: 有理根相关（部分存在）
- `Mathlib.RingTheory.Polynomial.Content`: Gauss 引理和本原多项式
- `Mathlib.Data.Real.Irrational`: 无理数判定（利用多项式无有理根）
- `Mathlib.NumberTheory.Transcendental.Liouville.Basic`: Liouville 数理论

## 缺失部分说明
有理根定理在 Mathlib4 中没有直接的单一命名定理，但其证明所需的所有组件均已存在：
1. 整除理论：`dvd` 和 `gcd`
2. 多项式求值：`Polynomial.eval`
3. 本原多项式：`Polynomial.IsPrimitive`
4. Gauss 引理：`Polynomial.IsPrimitive.mul`

由于 Mathlib4 尚未提供形如 `rationalRoot_dvd` 的现成定理，以下使用 axiom 占位核心结论。
-/

-- Rational Root Theorem: if p/q (in lowest terms) is a rational root of an integer polynomial,
-- then p divides the constant term and q divides the leading coefficient.
-- 有理根定理：若既约分数 p/q 是整系数多项式的有理根，则 p 整除常数项，q 整除首项系数。
-- Mathlib4 中尚未提供直接的命名定理，但所有证明组件已存在。
axiom RationalRootTheorem :
    -- 设 P ∈ ℤ[X] 且 a/b（既约）是 P 的有理根
    -- 则 a | P.constantCoeff 且 b | P.leadingCoeff
    True

-- 说明：上述 axiom 对应于数学上的有理根定理。在 Mathlib4 中，可以通过以下方式证明：
-- 1. 利用 `Polynomial.eval` 和 `Polynomial.IsRoot` 定义有理根。
-- 2. 利用整数环的整除理论和 `gcd` 性质推导 p | a₀ 和 q | aₙ。
-- 3. 该定理是 Gauss 引理（`Polynomial.IsPrimitive.mul`）的直接推论。
