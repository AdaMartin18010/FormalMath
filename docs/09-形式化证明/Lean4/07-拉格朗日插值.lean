/-
# 拉格朗日插值多项式的形式化 / Lagrange Interpolation Formalization

## Mathlib4对应
- **模块**: `Mathlib.Algebra.Polynomial.Lagrange`
- **核心定理**:
  - `Polynomial.lagrangeInterp`: 拉格朗日插值多项式
  - `Polynomial.eval_lagrangeInterp`: 插值多项式的求值性质
- **相关定义**:
  - `Polynomial`: 多项式类型
  - `Polynomial.eval`: 多项式求值
  - `Polynomial.degree`: 多项式次数

## 定理陈述

给定 n+1 个互异的点 (x₀, y₀), (x₁, y₁), ..., (xₙ, yₙ)，
存在唯一的次数不超过 n 的多项式 P 使得 P(xᵢ) = yᵢ 对所有 i 成立。

## 数学意义

拉格朗日插值是数值分析和逼近论的基础工具。
它保证了通过任意 n+1 个点可以唯一确定一个次数不超过 n 的多项式。

## 历史背景

由法国数学家约瑟夫·路易斯·拉格朗日(Joseph-Louis Lagrange)于1795年提出。
-/

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Finset.Basic

universe u v

namespace LagrangeInterpolation

open Polynomial BigOperators Finset

/-
## 第一部分：多项式环的基础

多项式环 R[X] 是由变量 X 和系数在环 R 中的多项式构成的环。

基本操作：
- 加法：(∑ aᵢXⁱ) + (∑ bᵢXⁱ) = ∑ (aᵢ+bᵢ)Xⁱ
- 乘法：(∑ aᵢXⁱ) · (∑ bⱼXʲ) = ∑ₖ (∑ᵢ aᵢbₖ₋ᵢ) Xᵏ

在Mathlib4中，多项式通过 `Polynomial R` 表示。
-/

-- 多项式求值的基本性质
theorem eval_add {R : Type*} [CommRing R] (p q : Polynomial R) (x : R) :
    (p + q).eval x = p.eval x + q.eval x := by
  apply eval_add

-- 多项式乘积的求值
theorem eval_mul {R : Type*} [CommRing R] (p q : Polynomial R) (x : R) :
    (p * q).eval x = p.eval x * q.eval x := by
  apply eval_mul

/-
## 第二部分：拉格朗日基多项式

对于给定的互异点 x₀, x₁, ..., xₙ，第 i 个拉格朗日基多项式定义为：

Lᵢ(X) = ∏_{j≠i} (X - xⱼ) / (xᵢ - xⱼ)

性质：
- Lᵢ(xᵢ) = 1
- Lᵢ(xⱼ) = 0 对于 j ≠ i
- deg(Lᵢ) = n
-/

variable {R : Type*} [Field R] [DecidableEq R]

-- 拉格朗日基多项式的定义
def lagrangeBasis (xs : Finset R) (i : R) (hi : i ∈ xs) : Polynomial R :=
  /- Lᵢ(X) = ∏_{j ∈ xs, j≠i} (X - j) / (i - j) -/
  ∏ j ∈ (xs.erase i), (X - C j) / C (i - j)

-- 拉格朗日基多项式的次数
theorem lagrangeBasis_degree (xs : Finset R) (i : R) (hi : i ∈ xs) :
    (lagrangeBasis xs i hi).degree ≤ (xs.card - 1 : ℕ) := by
  /- deg(Lᵢ) = |xs| - 1 -/
  unfold lagrangeBasis
  /- 每个因子 (X - j) 的次数为1，共有 |xs| - 1 个因子 -/
  have h : ∀ j ∈ xs.erase i, ((X - C j) / C (i - j) : Polynomial R).degree ≤ 1 := by
    intro j hj
    /- (X - j) / (i - j) 的次数为1（当 i ≠ j） -/
    have h_ne : i - j ≠ 0 := by
      intro h_zero
      have : i = j := by
        apply eq_of_sub_eq_zero
        exact h_zero
      have : i ≠ j := by
        apply Finset.ne_of_mem_erase hj
      contradiction
    /- 除以一个非零常数不改变次数 -/
    simp [degree_div, h_ne]
    exact degree_X_sub_C j
  /- 乘积的次数不超过次数之和 -/
  apply degree_prod_le
  intro j hj
  exact h j hj

-- 拉格朗日基多项式的关键性质：在 i 处取值为1
theorem lagrangeBasis_eval_self (xs : Finset R) (i : R) (hi : i ∈ xs) :
    (lagrangeBasis xs i hi).eval i = 1 := by
  /- Lᵢ(i) = ∏_{j≠i} (i - j) / (i - j) = ∏_{j≠i} 1 = 1 -/
  unfold lagrangeBasis
  rw [eval_prod]
  apply prod_eq_one
  intro j hj
  /- 每个因子 (i - j) / (i - j) = 1 -/
  have h_ne : i - j ≠ 0 := by
    intro h_zero
    have : i = j := by
      apply eq_of_sub_eq_zero
      exact h_zero
    have : i ≠ j := by
      apply Finset.ne_of_mem_erase hj
    contradiction
  /- 计算求值 -/
  simp [eval_div, eval_sub, eval_X, eval_C]
  field_simp [h_ne]

-- 拉格朗日基多项式的关键性质：在其他点处取值为0
theorem lagrangeBasis_eval_other (xs : Finset R) (i : R) (hi : i ∈ xs)
    (k : R) (hk : k ∈ xs) (hik : i ≠ k) :
    (lagrangeBasis xs i hi).eval k = 0 := by
  /- Lᵢ(k) = ∏_{j≠i} (k - j) / (i - j) = 0 -/
  /- 因为当 j = k 时，(k - k) = 0 -/
  unfold lagrangeBasis
  rw [eval_prod]
  /- 证明存在因子为0 -/
  apply prod_eq_zero (Finset.mem_erase.mpr ⟨hik, hk⟩)
  /- 当 j = k 时，因子为 (k - k) / (i - k) = 0 -/
  simp [eval_sub, eval_X, eval_C]

/-
## 第三部分：拉格朗日插值多项式

给定数据点 (x₀, y₀), ..., (xₙ, yₙ)，拉格朗日插值多项式为：

P(X) = ∑_{i=0}^{n} yᵢ · Lᵢ(X)

其中 Lᵢ 是拉格朗日基多项式。

性质：
- P(xᵢ) = yᵢ 对所有 i
- deg(P) ≤ n
-/

-- 拉格朗日插值多项式的定义
def lagrangeInterpolation (xs : Finset R) (ys : R → R) : Polynomial R :=
  /- P(X) = ∑_{i ∈ xs} yᵢ · Lᵢ(X) -/
  ∑ i ∈ xs, C (ys i) * lagrangeBasis xs i (by assumption)

-- 插值多项式的求值性质
theorem lagrangeInterpolation_eval (xs : Finset R) (ys : R → R) (k : R) (hk : k ∈ xs) :
    (lagrangeInterpolation xs ys).eval k = ys k := by
  /- P(xₖ) = ∑ᵢ yᵢ · Lᵢ(xₖ) = yₖ · Lₖ(xₖ) + ∑_{i≠k} yᵢ · Lᵢ(xₖ)
             = yₖ · 1 + ∑_{i≠k} yᵢ · 0 = yₖ -/
  unfold lagrangeInterpolation
  rw [eval_sum]
  /- 分离 k 项和其他项 -/
  rw [← Finset.add_sum_erase _ _ hk]
  /- k 项的贡献 -/
  have h_k : (C (ys k) * lagrangeBasis xs k (by assumption)).eval k = ys k := by
    simp [lagrangeBasis_eval_self]
  /- 其他项的贡献为0 -/
  have h_other : ∑ i ∈ xs.erase k, (C (ys i) * lagrangeBasis xs i _).eval k = 0 := by
    apply sum_eq_zero
    intro i hi
    /- 对于 i ≠ k，Lᵢ(xₖ) = 0 -/
    have hik : i ≠ k := by
      apply Finset.ne_of_mem_erase hi
    simp [lagrangeBasis_eval_other xs i _ k hk hik]
  /- 综合 -/
  rw [h_k, h_other]
  simp

-- 插值多项式的次数
theorem lagrangeInterpolation_degree (xs : Finset R) (ys : R → R) :
    (lagrangeInterpolation xs ys).degree ≤ (xs.card - 1 : ℕ) := by
  /- deg(P) ≤ maxᵢ deg(yᵢ·Lᵢ) ≤ maxᵢ deg(Lᵢ) ≤ n -/
  unfold lagrangeInterpolation
  apply degree_sum_le
  intro i hi
  /- 每个项的次数 -/
  have h : (C (ys i) * lagrangeBasis xs i _).degree ≤ (xs.card - 1 : ℕ) := by
    /- 常数乘以多项式不改变次数 -/
    apply degree_mul_le.trans
    rw [degree_C]
    split_ifs with h_zero
    · /- 如果 yᵢ = 0，则次数为 -∞ ≤ n -/
      simp
    · /- 否则次数为 deg(Lᵢ) ≤ n -/
      rw [zero_add]
      exact lagrangeBasis_degree xs i _
  exact h

/-
## 第四部分：唯一性证明

**定理**: 给定 n+1 个互异的点，次数不超过 n 的插值多项式是唯一的。

**证明**: 假设有两个次数不超过 n 的多项式 P 和 Q 都满足插值条件。
则 R = P - Q 满足 R(xᵢ) = 0 对所有 i。
但 deg(R) ≤ n，而有 n+1 个根，所以 R = 0，即 P = Q。
-/

-- 多项式的根与次数关系
theorem poly_eq_zero_of_degree_lt_card_roots {R : Type*} [Field R] [DecidableEq R]
    (p : Polynomial R) (s : Finset R) :
    (∀ x ∈ s, p.IsRoot x) → p.degree < s.card → p = 0 := by
  /- 如果 p 有 |s| 个不同的根，但 deg(p) < |s|，则 p = 0 -/
  intro h_roots h_deg
  /- 利用Mathlib4的定理 -/
  have h : p.roots.card ≤ p.natDegree := by
    apply card_roots'
  /- 所有 s 中的点都是根 -/
  have h_s : s.card ≤ p.roots.card := by
    apply le_trans _ h
    /- s ⊆ roots(p) -/
    sorry  -- 需要更多代数工具
  /- 但 deg(p) < s.card，矛盾 -/
  sorry

-- 插值多项式的唯一性
theorem lagrangeInterpolation_unique (xs : Finset R) (ys : R → R)
    (p : Polynomial R) (hp_deg : p.degree ≤ (xs.card - 1 : ℕ))
    (hp_interp : ∀ x ∈ xs, p.eval x = ys x) :
    p = lagrangeInterpolation xs ys := by
  /- 考虑差值多项式 R = p - L -/
  let R := p - lagrangeInterpolation xs ys
  /- R 在所有插值点处为0 -/
  have h_roots : ∀ x ∈ xs, R.IsRoot x := by
    intro x hx
    simp [R, IsRoot.def]
    rw [hp_interp x hx, lagrangeInterpolation_eval xs ys x hx]
    simp
  /- deg(R) ≤ max(deg(p), deg(L)) ≤ n -/
  have h_deg : R.degree ≤ (xs.card - 1 : ℕ) := by
    apply (degree_sub_le _ _).trans
    rw [max_le_iff]
    constructor
    · exact hp_deg
    · exact lagrangeInterpolation_degree xs ys
  /- 但 R 有 |xs| 个根，所以 R = 0 -/
  have h_zero : R = 0 := by
    /- 利用根的个数与次数的关系 -/
    sorry  -- 需要完成证明
  /- 因此 p = L -/
  calc
    p = R + lagrangeInterpolation xs ys := by simp [R]
    _ = 0 + lagrangeInterpolation xs ys := by rw [h_zero]
    _ = lagrangeInterpolation xs ys := by simp

/-
## 第五部分：具体示例

### 线性插值（两点插值）

给定 (x₀, y₀) 和 (x₁, y₁)，插值多项式为：
P(X) = y₀·(X-x₁)/(x₀-x₁) + y₁·(X-x₀)/(x₁-x₀)
-/

-- 线性插值示例
theorem linear_interpolation {R : Type*} [Field R] [DecidableEq R]
    (x₀ x₁ y₀ y₁ : R) (h_ne : x₀ ≠ x₁) :
    let xs : Finset R := {x₀, x₁}
    let ys : R → R := fun x => if x = x₀ then y₀ else y₁
    ∃ p : Polynomial R, p.degree ≤ 1 ∧ p.eval x₀ = y₀ ∧ p.eval x₁ = y₁ := by
  /- 构造插值多项式 -/
  let xs : Finset R := {x₀, x₁}
  let ys : R → R := fun x => if x = x₀ then y₀ else y₁
  let p := lagrangeInterpolation xs ys
  use p
  constructor
  · /- 次数不超过1 -/
    apply lagrangeInterpolation_degree
  constructor
  · /- p(x₀) = y₀ -/
    apply lagrangeInterpolation_eval
    simp [xs]
  · /- p(x₁) = y₁ -/
    apply lagrangeInterpolation_eval
    simp [xs, h_ne]

/-
## 数学意义

拉格朗日插值的重要性：

1. **存在性保证**：任何有限数据点集都可以被多项式精确拟合
2. **唯一性**：给定次数限制，插值多项式是唯一的
3. **数值计算**：为数值积分、微分方程求解等提供基础
4. **逼近理论**：多项式逼近连续函数的理论基础

## 与其他概念的关系

- **Newton插值**：另一种插值方法，使用差商
- **样条插值**：分段多项式插值
- **最小二乘拟合**：当插值条件过多时的替代方法

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `Mathlib.Algebra.Polynomial.Basic`: 多项式基础
- `Mathlib.Algebra.Polynomial.Eval`: 多项式求值
- `Mathlib.Algebra.Polynomial.Lagrange`: 拉格朗日插值
-/
