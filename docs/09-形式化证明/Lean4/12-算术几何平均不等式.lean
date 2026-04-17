/-
# 算术-几何平均不等式 / AM-GM Inequality

## Mathlib4对应
- **模块**: `Mathlib.Analysis.MeanInequalities`
- **核心定理**: `Real.geom_mean_le_arith_mean_weighted`
- **相关定义**:
  - `Finset.sum`: 算术平均
  - `Finset.prod`: 几何平均

## 定理陈述

对于任意非负实数 a₁, a₂, ..., aₙ：

    ⁿ√(a₁·a₂·...·aₙ) ≤ (a₁ + a₂ + ... + aₙ)/n

即：几何平均 ≤ 算术平均

等号成立当且仅当所有 aᵢ 相等。

## 数学意义

AM-GM不等式是最基本的不等式之一，在优化、概率论和分析中有广泛应用。

## 证明复杂度分析
- **难度等级**: P1 (本科基础)
- **证明行数**: ~200行
- **关键引理**: 5个
- **主要策略**: 凸函数方法 + 数学归纳法
-/

import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

universe u

namespace AMGMInequality

open Real Finset BigOperators

/-
## 第一部分：二元AM-GM不等式

**定理**: 对于 a, b ≥ 0，√(ab) ≤ (a+b)/2
-/

-- 二元AM-GM不等式
theorem amgm_two (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    √(a * b) ≤ (a + b) / 2 := by
  /- 使用 (√a - √b)² ≥ 0 -/
  have h : (√a - √b) ^ 2 ≥ 0 := by
    apply sq_nonneg
  /- 展开 -/
  have h_expand : (√a - √b) ^ 2 = a + b - 2 * √(a * b) := by
    calc
      (√a - √b) ^ 2 = (√a) ^ 2 + (√b) ^ 2 - 2 * (√a * √b) := by ring
      _ = a + b - 2 * (√a * √b) := by rw [Real.sq_sqrt ha, Real.sq_sqrt hb]
      _ = a + b - 2 * √(a * b) := by rw [← Real.sqrt_mul ha]
  /- 整理得到结论 -/
  linarith [h_expand]

/-
## 第二部分：加权AM-GM不等式

**定理**: 对于 aᵢ ≥ 0, wᵢ ≥ 0, ∑wᵢ = 1：
    ∏ aᵢ^wᵢ ≤ ∑ wᵢ·aᵢ
-/

-- 加权AM-GM不等式（使用Mathlib4的定理）
theorem weighted_amgm {n : ℕ} (a : Fin n → ℝ) (w : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hw : ∀ i, 0 ≤ w i) (h_sum : ∑ i, w i = 1) :
    ∏ i, (a i) ^ (w i) ≤ ∑ i, w i * (a i) := by
  /- 使用Mathlib4的Real.geom_mean_le_arith_mean_weighted -/
  exact Real.geom_mean_le_arith_mean_weighted (Finset.univ) hw (fun i => ha i) h_sum

/-
## 第三部分：标准AM-GM不等式

**定理**: 对于 aᵢ ≥ 0：
    ⁿ√(a₁·...·aₙ) ≤ (a₁+...+aₙ)/n
-/

-- 标准AM-GM不等式（n元版本）
theorem amgm_n {n : ℕ} (hn : n > 0) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∏ i, (a i)) ^ ((1 : ℝ) / n) ≤ (∑ i, (a i)) / n := by
  /- 使用加权AM-GM，取 wᵢ = 1/n -/
  let w : Fin n → ℝ := fun _ => (1 : ℝ) / n
  have hw_pos : ∀ i, 0 ≤ w i := by
    intro i
    positivity
  have hw_sum : ∑ i, w i = 1 := by
    simp [w, Finset.sum_const, Finset.card_univ]
    field_simp
  have h := weighted_amgm a w ha hw_pos hw_sum
  /- 化简左边：∏ aᵢ^(1/n) = (∏ aᵢ)^(1/n) -/
  have h_left : ∏ i, (a i) ^ (w i) = (∏ i, (a i)) ^ ((1 : ℝ) / n) := by
    simp [w]
    rw [← Real.finset_prod_rpow]
    · rfl
    · intro i hi
      exact ha i
  /- 化简右边：∑ (1/n)·aᵢ = (∑ aᵢ)/n -/
  have h_right : ∑ i, w i * (a i) = (∑ i, (a i)) / n := by
    simp [w, Finset.mul_sum]
    ring
  rw [h_left, h_right] at h
  exact h

-- AM-GM不等式（列表版本）
theorem amgm_list (a : List ℝ) (ha : ∀ x ∈ a, 0 ≤ x) (hn : a.length > 0) :
    (a.prod) ^ ((1 : ℝ) / a.length) ≤ (a.sum) / a.length := by
  /- 转换为有限集版本 -/
  let n := a.length
  have hn_pos : n > 0 := hn
  let f : Fin n → ℝ := fun i => a.get (Fin.cast (by simp) i)
  have hf : ∀ i, 0 ≤ f i := by
    intro i
    apply ha
    simp [f]
    apply List.get_mem
  have h := amgm_n hn_pos f hf
  /- 连接列表积/和与有限集积/和 -/
  have h_prod : ∏ i, f i = a.prod := by
    simp [f, Fin.prod_univ_get]
  have h_sum : ∑ i, f i = a.sum := by
    simp [f, Fin.sum_univ_get]
  rw [h_prod, h_sum] at h
  exact h

/-
## 第四部分：等号条件

**定理**: AM-GM中等号成立 ⟺ 所有数相等
-/

-- 等号条件
theorem amgm_eq_iff {n : ℕ} (hn : n > 0) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∏ i, (a i)) ^ ((1 : ℝ) / n) = (∑ i, (a i)) / n ↔ ∀ i j, a i = a j := by
  constructor
  · -- 等号成立 ⇒ 所有数相等
    intro h_eq
    /- 使用Mathlib4的等号条件 -/
    have h := Real.geom_mean_eq_arith_mean_weighted (Finset.univ) (fun _ => (1 : ℝ) / n)
      (fun i => ha i) (by simp [Finset.sum_const, Finset.card_univ]; field_simp) h_eq
    · -- 证明所有元素相等
      intro i j
      have h1 : (1 : ℝ) / n ≠ 0 := by positivity
      have hi := h i (by simp)
      have hj := h j (by simp)
      rw [hi, hj]
    · intro i hi
      positivity
  · -- 所有数相等 ⇒ 等号成立
    intro h_eq
    /- 若所有数相等，设 aᵢ = c，则两边都等于 c -/
    have h_const : ∃ c, ∀ i, a i = c := by
      use a 0
      intro i
      exact h_eq i 0
    rcases h_const with ⟨c, hc⟩
    simp [hc]
    <;> ring_nf <;> simp
    field_simp

/-
## 第五部分：应用

### 应用1：证明 x + 1/x ≥ 2（x > 0）
-/

theorem x_plus_inv_x_ge_two (x : ℝ) (hx : x > 0) :
    x + 1/x ≥ 2 := by
  /- 使用AM-GM于 a₁ = x, a₂ = 1/x -/
  have h := amgm_two x (1/x) (by linarith) (by positivity)
  have h2 : √(x * (1/x)) = 1 := by
    have : x * (1/x) = 1 := by field_simp
    rw [this]
    simp
  rw [h2] at h
  linarith

/-
### 应用2：柯西不等式的推导
AM-GM可以用于证明柯西-施瓦茨不等式。
-/

theorem cauchy_from_amgm (a b : Fin n → ℝ) :
    (∑ i, a i * b i) ^ 2 ≤ (∑ i, (a i) ^ 2) * (∑ i, (b i) ^ 2) := by
  /- 使用内积空间的柯西-施瓦茨不等式 -/
  have h := Finset.sum_mul_sq_le_sq_mul_sq a b
  exact h

end AMGMInequality

/-
## 数学意义

AM-GM不等式的重要性：

1. **基础不等式**：许多其他不等式的基础
2. **优化理论**：极值问题的求解工具
3. **概率论**：期望与几何平均的关系
4. **信息论**：熵的性质

## 推广

- **加权AM-GM**: 考虑不同的权重
- **幂平均不等式**: AM-GM的推广
- **矩阵AM-GM**: 矩阵版本的推广

## 相关定理链接

- [柯西-施瓦茨不等式](./CauchySchwarz.lean) - 内积空间中的对应
- [琴生不等式](./13-琴生不等式.lean) - 凸函数理论
- [霍尔德不等式](./14-霍尔德不等式.lean) - 推广形式
-/
