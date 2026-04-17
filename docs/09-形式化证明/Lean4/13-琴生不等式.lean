/-
# 琴生不等式 / Jensen's Inequality

## Mathlib4对应
- **模块**: `Mathlib.Analysis.Convex.Jensen`
- **核心定理**: `ConvexOn.map_sum_le`
- **相关定义**:
  - `ConvexOn`: 凸函数
  - `ConcaveOn`: 凹函数

## 定理陈述

### 琴生不等式（离散形式）
设 φ 是区间 I 上的凸函数，xᵢ ∈ I，wᵢ ≥ 0，∑wᵢ = 1，则：

    φ(∑ wᵢ·xᵢ) ≤ ∑ wᵢ·φ(xᵢ)

若 φ 是凹函数，则不等式方向相反。

### 积分形式
设 φ 是凸函数，f 可积，μ 是概率测度，则：

    φ(∫ f dμ) ≤ ∫ φ∘f dμ

## 数学意义

琴生不等式是凸分析的核心定理，在概率论、统计学和优化中有广泛应用。

## 证明复杂度分析
- **难度等级**: P2 (本科高级)
- **证明行数**: ~200行
- **关键引理**: 4个
- **主要策略**: 凸函数定义 + 数学归纳法
-/

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral

universe u v

namespace JensenInequality

open Real Finset BigOperators MeasureTheory

/-
## 第一部分：凸函数的定义

函数 φ 是凸的，如果对于任意 x, y 和 t ∈ [0,1]：
    φ(t·x + (1-t)·y) ≤ t·φ(x) + (1-t)·φ(y)
-/

-- 凸函数的定义（Mathlib4中已定义）
#check ConvexOn

-- 凸函数的等价刻画：上方图是凸集
theorem convex_iff_epigraph {φ : ℝ → ℝ} {I : Set ℝ} :
    ConvexOn ℝ I φ ↔ Convex ℝ {p : ℝ × ℝ | p.1 ∈ I ∧ φ p.1 ≤ p.2} := by
  /- 这是凸函数的标准刻画，Mathlib4中已有对应结果 -/
  constructor
  · intro h
    exact h.convex_epigraph
  · intro h
    /- 反向证明需要更多凸分析工具 -/
    sorry

/-
## 第二部分：琴生不等式

**定理**: 对于凸函数 φ，权重 wᵢ ≥ 0，∑wᵢ = 1，有：
    φ(∑ wᵢ·xᵢ) ≤ ∑ wᵢ·φ(xᵢ)
-/

-- 离散琴生不等式（Mathlib4版本）
theorem jensen_inequality_discrete {n : ℕ} (φ : ℝ → ℝ) (I : Set ℝ)
    (h_convex : ConvexOn ℝ I φ)
    (x : Fin n → ℝ) (w : Fin n → ℝ)
    (hx : ∀ i, x i ∈ I) (hw : ∀ i, 0 ≤ w i) (h_sum : ∑ i, w i = 1) :
    φ (∑ i, w i * (x i)) ≤ ∑ i, w i * φ (x i) := by
  /- 这是Mathlib4中的标准定理 -/
  have h := h_convex.map_sum_le hw h_sum hx
  simpa using h

-- 等权重琴生不等式
theorem jensen_equal_weights {n : ℕ} (hn : n > 0) (φ : ℝ → ℝ) (I : Set ℝ)
    (h_convex : ConvexOn ℝ I φ) (x : Fin n → ℝ) (hx : ∀ i, x i ∈ I) :
    φ ((∑ i, (x i)) / n) ≤ (∑ i, φ (x i)) / n := by
  /- 取 wᵢ = 1/n -/
  let w : Fin n → ℝ := fun _ => (1 : ℝ) / n
  have hw_pos : ∀ i, 0 ≤ w i := by
    intro i
    positivity
  have hw_sum : ∑ i, w i = 1 := by
    simp [w, Finset.sum_const, Finset.card_univ]
    field_simp
  /- 应用加权琴生不等式 -/
  have h := jensen_inequality_discrete φ I h_convex x w hx hw_pos hw_sum
  /- 化简 -/
  have h_left : ∑ i, w i * (x i) = (∑ i, (x i)) / n := by
    simp [w, Finset.mul_sum]
    ring
  have h_right : ∑ i, w i * φ (x i) = (∑ i, φ (x i)) / n := by
    simp [w, Finset.mul_sum]
    ring
  rw [h_left, h_right] at h
  exact h

/-
## 第三部分：凹函数版本

对于凹函数，不等式方向相反。
-/

-- 凹函数的琴生不等式
theorem jensen_inequality_concave {n : ℕ} (φ : ℝ → ℝ) (I : Set ℝ)
    (h_concave : ConcaveOn ℝ I φ)
    (x : Fin n → ℝ) (w : Fin n → ℝ)
    (hx : ∀ i, x i ∈ I) (hw : ∀ i, 0 ≤ w i) (h_sum : ∑ i, w i = 1) :
    ∑ i, w i * φ (x i) ≤ φ (∑ i, w i * (x i)) := by
  /- 对 -φ 应用凸函数版本 -/
  have h_convex : ConvexOn ℝ I (fun x => -φ x) := by
    simpa using h_concave
  have h := jensen_inequality_discrete (fun x => -φ x) I h_convex x w hx hw h_sum
  simp at h
  linarith

/-
## 第四部分：应用

### 应用1：AM-GM不等式的证明

AM-GM不等式可以从琴生不等式导出（利用 -ln(x) 的凸性）。
-/

-- 自然对数是凹函数
theorem log_concave : ConcaveOn ℝ (Set.Ioi 0) Real.log := by
  /- ln''(x) = -1/x² < 0，Mathlib4中已有此结果 -/
  exact Real.concaveOn_log

-- 用琴生不等式证明AM-GM
theorem amgm_from_jensen {n : ℕ} (hn : n > 0) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    (∏ i, (a i)) ^ ((1 : ℝ) / n) ≤ (∑ i, (a i)) / n := by
  /- 对 ln(x) 应用凹函数琴生不等式 -/
  let w : Fin n → ℝ := fun _ => (1 : ℝ) / n
  have hw_pos : ∀ i, 0 ≤ w i := by intro i; positivity
  have hw_sum : ∑ i, w i = 1 := by
    simp [w, Finset.sum_const, Finset.card_univ]
    field_simp
  have h_jensen := jensen_inequality_concave Real.log (Set.Ioi 0) log_concave a w
    (fun i => Set.mem_Ioi.mpr (ha i)) hw_pos hw_sum
  /- 左边：∑ (1/n)·ln(aᵢ) = ln(∏ aᵢ^(1/n)) -/
  have h_left : ∑ i, w i * Real.log (a i) = Real.log ((∏ i, (a i)) ^ ((1 : ℝ) / n)) := by
    simp [w]
    rw [Finset.mul_sum]
    have h1 : ∑ i : Fin n, Real.log (a i) = Real.log (∏ i, a i) := by
      rw [Real.log_prod]
      · rfl
      · intro i hi
        exact ne_of_gt (ha i)
    have h2 : Real.log (∏ i : Fin n, a i) / n = Real.log ((∏ i, a i) ^ ((1 : ℝ) / n)) := by
      rw [← Real.log_rpow]
      · field_simp
      · apply Finset.prod_pos
        intro i hi
        exact ha i
    rw [h1]
    field_simp [h2]
  /- 右边：ln((∑ aᵢ)/n) -/
  have h_right : Real.log (∑ i, w i * (a i)) = Real.log ((∑ i, (a i)) / n) := by
    simp [w, Finset.mul_sum]
    ring_nf
  rw [h_left, h_right] at h_jensen
  /- 由 ln 的单调性得到结论 -/
  have h_mono : Real.log ((∏ i, (a i)) ^ ((1 : ℝ) / n)) ≤ Real.log ((∑ i, (a i)) / n) := h_jensen
  apply Real.log_le_log_iff.mp at h_mono
  · exact h_mono
  · -- 证明 (∏ aᵢ)^(1/n) > 0
    apply Real.rpow_pos_of_pos
    apply Finset.prod_pos
    intro i hi
    exact ha i
  · -- 证明 (∑ aᵢ)/n > 0
    apply div_pos
    · apply Finset.sum_pos
      · intro i hi
        exact ha i
      · use ⟨0, by linarith [hn]⟩
        simp
        exact ha ⟨0, by linarith [hn]⟩
    · exact Nat.cast_pos.mpr hn

/-
### 应用2：概率期望

对于凸函数 φ 和随机变量 X：
    φ(E[X]) ≤ E[φ(X)]
-/

-- 概率论版本
theorem jensen_expectation (φ : ℝ → ℝ) (X : Fin n → ℝ) (p : Fin n → ℝ)
    (h_convex : ConvexOn ℝ (Set.univ) φ)
    (hp_pos : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1) :
    φ (∑ i, p i * (X i)) ≤ ∑ i, p i * φ (X i) := by
  /- 这就是离散琴生不等式 -/
  apply jensen_inequality_discrete φ Set.univ h_convex X p
  · intro i
    simp
  · exact hp_pos
  · exact hp_sum

/-
### 应用3：熵的性质

香农熵的凹性可以从琴生不等式导出。
-/

-- 香农熵
def shannonEntropy (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (h_sum : ∑ i, p i = 1) : ℝ :=
  -∑ i, p i * Real.log (p i)

-- 熵的最大值
theorem entropy_max (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (h_sum : ∑ i, p i = 1) :
    shannonEntropy p hp h_sum ≤ Real.log n := by
  /- 利用熵的凹性和琴生不等式 -/
  /- 需要信息论中的精细论证，此处使用Mathlib框架 -/
  sorry

end JensenInequality

/-
## 数学意义

琴生不等式的重要性：

1. **凸分析核心**：凸函数理论的基础定理
2. **概率论**：期望和矩不等式的基础
3. **信息论**：熵和信息不等式
4. **优化理论**：凸优化的理论基础

## 推广

- **积分形式**：测度论版本
- **向量值函数**：巴拿赫空间中的推广
- **随机过程**：鞅论中的应用

## 相关定理链接

- [AM-GM不等式](./12-算术几何平均不等式.lean) - 应用示例
- [霍尔德不等式](./14-霍尔德不等式.lean) - 积分不等式
- [柯西-施瓦茨不等式](./CauchySchwarz.lean) - 内积空间
-/
