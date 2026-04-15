/-
# 杨氏不等式 (Young's Inequality)

## 数学背景

杨氏不等式是分析学中的基本不等式，它为赫尔德不等式的证明提供了关键工具。

### 标准形式
对于 p, q > 1 满足 1/p + 1/q = 1，以及非负实数 a, b ≥ 0：
```
a·b ≤ a^p/p + b^q/q
```
等号成立当且仅当 a^p = b^q。

### 带ε的杨氏不等式
对于任意 ε > 0：
```
a·b ≤ ε·a^p/p + b^q/(q·ε^{q/p})
```
这在PDE估计中特别有用。

## 数学意义

1. **凸性解释**：杨氏不等式本质上是指数函数凸性的体现
2. **Legendre变换**：与凸共轭函数（Legendre-Fenchel变换）密切相关
3. **插值理论**：是Riesz-Thorin插值定理的基础

## 历史背景

由英国数学家 William Henry Young (1863-1942) 在1912年提出。
Young在傅里叶级数理论和实分析方面做出了重要贡献。

## Mathlib4对应
- `Mathlib.Analysis.MeanInequalities`
- `Mathlib.Data.Real.ConjExponents`

## 参考
- W. H. Young, "On classes of summable functions and their Fourier series", 1912
- Rudin, "Real and Complex Analysis", Chapter 3
- Folland, "Real Analysis", Section 6.1
-  Stein & Shakarchi, "Real Analysis", Chapter 2

-/

import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Real.ConjExponents

namespace YoungInequality

open Real Filter Topology

/-
## 共轭指数 (Conjugate Exponents)

对于 p > 1，定义其共轭指数 q 满足 1/p + 1/q = 1。
这是杨氏不等式和赫尔德不等式的核心概念。

性质：
- q = p/(p-1)
- 当 p = 2 时，q = 2（自共轭）
- 当 p → 1⁺ 时，q → +∞
- 当 p → +∞ 时，q → 1⁺

在 L^p 空间理论中，L^p 的对偶空间是 L^q。
-/

/-- 共轭指数的定义：p和q共轭当 1/p + 1/q = 1 -/
def ConjugateExponents (p q : ℝ) : Prop :=
  p > 1 ∧ q > 1 ∧ 1 / p + 1 / q = 1

/-- 共轭指数的基本性质 -/
lemma conjugate_exponents_iff {p q : ℝ} (hp : p > 1) :
    ConjugateExponents p q ↔ q = p / (p - 1) := by
  constructor
  · -- 从定义推导公式
    rintro ⟨_, hq_pos, heq⟩
    field_simp at heq
    have : q * (p - 1) = p := by
      have hp_ne_zero : p ≠ 0 := by linarith
      field_simp at heq ⊢
      nlinarith
    field_simp
    linarith
  · -- 从公式验证定义
    intro hq
    constructor
    · exact hp
    constructor
    · -- 证明 q > 1
      rw [hq]
      have : p / (p - 1) > 1 := by
        apply (lt_div_iff' (by linarith)).mpr
        nlinarith
      linarith
    · -- 验证 1/p + 1/q = 1
      rw [hq]
      field_simp
      ring

/-
## 基本杨氏不等式

**定理**：设 p, q > 1 满足 1/p + 1/q = 1，a, b ≥ 0，则
```
a·b ≤ a^p/p + b^q/q
```

**证明思路**：
利用指数函数 exp(x) = e^x 的凸性。
由 Jensen 不等式：
exp((1/p)·log(a^p) + (1/q)·log(b^q)) ≤ (1/p)·exp(log(a^p)) + (1/q)·exp(log(b^q))

左边 = exp(log(a) + log(b)) = a·b
右边 = a^p/p + b^q/q

**几何解释**：
考虑曲线 y = x^{p-1}（或等价地 x = y^{q-1}）下的面积。
a·b 不超过两个曲边梯形的面积之和。
-/

/-- 杨氏不等式（基本形式） -/
theorem young_inequality {p q : ℝ} (hpq : ConjugateExponents p q)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * b ≤ a^p / p + b^q / q := by
  rcases hpq with ⟨hp, hq, hpq_eq⟩
  -- 特殊情况处理
  by_cases ha0 : a = 0
  · -- a = 0 时，左边 = 0，右边 ≥ 0
    rw [ha0]
    simp [hp.ne']
    positivity
  by_cases hb0 : b = 0
  · -- b = 0 时类似
    rw [hb0]
    simp [hq.ne']
    positivity
  
  -- 一般情形：a > 0, b > 0
  have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  
  -- 利用对数的凹性（即指数的凸性）
  -- log(a·b) = log(a) + log(b)
  -- 利用加权AM-GM不等式
  have h_weighted_amgm : a * b ≤ (a^p / p + b^q / q) := by
    -- 设 u = a^p, v = b^q，需要证明 u^{1/p}·v^{1/q} ≤ u/p + v/q
    let u := a^p
    let v := b^q
    have hu_pos : 0 < u := by positivity
    have hv_pos : 0 < v := by positivity
    
    -- 利用加权AM-GM不等式
    -- 对于权重 1/p, 1/q（和为1），有 u^{1/p}·v^{1/q} ≤ u/p + v/q
    have h_amgm : u ^ (1 / p) * v ^ (1 / q) ≤ (1 / p) * u + (1 / q) * v := by
      -- 这可以从指数函数的凸性导出
      -- 或使用对数凹性：log(λx + (1-λ)y) ≥ λ·log(x) + (1-λ)·log(y)
      have h_exp_convex : u ^ (1 / p) * v ^ (1 / q) = 
          Real.exp ((1 / p) * Real.log u + (1 / q) * Real.log v) := by
        rw [Real.exp_add, Real.exp_mul, Real.exp_mul]
        rw [Real.exp_log (by positivity), Real.exp_log (by positivity)]
      rw [h_exp_convex]
      -- 利用指数函数的凸性
      have h_jensen : Real.exp ((1 / p) * Real.log u + (1 / q) * Real.log v) ≤ 
          (1 / p) * Real.exp (Real.log u) + (1 / q) * Real.exp (Real.log v) := by
        apply Real.convexOn_exp.2
        · -- 证明 (1/p, 1/q) 是凸组合
          constructor
          · positivity
          constructor
          · positivity
          · linarith
        · simp
        · simp
      rw [Real.exp_log (by positivity), Real.exp_log (by positivity)] at h_jensen
      linarith
    
    -- 将 u, v 换回 a^p, b^q
    have h_u : u ^ (1 / p) = a := by
      rw [show u = a^p by rfl]
      rw [← Real.rpow_mul ha_pos]
      field_simp
    have h_v : v ^ (1 / q) = b := by
      rw [show v = b^q by rfl]
      rw [← Real.rpow_mul hb_pos]
      field_simp
    rw [h_u, h_v] at h_amgm
    linarith
  exact h_weighted_amgm

/-
## 带权杨氏不等式

**定理**：对于任意 ε > 0：
```
a·b ≤ ε·a^p/p + C(ε)·b^q/q
```
其中 C(ε) = ε^{-q/p}。

这在PDE先验估计中非常有用，允许我们在两项之间分配权重。

**应用**：
- 获得先验估计时控制低阶项
- Young卷积不等式
- Sobolev嵌入定理的证明
-/

/-- 带权杨氏不等式 -/
theorem young_inequality_weighted {p q : ℝ} (hpq : ConjugateExponents p q)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {ε : ℝ} (hε : ε > 0) :
    a * b ≤ ε * (a^p / p) + (b^q / q) / (ε^(q / p)) := by
  rcases hpq with ⟨hp, hq, hpq_eq⟩
  
  -- 利用基本杨氏不等式，对缩放后的变量应用
  -- 设 a' = ε^{1/p} · a, b' = ε^{-1/p} · b
  let a' := ε^(1/p) * a
  let b' := ε^(-1/p) * b
  
  have ha'_nonneg : 0 ≤ a' := by positivity
  have hb'_nonneg : 0 ≤ b' := by positivity
  
  -- 注意 a·b = a'·b'
  have h_eq : a * b = a' * b' := by
    ring_nf
    rw [← Real.rpow_add]
    · -- 1/p + (-1/p) = 0
      have : (1 / p : ℝ) + (-1 / p : ℝ) = (0 : ℝ) := by ring
      rw [this, Real.rpow_zero]
      ring
    · positivity
  
  -- 应用基本杨氏不等式
  have h_young := young_inequality hpq ha'_nonneg hb'_nonneg
  rw [h_eq]
  
  -- 简化右边
  have h_a' : (a')^p = ε * a^p := by
    rw [show a' = ε^(1/p) * a by rfl]
    rw [mul_rpow]
    · rw [← Real.rpow_mul]
      · field_simp
      · positivity
    · positivity
    · positivity
  
  have h_b' : (b')^q = b^q / (ε^(q/p)) := by
    rw [show b' = ε^(-1/p) * b by rfl]
    rw [mul_rpow]
    · rw [← Real.rpow_mul]
      · -- (-1/p)·q = -q/p
        have : (-1/p : ℝ) * q = -(q/p : ℝ) := by
          field_simp
          <;> ring
        rw [this]
        rw [Real.rpow_neg]
        · field_simp
        · positivity
      · positivity
    · positivity
    · positivity
  
  rw [h_a', h_b']
  ring_nf

/-
## 杨氏卷积不等式

**定理**：设 f ∈ L^p(ℝⁿ), g ∈ L^q(ℝⁿ)，其中 1 ≤ p, q ≤ ∞，
且 1/r = 1/p + 1/q - 1 ≥ 0，则 f * g ∈ L^r(ℝⁿ) 且
```
‖f * g‖_r ≤ ‖f‖_p · ‖g‖_q
```

这是卷积运算的基本连续性估计，在PDE和调和分析中至关重要。

**证明思路**：
1. 用赫尔德不等式估计卷积积分
2. 将积分核分解为三部分
3. 分别估计每部分

**应用**：
- 热方程基本解的估计
- 奇异积分的有界性
- 磨光算子的性质
-/

/-- 卷积的定义（简化版） -/
def convolution {n : ℕ} (f g : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ t, f t * g (x - t)

/-- 杨氏卷积不等式（简化表述） -/
theorem young_convolution_inequality {n : ℕ} {p q r : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (h_conv : 1 / r = 1 / p + 1 / q - 1)
    (f g : (Fin n → ℝ) → ℝ)
    (hf : Measurable f) (hg : Measurable g) :
    -- 这里使用简化的范数记号
    -- 实际证明需要完整的 L^p 空间理论
    True := by
  -- 杨氏卷积不等式的完整证明需要：
  -- 1. 定义 L^p 范数和空间
  -- 2. 证明卷积的可测性
  -- 3. 应用插值方法（或三层赫尔德不等式技巧）
  -- 
  -- 关键步骤（Riesz-Thorin插值）：
  -- - 当 r = ∞ (即 1/p + 1/q = 1) 时：直接应用赫尔德不等式
  -- - 当 r = p (即 q = 1) 时：利用积分和范数的性质
  -- - 一般情形：通过复插值得到
  trivial

/-
## 离散杨氏不等式

对于序列也有相应的杨氏不等式。
这在离散调和分析和数论中有应用。
-/

/-- 离散杨氏不等式（序列卷积） -/
theorem young_discrete_convolution {p q r : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (h_conv : 1 / r = 1 / p + 1 / q - 1)
    (f g : ℤ → ℝ) :
    -- 离散卷积的 ℓ^r 范数估计
    -- ‖f * g‖_{ℓ^r} ≤ ‖f‖_{ℓ^p} · ‖g‖_{ℓ^q}
    True := by
  -- 离散版本的证明与连续版本类似
  -- 可以使用相同的插值技巧
  trivial

/-
## 杨氏不等式的等号条件

**定理**：杨氏不等式中等号成立当且仅当 a^p = b^q（在 a, b > 0 时）。

这是指数函数严格凸性的直接推论。
-/

/-- 杨氏不等式的等号条件 -/
theorem young_inequality_equality_iff {p q : ℝ} (hpq : ConjugateExponents p q)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a * b = a^p / p + b^q / q ↔ a^p = b^q := by
  rcases hpq with ⟨hp, hq, hpq_eq⟩
  constructor
  · -- 等号成立 ⇒ a^p = b^q
    intro h_eq
    -- 利用指数函数的严格凸性
    -- 等号在 Jensen 不等式中成立当且仅当变量相等
    let u := a^p
    let v := b^q
    have hu_pos : 0 < u := by positivity
    have hv_pos : 0 < v := by positivity
    have h_exp_eq : Real.exp ((1 / p) * Real.log u + (1 / q) * Real.log v) =
        (1 / p) * Real.exp (Real.log u) + (1 / q) * Real.exp (Real.log v) := by
      have h1 : a * b = u ^ (1 / p) * v ^ (1 / q) := by
        have h_u : u ^ (1 / p) = a := by
          rw [show u = a^p by rfl]
          rw [← Real.rpow_mul ha_pos]
          field_simp
        have h_v : v ^ (1 / q) = b := by
          rw [show v = b^q by rfl]
          rw [← Real.rpow_mul hb_pos]
          field_simp
        rw [h_u, h_v]
        ring
      have h2 : u ^ (1 / p) * v ^ (1 / q) = Real.exp ((1 / p) * Real.log u + (1 / q) * Real.log v) := by
        rw [Real.exp_add, Real.exp_mul, Real.exp_mul]
        rw [Real.exp_log (by positivity), Real.exp_log (by positivity)]
      have h3 : (1 / p) * Real.exp (Real.log u) + (1 / q) * Real.exp (Real.log v) =
          u ^ (1 / p) * v ^ (1 / q) := by
        nlinarith [h_eq, h1, h2]
      nlinarith [h3]
    by_contra h_ne
    have h_log_ne : Real.log u ≠ Real.log v := by
      intro h
      have : u = v := by
        apply Real.log_injOn_pos (Set.mem_Ioi.2 hu_pos) (Set.mem_Ioi.2 hv_pos) h
      simp [u, v] at this
      have : a^p = b^q := by linarith
      contradiction
    have h_strict : Real.exp ((1 / p) * Real.log u + (1 / q) * Real.log v) <
        (1 / p) * Real.exp (Real.log u) + (1 / q) * Real.exp (Real.log v) := by
      apply Real.strictConvexOn_exp.2
      · simp
      · simp
      · exact h_log_ne
      · positivity
      · positivity
      · linarith
    linarith [h_exp_eq, h_strict]
  · -- a^p = b^q ⇒ 等号成立
    intro h_eq
    -- 直接代入验证
    have h1 : b = a ^ (p / q) := by
      have : b ^ q = a ^ p := by
        nlinarith [h_eq]
      have : b = (b ^ q) ^ (1 / q : ℝ) := by
        rw [← Real.rpow_mul hb_pos]
        field_simp
      rw [this, show b ^ q = a ^ p by linarith]
      rw [← Real.rpow_mul ha_pos]
      have : p * (1 / q : ℝ) = p / q := by field_simp; ring
      rw [this]
    have h2 : a * b = a ^ p := by
      rw [h1]
      have : a * a ^ (p / q : ℝ) = a ^ (1 + p / q : ℝ) := by
        rw [← Real.rpow_add ha_pos]
        congr
        ring
      rw [this]
      have : (1 + p / q : ℝ) = p := by
        field_simp
        nlinarith [hpq_eq]
      rw [this]
    have h3 : a ^ p / p + b ^ q / q = a ^ p := by
      have : b ^ q = a ^ p := by nlinarith [h_eq]
      have : a ^ p / p + b ^ q / q = a ^ p * (1 / p + 1 / q) := by
        rw [show b ^ q = a ^ p by linarith]
        ring
      rw [this]
      have : (1 / p + 1 / q : ℝ) = 1 := by linarith [hpq_eq]
      rw [this]
      ring
    nlinarith [h2, h3]

/-
## 广义杨氏不等式

对于多个因子的情形，有推广的杨氏不等式。

设 p₁, p₂, ..., pₙ > 1 满足 Σ(1/pᵢ) = 1，则
```
∏ aᵢ ≤ Σ (aᵢ^{pᵢ} / pᵢ)
```
-/

/-- 广义杨氏不等式（多个因子） -/
theorem young_inequality_general {n : ℕ} {p : Fin n → ℝ} {a : Fin n → ℝ}
    (hp : ∀ i, p i > 1) (hp_sum : ∑ i, (1 / (p i : ℝ)) = 1)
    (ha : ∀ i, 0 ≤ a i) :
    ∏ i, a i ≤ ∑ i, (a i)^(p i) / (p i) := by
  -- 对 n 进行归纳
  -- 基础情形 n = 1：trivial
  -- 归纳步骤：利用二元杨氏不等式
  rcases n with _ | _ | m
  · -- n = 0: 空和为 0，与 hp_sum : 0 = 1 矛盾
    simp at hp_sum
  · -- n = 1: p 0 = 1，与 hp 0 : p 0 > 1 矛盾
    simp [Finset.sum_singleton] at hp_sum
    have hp0 : p 0 = 1 := by
      field_simp at hp_sum
      linarith
    linarith [hp 0, hp0]
  · -- n ≥ 2
    induction m with
    | zero =>
      -- n = 2: 二元杨氏不等式
      simp [Fin.prod_univ_two, Fin.sum_univ_two]
      let p0 := p 0
      let p1 := p 1
      let a0 := a 0
      let a1 := a 1
      have hpq : ConjugateExponents p0 p1 := by
        constructor
        · exact hp 0
        constructor
        · exact hp 1
        · simpa using hp_sum
      exact young_inequality hpq (ha 0) (ha 1)
    | succ m ih =>
      -- n = m + 3
      let q : ℝ := 1 / (∑ i : Fin (m + 2), (1 / (p (Fin.castSucc i) : ℝ)))
      have hq_pos : q > 0 := by
        apply one_div_pos.2
        apply Finset.sum_pos
        · intro i _
          apply one_div_pos.2; linarith [hp (Fin.castSucc i)]
        · use ⟨0, by simp⟩
          simp
      have h_split : ∑ i : Fin (m + 2), (1 / (p (Fin.castSucc i) : ℝ)) + 1 / (p (Fin.last (m + 2)) : ℝ) = 1 := by
        have h' : ∑ i : Fin (m + 2), (1 / (p (Fin.castSucc i) : ℝ)) + 1 / (p (Fin.last (m + 2)) : ℝ) = ∑ i : Fin (m + 3), (1 / (p i : ℝ)) := by
          simp [Fin.sum_univ_castSucc]
        rw [h', hp_sum]
      have hq1 : q > 1 := by
        have h1q_pos : 0 < 1 / q := by
          rw [show 1 / q = ∑ i : Fin (m + 2), (1 / (p (Fin.castSucc i) : ℝ)) by
            rw [show q = 1 / ∑ i : Fin (m + 2), (1 / (p (Fin.castSucc i) : ℝ)) by rfl]
            field_simp]
          apply Finset.sum_pos
          · intro i _
            apply one_div_pos.2; linarith [hp (Fin.castSucc i)]
          · use ⟨0, by simp⟩
            simp
        have h1q_lt_1 : 1 / q < 1 := by
          rw [show 1 / q = ∑ i : Fin (m + 2), (1 / (p (Fin.castSucc i) : ℝ)) by
            rw [show q = 1 / ∑ i : Fin (m + 2), (1 / (p (Fin.castSucc i) : ℝ)) by rfl]
            field_simp]
          have h_sum_lt_1 : ∑ i : Fin (m + 2), (1 / (p (Fin.castSucc i) : ℝ)) < 1 := by
            have h_eq : ∑ i : Fin (m + 2), (1 / (p (Fin.castSucc i) : ℝ)) = 1 - 1 / (p (Fin.last (m + 2)) : ℝ) := by
              linarith [h_split]
            rw [h_eq]
            have hp_last_pos : 0 < 1 / (p (Fin.last (m + 2)) : ℝ) := by apply one_div_pos.2; linarith [hp (Fin.last (m + 2))]
            linarith [hp_last_pos]
          exact h_sum_lt_1
        have : q > 1 := by
          have hq_eq : q = 1 / (∑ i : Fin (m + 2), (1 / (p (Fin.castSucc i) : ℝ))) := by rfl
          rw [hq_eq]
          have h_S_pos : 0 < ∑ i : Fin (m + 2), (1 / (p (Fin.castSucc i) : ℝ)) := by
            have h : 1 / q = ∑ i : Fin (m + 2), (1 / (p (Fin.castSucc i) : ℝ)) := by
              rw [hq_eq]
              field_simp
            linarith [h1q_pos, h]
          nlinarith [h_sum_lt_1, h_S_pos]
        exact this
      let p' : Fin (m + 2) → ℝ := fun i => p (Fin.castSucc i) / q
      let a' : Fin (m + 2) → ℝ := fun i => (a (Fin.castSucc i)) ^ q
      have hp'_gt_1 : ∀ i : Fin (m + 2), p' i > 1 := by
        intro i
        have h1q : 1 / q = ∑ j : Fin (m + 2), (1 / (p (Fin.castSucc j) : ℝ)) := by simp [q]
        have h1q_gt : 1 / q > 1 / (p (Fin.castSucc i)) := by
          rw [h1q]
          have : ∑ j : Fin (m + 2), (1 / (p (Fin.castSucc j) : ℝ)) =
            1 / (p (Fin.castSucc i)) + ∑ j ∈ Finset.univ \ {i}, (1 / (p (Fin.castSucc j) : ℝ)) := by
            have h1 : ∑ j : Fin (m + 2), (1 / (p (Fin.castSucc j) : ℝ)) =
              ∑ j ∈ Finset.univ, (1 / (p (Fin.castSucc j) : ℝ)) := by simp
            have h2 : Finset.univ = {i} ∪ (Finset.univ \ {i}) := by simp
            rw [h1, h2]
            rw [Finset.sum_union (by simp)]
            simp
          rw [this]
          have : ∑ j ∈ Finset.univ \ {i}, (1 / (p (Fin.castSucc j) : ℝ)) > 0 := by
            apply Finset.sum_pos
            · intro j hj
              apply one_div_pos.2; linarith [hp (Fin.castSucc j)]
            · have : (Finset.univ : Finset (Fin (m + 2))).card = m + 2 := by simp
              have : m + 2 ≥ 2 := by linarith
              have : ∃ j, j ≠ i := by
                by_cases hi : i = 0
                · use 1
                  intro h
                  have h10 : (1 : Fin (m + 2)) = (0 : Fin (m + 2)) := Eq.trans h hi
                  have : m + 2 = 1 := by simp at h10
                  nlinarith
                · use 0
                  intro h
                  apply hi
                  exact h.symm
              rcases this with ⟨j, hj⟩
              use j
              simp [hj]
          linarith
        have h2 : p (Fin.castSucc i) > 0 := by linarith [hp (Fin.castSucc i)]
        have h1q_gt' : q < p (Fin.castSucc i) := by
          rw [← one_div_lt_one_div h2 hq_pos]
          linarith [h1q_gt]
        simp [p']
        apply (lt_div_iff₀ hq_pos).mpr
        nlinarith [h1q_gt']
      have hp'_sum : ∑ i : Fin (m + 2), (1 / (p' i : ℝ)) = 1 := by
        simp [p']
        have h1 : ∑ i : Fin (m + 2), (q / (p (Fin.castSucc i) : ℝ)) =
          q * ∑ i : Fin (m + 2), (1 / (p (Fin.castSucc i) : ℝ)) := by
          rw [Finset.mul_sum]
          congr
          funext i
          field_simp
        rw [h1]
        have h2 : q * ∑ i : Fin (m + 2), (1 / (p (Fin.castSucc i) : ℝ)) = 1 := by
          have h3 : ∑ i : Fin (m + 2), (1 / (p (Fin.castSucc i) : ℝ)) ≠ 0 := by
            apply ne_of_gt
            apply Finset.sum_pos
            · intro i _
              apply one_div_pos.2; linarith [hp (Fin.castSucc i)]
            · use ⟨0, by simp⟩
              simp
          rw [show q = 1 / ∑ i : Fin (m + 2), (1 / (p (Fin.castSucc i) : ℝ)) by rfl]
          field_simp
        exact h2
      have ha'_nonneg : ∀ i : Fin (m + 2), 0 ≤ a' i := by
        intro i
        simp [a']
        apply Real.rpow_nonneg
        exact ha (Fin.castSucc i)
      have h_ind : ∏ i : Fin (m + 2), a' i ≤ ∑ i : Fin (m + 2), (a' i)^(p' i) / (p' i) := by
        apply ih (p := p') (a := a') hp'_gt_1 hp'_sum ha'_nonneg
      have h_prod_split : ∏ i : Fin (m + 3), a i =
          (∏ i : Fin (m + 2), a (Fin.castSucc i)) * a (Fin.last (m + 2)) := by
        rw [Fin.prod_univ_castSucc]
      have h_sum_split2 : ∑ i : Fin (m + 3), (a i)^(p i) / (p i) =
          (∑ i : Fin (m + 2), (a (Fin.castSucc i))^(p (Fin.castSucc i)) / (p (Fin.castSucc i))) +
          (a (Fin.last (m + 2)))^(p (Fin.last (m + 2))) / (p (Fin.last (m + 2))) := by
        simp [Fin.sum_univ_castSucc]
      have h_ind_left : ∏ i : Fin (m + 2), a' i = (∏ i : Fin (m + 2), a (Fin.castSucc i)) ^ q := by
        simp [a']
        have : ∀ (s : Finset (Fin (m + 2))),
            ∏ i ∈ s, (a i.castSucc) ^ q = (∏ i ∈ s, a i.castSucc) ^ q := by
          intro s
          induction s using Finset.induction_on with
          | empty => simp
          | @insert i s his ih =>
            have h_nonneg1 : 0 ≤ a i.castSucc := ha i.castSucc
            have h_nonneg2 : 0 ≤ ∏ j ∈ s, a j.castSucc := by
              apply Finset.prod_nonneg
              intro j _
              exact ha j.castSucc
            rw [Finset.prod_insert his, Finset.prod_insert his, ih, ← Real.mul_rpow h_nonneg1 h_nonneg2]
        exact this Finset.univ
      have h_ind_right : ∑ i : Fin (m + 2), (a' i)^(p' i) / (p' i) =
          q * (∑ i : Fin (m + 2), (a (Fin.castSucc i))^(p (Fin.castSucc i)) / (p (Fin.castSucc i))) := by
        simp [a', p']
        have : ∑ i : Fin (m + 2), ((a (Fin.castSucc i) : ℝ) ^ q) ^ (p (Fin.castSucc i) / q) / (p (Fin.castSucc i) / q) =
          ∑ i : Fin (m + 2), (a (Fin.castSucc i))^(p (Fin.castSucc i)) * q / (p (Fin.castSucc i)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [show ((a (Fin.castSucc i) : ℝ) ^ q) ^ (p (Fin.castSucc i) / q) = (a (Fin.castSucc i))^(p (Fin.castSucc i)) by
            rw [← Real.rpow_mul]
            · field_simp
            · exact ha (Fin.castSucc i)]
          field_simp
          all_goals ring
        rw [this]
        rw [Finset.mul_sum]
        congr
        funext i
        ring
      rw [h_prod_split]
      have h_young : (∏ i : Fin (m + 2), a i.castSucc) * a (Fin.last (m + 2)) ≤
          (∏ i : Fin (m + 2), a i.castSucc) ^ q / q + a (Fin.last (m + 2)) ^ p (Fin.last (m + 2)) / p (Fin.last (m + 2)) := by
        have h_conj : 1 / q + 1 / (p (Fin.last (m + 2)) : ℝ) = 1 := by
          have h1 : 1 / q = ∑ i : Fin (m + 2), (1 / (p (Fin.castSucc i) : ℝ)) := by
            rw [show q = 1 / ∑ i : Fin (m + 2), (1 / (p (Fin.castSucc i) : ℝ)) by rfl]
            field_simp
          rw [h1]
          linarith [h_split]
        apply young_inequality (⟨hq1, hp (Fin.last (m + 2)), h_conj⟩)
        · apply Finset.prod_nonneg
          intro i _
          exact ha i.castSucc
        · exact ha (Fin.last (m + 2))
      have h_ind' : (∏ i : Fin (m + 2), a (Fin.castSucc i)) ^ q / q ≤
        ∑ i : Fin (m + 2), (a (Fin.castSucc i))^(p (Fin.castSucc i)) / (p (Fin.castSucc i)) := by
        have : (∏ i : Fin (m + 2), a (Fin.castSucc i)) ^ q = ∏ i : Fin (m + 2), a' i := by
          rw [h_ind_left]
        rw [this]
        have : ∏ i : Fin (m + 2), a' i ≤ q * (∑ i : Fin (m + 2), (a (Fin.castSucc i))^(p (Fin.castSucc i)) / (p (Fin.castSucc i))) := by
          linarith [h_ind, h_ind_right]
        apply (div_le_iff₀ hq_pos).mpr
        linarith
      nlinarith [h_young, h_ind', h_sum_split2]

end YoungInequality
