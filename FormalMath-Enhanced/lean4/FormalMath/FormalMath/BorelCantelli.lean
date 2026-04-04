/-
# 博雷尔-坎泰利引理 (Borel-Cantelli Lemmas)

## 数学背景

博雷尔-坎泰利引理是测度论和概率论中最基本的结果之一，
它提供了判断事件序列"无穷多次发生"的概率的方法。

### 第一博雷尔-坎泰利引理
设 {Aₙ} 是事件序列，若 Σ P(Aₙ) < ∞，则
```
P(Aₙ i.o.) = 0
```
即"Aₙ发生无穷多次"的概率为0。

### 第二博雷尔-坎泰利引理
设 {Aₙ} 是**独立**事件序列，若 Σ P(Aₙ) = ∞，则
```
P(Aₙ i.o.) = 1
```
即"Aₙ发生无穷多次"的概率为1。

这里 "i.o." 表示 "infinitely often"（无穷多次）。

## 数学意义

1. **0-1律**：第二引理是Kolmogorov 0-1律的特例
2. **几乎必然收敛**：是证明a.s.收敛的核心工具
3. **强大数定律**：是证明SLLN的关键引理
4. **随机级数**：用于判断随机级数的收敛性

## 历史背景

由法国数学家 Émile Borel (1871-1956) 于1909年发现第一引理，
意大利数学家 Francesco Cantelli (1875-1966) 于1917年证明第二引理。

Borel在测度论、概率论和数论方面都有开创性贡献。
Cantelli是概率论公理化早期的关键人物。

## Mathlib4对应
- `Mathlib.Probability.Independence`
- `Mathlib.MeasureTheory.Measure.Limsup`
- `Mathlib.Probability.StrongLaw`

## 参考
- É. Borel, "Les probabilités dénombrables et leurs applications arithmétiques", 1909
- F. P. Cantelli, "Sulla probabilità come limite della frequenza", 1917
- Durrett, "Probability: Theory and Examples", Chapter 2
- Williams, "Probability with Martingales", Chapter 4
- Billingsley, "Probability and Measure", Section 4

-/

import Mathlib.Probability.Independence
import Mathlib.MeasureTheory.Measure.Limsup
import Mathlib.Probability.StrongLaw

namespace BorelCantelli

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-
## 上极限事件

定义 limsup Aₙ = ⋂ₙ ⋃ₖ≥ₙ Aₖ

这表示"Aₙ发生无穷多次"的事件：
- ω ∈ limsup Aₙ ⟺ ω 属于无穷多个 Aₙ
- 等价于：∀n, ∃k≥n, ω ∈ Aₖ

记号：{Aₙ i.o.} = limsup Aₙ
-/

/-- 事件序列的无穷多次发生 -/
def infinitelyOften {α : Type*} (A : ℕ → Set α) : Set α :=
  Filter.limsup A atTop

notation:max "{ " A " i.o. }" => infinitelyOften A

/-
## 第一博雷尔-坎泰利引理

**定理**：设 {Aₙ} 是可测集序列，若 Σ ℙ(Aₙ) < ∞，则
```
ℙ({Aₙ i.o.}) = 0
```

**证明**：
1. 注意到 {Aₙ i.o.} = ⋂ₙ ⋃ₖ≥ₙ Aₖ
2. 由连续性，ℙ({Aₙ i.o.}) = limₙ ℙ(⋃ₖ≥ₙ Aₖ)
3. 由次可加性，ℙ(⋃ₖ≥ₙ Aₖ) ≤ Σₖ≥ₙ ℙ(Aₖ)
4. 由于级数收敛，尾部和趋于0：limₙ Σₖ≥ₙ ℙ(Aₖ) = 0
5. 因此 ℙ({Aₙ i.o.}) = 0

**直观理解**：
如果总"期望次数"有限，那么几乎必然只有有限次发生。

这是测度论的基本结果，不需要独立性假设。
-/

theorem borel_cantelli_first {A : ℕ → Set Ω} 
    (hA : ∀ n, MeasurableSet (A n))
    (h_sum : ∑' n, ℙ (A n) < ∞) :
    ℙ { A i.o. } = 0 := by
  -- 利用MeasureTheory中的结果
  apply measure_limsup_eq_zero
  · -- Σ ℙ(Aₙ) < ∞
    exact h_sum
  · -- 每个 Aₙ 可测
    intro n
    exact hA n

/-
## 第一引理的推论

第一博雷尔-坎泰利引理有许多重要推论：

1. **几乎必然收敛的充分条件**：
   若 Σ P(|Xₙ - X| > ε) < ∞ 对所有 ε > 0，则 Xₙ → X a.s.

2. **完全收敛**：
   若 Σ P(|Xₙ| > ε) < ∞ 对所有 ε > 0，则 Xₙ → 0 a.s.

3. **快速收敛**：
   若 P(|Xₙ - X| > ε) = O(n^{-p}) 对某个 p > 1，则 Xₙ → X a.s.
-/

/-- 几乎必然收敛的充分条件 -/
theorem a_s_convergence_criterion {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, Measurable (X n)) (hY : Measurable Y)
    (h : ∀ ε > 0, ∑' n, ℙ {ω | |X n ω - Y ω| > ε} < ∞) :
    ∀ᵐ ω ∂ℙ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (Y ω)) := by
  -- 证明思路：
  -- 对每个 ε = 1/k，应用Borel-Cantelli第一引理
  -- 说明 |Xₙ - Y| > 1/k 只发生有限次
  -- 这意味着 Xₙ → Y a.s.
  sorry

/-
## 第二博雷尔-坎泰利引理

**定理**：设 {Aₙ} 是**独立**事件序列，若 Σ ℙ(Aₙ) = ∞，则
```
ℙ({Aₙ i.o.}) = 1
```

**证明**：
1. 注意到 {Aₙ i.o.}ᶜ = ⋃ₙ ⋂ₖ≥ₙ Aₖᶜ
2. 只需证明 ℙ(⋂ₖ≥ₙ Aₖᶜ) = 0 对所有 n
3. 由独立性：
   ℙ(⋂ₖ₌ₙᵐ Aₖᶜ) = ∏ₖ₌ₙᵐ (1 - ℙ(Aₖ))
4. 利用 1 - x ≤ e^{-x}：
   ∏ₖ₌ₙᵐ (1 - ℙ(Aₖ)) ≤ exp(-∑ₖ₌ₙᵐ ℙ(Aₖ))
5. 由于 Σ ℙ(Aₙ) = ∞，有 ∑ₖ₌ₙᵐ ℙ(Aₖ) → ∞ 当 m → ∞
6. 因此 ℙ(⋂ₖ≥ₙ Aₖᶜ) = limₘ ∏ₖ₌ₙᵐ (1 - ℙ(Aₖ)) = 0

这是概率论中0-1律的经典例子。

**注意**：独立性假设是本质的！
反例：取 Aₙ = A₁ 对所有 n，若 0 < P(A₁) < 1，
则 Σ P(Aₙ) = ∞，但 P(Aₙ i.o.) = P(A₁) ≠ 1。
-/

theorem borel_cantelli_second {A : ℕ → Set Ω}
    (hA : ∀ n, MeasurableSet (A n))
    (h_indep : iIndepSet A ℙ)
    (h_sum : ∑' n, ℙ (A n) = ∞) :
    ℙ { A i.o. } = 1 := by
  -- 证明补事件的概率为0
  have h_compl : ℙ ({ A i.o. }ᶜ) = 0 := by
    -- 补事件是"最终全不发生"
    have h_compl_eq : { A i.o. }ᶜ = ⋃ n, ⋂ k ≥ n, (A k)ᶜ := by
      rw [infinitelyOften, Filter.limsup_eq_iInf_iSup]
      simp [Set.compl_iInf, Set.compl_iSup]
      ext ω
      simp
      aesop
    
    rw [h_compl_eq]
    -- 证明每个 ⋃ₙ ⋂ₖ≥ₙ Aₖᶜ 的概率为0
    have h_zero : ∀ n, ℙ (⋂ k ≥ n, (A k)ᶜ) = 0 := by
      intro n
      -- 计算有限交的测度
      have h_finite_inter : ∀ m ≥ n, ℙ (⋂ k ∈ Finset.Icc n m, (A k)ᶜ) = 
          ∏ k ∈ Finset.Icc n m, (1 - ℙ (A k)) := by
        intro m hm
        -- 利用独立性
        sorry
      
      -- 取极限
      have h_limit : ℙ (⋂ k ≥ n, (A k)ᶜ) = 
          ⨅ m ≥ n, ℙ (⋂ k ∈ Finset.Icc n m, (A k)ᶜ) := by
        sorry
      
      rw [h_limit]
      -- 利用 1 - x ≤ e^{-x}
      have h_exp_bound : ∀ m ≥ n, ∏ k ∈ Finset.Icc n m, (1 - ℙ (A k)) ≤ 
          Real.exp (-∑ k ∈ Finset.Icc n m, ℙ (A k)) := by
        intro m hm
        apply Finset.prod_le_exp_neg_sum
        intro k hk
        -- 0 ≤ ℙ(Aₖ) ≤ 1
        sorry
      
      -- 由于级数发散，指数趋于0
      have h_exp_tendsto : Tendsto (fun m ↦ Real.exp (-∑ k ∈ Finset.Icc n m, ℙ (A k))) atTop (𝓝 0) := by
        have h_sum_tendsto : Tendsto (fun m ↦ ∑ k ∈ Finset.Icc n m, ℙ (A k)) atTop atTop := by
          -- 级数发散意味着部分和无界
          sorry
        have : Tendsto (fun x ↦ Real.exp (-x)) atTop (𝓝 0) := by
          apply Real.tendsto_exp_atBot.comp
          exact tendsto_neg_atTop_atBot
        exact this.comp h_sum_tendsto
      
      -- 因此概率为0
      sorry
    
    -- 可数个零测集的并仍为零测
    sorry
  
  -- 补事件概率为0 ⟹ 原事件概率为1
  have h_total : ℙ { A i.o. } + ℙ ({ A i.o. }ᶜ) = 1 := by
    rw [← measure_union disjoint_compl_right _ _]
    · simp
    · -- limsup A 可测
      sorry
    · -- (limsup A)ᶜ 可测
      sorry
  linarith

/-
## 两两独立版本

第二博雷尔-坎泰利引理在两两独立（而非联合独立）的条件下也成立。
这是Erdős和Rényi在1959年证明的。

这个版本在应用中更加灵活。
-/

theorem borel_cantelli_pairwise_independent {A : ℕ → Set Ω}
    (hA : ∀ n, MeasurableSet (A n))
    (h_pairwise_indep : ∀ i j, i ≠ j → IndepSet (A i) (A j) ℙ)
    (h_sum : ∑' n, ℙ (A n) = ∞) :
    ℙ { A i.o. } = 1 := by
  -- Erdős-Rényi证明的关键步骤：
  -- 1. 计算 Var(∑ 1_{A_k}) = ∑ Var(1_{A_k}) （两两独立）
  -- 2. 应用切比雪夫不等式
  -- 3. 证明 S_n / E[S_n] → 1 依概率收敛
  -- 4. 结合Borel-Cantelli第一引理得到 a.s. 结果
  sorry

/-
## 应用：强大数定律

博雷尔-坎泰利引理是证明强大数定律的关键工具。

**定理**：设 X₁, X₂, ... 是 i.i.d. 随机变量，E|X₁| < ∞，则
```
(X₁ + ... + Xₙ)/n → E[X₁]  a.s.
```

**证明概要**（截断法）：
1. 定义截断变量 Yₙ = Xₙ·1_{|Xₙ|≤n}
2. 证明 Σ P(Xₙ ≠ Yₙ) < ∞（利用 E|X₁| < ∞）
3. 由Borel-Cantelli第一引理，Xₙ = Yₙ 最终成立
4. 对截断后的变量应用方差估计
5. 再次使用Borel-Cantelli得到收敛

详见 StrongLawOfLargeNumbers.lean
-/

/-
## 应用：随机级数

博雷尔-坎泰利引理可用于判断随机级数的收敛性。

**定理**：设 Xₙ 是独立随机变量，则
```
Σ Xₙ 收敛 a.s.  ⟺  Σ Xₙ 收敛依概率
```

这是Lévy定理的一个版本。
-/

theorem random_series_convergence {X : ℕ → Ω → ℝ}
    (h_indep : iIndepFun (fun _ ↦ borel ℝ) X ℙ) :
    (∀ᵐ ω ∂ℙ, ∃ L, Tendsto (fun n ↦ ∑ i in Finset.range n, X i ω) atTop (𝓝 L)) ↔
    (Tendsto (fun n ↦ ∑ i in Finset.range n, X i) atTop (𝓝 (0 : Ω → ℝ)) :
      Filter.Tendsto _ _ (Measure.ae ℙ)) := by
  -- Lévy定理：对独立随机变量，a.s.收敛与依概率收敛等价
  sorry

/-
## Kolmogorov三级数定理

这是判定独立随机变量级数几乎必然收敛的精确准则。

**定理**：设 Xₙ 独立，A > 0。令 Yₙ = Xₙ·1_{|Xₙ|≤A}。
则 Σ Xₙ 收敛 a.s. 当且仅当以下三级数收敛：
1. Σ P(|Xₙ| > A) < ∞
2. Σ E[Yₙ] 收敛
3. Σ Var(Yₙ) < ∞

这是博雷尔-坎泰利引理和方差技巧的综合应用。
-/

theorem kolmogorov_three_series {X : ℕ → Ω → ℝ}
    (h_indep : iIndepFun (fun _ ↦ borel ℝ) X ℙ)
    (A : ℝ) (hA : A > 0) :
    let Y n := X n * (indicator {ω | |X n ω| ≤ A} (fun _ ↦ (1 : ℝ)))
    (∀ᵐ ω ∂ℙ, ∃ L, Tendsto (fun n ↦ ∑ i in Finset.Icc 0 n, X i ω) atTop (𝓝 L)) ↔
    ((∑' n, ℙ {ω | |X n ω| > A}) < ∞ ∧
     (∃ s, Tendsto (fun n ↦ ∑ i in Finset.Icc 0 n, ∫ ω, Y i ω ∂ℙ) atTop (𝓝 s)) ∧
     (∑' n, variance (Y n) ℙ) < ∞) := by
  -- 证明分为两部分：
  -- (⇒) 利用Borel-Cantelli和收敛级数的必要条件
  -- (⇐) 利用Kolmogorov不等式和Borel-Cantelli
  sorry

/-
## 0-1律

第二博雷尔-坎泰利引理是Kolmogorov 0-1律的特例。

**Kolmogorov 0-1律**：
设 Xₙ 独立，A 是尾事件（即 A 不依赖于任何有限个Xₙ），
则 P(A) = 0 或 1。

{Aₙ i.o.} 对于独立事件序列是尾事件，因此其概率只能是0或1。
第二Borel-Cantelli引理精确地确定了何时为0，何时为1。
-/

/-- 尾σ-代数 -/
def tailSigmaAlgebra {X : ℕ → Ω → ℝ} (h_indep : iIndepFun (fun _ ↦ borel ℝ) X ℙ) :
    MeasurableSpace Ω :=
  -- 由 ⋂ₙ σ(Xₙ, X_{n+1}, ...) 生成的σ-代数
  sorry

/-- Kolmogorov 0-1律 -/
theorem kolmogorov_zero_one_law {X : ℕ → Ω → ℝ}
    (h_indep : iIndepFun (fun _ ↦ borel ℝ) X ℙ)
    {A : Set Ω} (hA : MeasurableSet[tailSigmaAlgebra h_indep] A) :
    ℙ A = 0 ∨ ℙ A = 1 := by
  -- 证明利用Dynkin π-λ定理
  -- 尾事件与任何有限个Xₙ独立
  -- 因此与自身独立，这意味着 P(A) = P(A)²
  sorry

/-
## 推广：条件Borel-Cantelli引理

在某些应用中，我们需要条件形式的Borel-Cantelli引理。

**定理**：设 {Aₙ} 是适应于滤子 {ℱₙ} 的事件序列，则
```
{Aₙ i.o.} = { Σ P(Aₙ | ℱ_{n-1}) = ∞ }  a.s.
```

这是鞅理论中的重要结果。
-/

-- 详见鞅相关定理文件

end BorelCantelli
