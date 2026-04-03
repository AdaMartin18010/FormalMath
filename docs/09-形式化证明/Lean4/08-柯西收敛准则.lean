/-
# 柯西收敛准则的形式化 / Cauchy Convergence Criterion

## Mathlib4对应
- **模块**: `Mathlib.Topology.UniformSpace`, `Mathlib.Analysis.SpecificLimits`
- **核心定理**:
  - `CompleteSpace.complete`: 完备空间中柯西序列收敛
  - `cauchySeq_tendsto_of_complete`: 完备空间中的柯西序列有极限
- **相关定义**:
  - `CauchySeq`: 柯西序列
  - `CompleteSpace`: 完备空间
  - `atTop`: 趋向无穷的滤子

## 定理陈述

在实数集 ℝ 中，序列 (aₙ) 收敛当且仅当它是柯西序列。

即：∀ ε > 0, ∃ N, ∀ m, n ≥ N, |aₘ - aₙ| < ε

## 数学意义

柯西收敛准则是实数完备性的核心体现。
它提供了不依赖极限值的收敛判定方法，是构造实数的重要工具。

## 历史背景

由法国数学家奥古斯丁-路易·柯西(Augustin-Louis Cauchy, 1789-1857)于1821年提出。
柯西对分析学的严格化做出了奠基性贡献。
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.Complete
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot

universe u

namespace CauchyConvergenceCriterion

open Filter Real Topology

/-
## 第一部分：柯西序列的定义

**定义**: 序列 (aₙ) 称为柯西序列，如果：
∀ ε > 0, ∃ N ∈ ℕ, ∀ m, n ≥ N, |aₘ - aₙ| < ε

直观理解：序列的项在足够远之后变得任意接近。
-/

-- 柯西序列的定义（使用Mathlib4的CauchySeq）
variable {α : Type*} [UniformSpace α]

def IsCauchySeq (a : ℕ → α) : Prop :=
  /- 序列是柯西序列 -/
  CauchySeq a

-- 柯西序列的ε-N定义（实数情形）
theorem cauchySeq_real_iff (a : ℕ → ℝ) :
    CauchySeq a ↔ ∀ ε > 0, ∃ N : ℕ, ∀ m n : ℕ, m ≥ N → n ≥ N → |a m - a n| < ε := by
  /- 展开CauchySeq的定义 -/
  rw [cauchySeq_iff]
  /- 实数上的均匀结构由绝对值度量诱导 -/
  simp [dist_eq_norm, norm_sub_rev]
  /- 等价转换 -/
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨N, hN⟩
    use N
    intro m n hm hn
    specialize hN m n hm hn
    simpa using hN
  · intro h ε hε
    rcases h ε hε with ⟨N, hN⟩
    use N
    intro m n hm hn
    specialize hN m n hm hn
    simpa using hN

/-
## 第二部分：收敛序列是柯西序列

**定理**: 任何收敛序列都是柯西序列。

**证明**: 设 aₙ → L，对于 ε > 0，存在 N 使得 ∀ n ≥ N, |aₙ - L| < ε/2。
则对于 m, n ≥ N：
|aₘ - aₙ| = |aₘ - L + L - aₙ| ≤ |aₘ - L| + |L - aₙ| < ε/2 + ε/2 = ε
-/

-- 收敛序列是柯西序列
theorem convergent_imp_cauchy {a : ℕ → ℝ} {L : ℝ} (ha : Tendsto a atTop (𝓝 L)) :
    CauchySeq a := by
  /- 使用Mathlib4的定理 -/
  apply cauchySeq_of_tendsto_nhds_atTop
  exact ha

-- 直接证明
theorem convergent_imp_cauchy_direct {a : ℕ → ℝ} {L : ℝ}
    (ha : Tendsto a atTop (𝓝 L)) :
    ∀ ε > 0, ∃ N : ℕ, ∀ m n : ℕ, m ≥ N → n ≥ N → |a m - a n| < ε := by
  intro ε hε
  /- 使用收敛的定义 -/
  rw [tendsto_atTop_nhds] at ha
  /- 存在 N 使得 ∀ n ≥ N, |aₙ - L| < ε/2 -/
  have h_half : ε / 2 > 0 := by linarith
  rcases ha (Metric.ball L (ε / 2)) (Metric.isOpen_ball) (by simp; linarith) with ⟨N, hN⟩
  use N
  intro m n hm hn
  /- |aₘ - aₙ| ≤ |aₘ - L| + |L - aₙ| -/
  have h1 : |a m - L| < ε / 2 := by
    specialize hN m hm
    simp [dist_eq_norm] at hN
    exact hN
  have h2 : |a n - L| < ε / 2 := by
    specialize hN n hn
    simp [dist_eq_norm] at hN
    exact hN
  /- 三角不等式 -/
  calc
    |a m - a n| = |(a m - L) + (L - a n)| := by ring_nf
    _ ≤ |a m - L| + |L - a n| := by apply abs_add
    _ = |a m - L| + |a n - L| := by rw [show |L - a n| = |a n - L| by rw [abs_sub_comm]]
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

/-
## 第三部分：柯西序列有界

**定理**: 任何柯西序列都是有界的。

**证明**: 取 ε = 1，存在 N 使得 ∀ m, n ≥ N, |aₘ - aₙ| < 1。
则对于 n ≥ N，|aₙ| ≤ |a_N| + 1。
结合前 N 项，整个序列有界。
-/

-- 柯西序列有界
theorem cauchy_seq_bounded {a : ℕ → ℝ} (ha : CauchySeq a) :
    ∃ M > 0, ∀ n : ℕ, |a n| ≤ M := by
  /- 取 ε = 1 -/
  rcases cauchySeq_iff.1 ha 1 (by norm_num) with ⟨N, hN⟩
  /- 对于 n ≥ N，|aₙ - a_N| < 1 -/
  let bound_N := |a N| + 1
  /- 前 N 项的最大值 -/
  let max_init := Finset.sup (Finset.range N) (fun n => |a n|)
  /- 整体界 -/
  use max (bound_N + 1) (max_init + 1)
  constructor
  · /- 界为正 -/
    simp [bound_N, max_init]
    intro n hn
    exact abs_nonneg (a n)
  · intro n
    by_cases hn : n ≥ N
    · /- n ≥ N 的情况 -/
      have h : |a n - a N| < 1 := by
        specialize hN n N hn (by simp)
        simpa using hN
      have h_abs : |a n| ≤ |a N| + |a n - a N| := by
        calc
          |a n| = |a N + (a n - a N)| := by ring_nf
          _ ≤ |a N| + |a n - a N| := by apply abs_add
      have h_bound : |a n| < bound_N := by
        linarith [h_abs, h]
      simp [bound_N, max_init]
      /- 证明 |a n| ≤ max(...) -/
      linarith
    · /- n < N 的情况 -/
      have hn' : n < N := by linarith
      simp [bound_N, max_init]
      have h : |a n| ∈ (Finset.range N).image (fun i => |a i|) := by
        simp
        use n
        omega
      have h_le : |a n| ≤ max_init := by
        apply Finset.le_sup h
      linarith

/-
## 第四部分：柯西序列收敛（完备性）

**定理**（实数的完备性）: 实数集中的任何柯西序列都收敛。

这是实数构造的核心性质，等价于：
1. 单调有界序列收敛
2. 区间套原理
3. 确界原理
4. Bolzano-Weierstrass定理
-/

-- 实数的完备性：柯西序列收敛
theorem cauchy_imp_convergent {a : ℕ → ℝ} (ha : CauchySeq a) :
    ∃ L : ℝ, Tendsto a atTop (𝓝 L) := by
  /- 使用Mathlib4的完备性定理 -/
  apply cauchySeq_tendsto_of_complete
  exact ha

-- 柯西收敛准则：双向蕴含
theorem cauchy_convergence_criterion (a : ℕ → ℝ) :
    CauchySeq a ↔ ∃ L : ℝ, Tendsto a atTop (𝓝 L) := by
  constructor
  · /- 柯西序列收敛 -/
    intro ha
    exact cauchy_imp_convergent ha
  · /- 收敛序列是柯西序列 -/
    rintro ⟨L, hL⟩
    exact convergent_imp_cauchy hL

/-
## 第五部分：完备空间

**定义**: 度量空间 (X, d) 称为完备的，如果其中的任何柯西序列都收敛。

实数集 ℝ 是完备空间。
有理数集 ℚ 不是完备空间（例如：√2的近似序列）。
-/

-- 实数空间的完备性实例
instance real_completeSpace : CompleteSpace ℝ := by
  /- Mathlib4已内置 -/
  infer_instance

-- 完备空间中柯西序列收敛
theorem completeSpace_cauchy_converges {α : Type*} [MetricSpace α] [CompleteSpace α]
    (a : ℕ → α) (ha : CauchySeq a) : ∃ L : α, Tendsto a atTop (𝓝 L) := by
  /- 由完备性定义 -/
  apply cauchySeq_tendsto_of_complete
  exact ha

/-
## 第六部分：应用与推论

### 推论1：级数收敛的柯西准则

级数 ∑aₙ 收敛当且仅当：
∀ ε > 0, ∃ N, ∀ m > n ≥ N, |∑_{k=n+1}^{m} aₖ| < ε
-/

-- 级数收敛的柯西准则
theorem series_cauchy_criterion (a : ℕ → ℝ) :
    (∃ S : ℝ, Tendsto (fun n => ∑ k in Finset.range n, a k) atTop (𝓝 S)) ↔
    ∀ ε > 0, ∃ N : ℕ, ∀ m n : ℕ, m > n → n ≥ N → |∑ k in Finset.Ico n m, a k| < ε := by
  /- 级数收敛 ↔ 部分和序列收敛 ↔ 部分和序列是柯西序列 -/
  let S := fun n => ∑ k in Finset.range n, a k
  have h : (∃ S : ℝ, Tendsto S atTop (𝓝 S)) ↔ CauchySeq S := by
    apply cauchy_convergence_criterion
  rw [h]
  /- 展开柯西序列定义 -/
  rw [cauchySeq_iff]
  constructor
  · /- 柯西序列 → 级数柯西条件 -/
    intro h ε hε
    rcases h ε hε with ⟨N, hN⟩
    use N
    intro m n hmn hnN
    have : m ≥ N := by linarith
    have hS := hN m n this hnN
    /- |Sₘ - Sₙ| = |∑_{k=n}^{m-1} aₖ| -/
    have h_diff : S m - S n = ∑ k in Finset.Ico n m, a k := by
      simp [S, sum_Ico_eq_sub]
    rw [← h_diff]
    simpa using hS
  · /- 级数柯西条件 → 柯西序列 -/
    intro h ε hε
    rcases h ε hε with ⟨N, hN⟩
    use N
    intro m n hmN hnN
    wlog hmn : m ≥ n generalizing m n
    · /- 假设 m < n，交换角色 -/
      have : n ≥ m := by linarith
      specialize hN n m (by linarith) hmN
      have h_abs : |S m - S n| = |S n - S m| := by rw [abs_sub_comm]
      rw [h_abs]
      simpa using hN
    · /- m ≥ n -/
      have : m > n ∨ m = n := by
        by_cases h : m = n
        · right; exact h
        · left; linarith
      cases this with
      | inl hmn' =>
        have hS := hN m n hmn' hnN
        have h_diff : S m - S n = ∑ k in Finset.Ico n m, a k := by
          simp [S, sum_Ico_eq_sub]
        rw [h_diff]
        simpa using hS
      | inr h_eq =>
        rw [h_eq]
        simp

/-
## 第七部分：具体例子

### 例子1：几何序列

序列 aₙ = 1/2ⁿ 是柯西序列。
-/

-- 几何序列是柯西序列
theorem geometric_seq_cauchy : CauchySeq (fun n : ℕ => (1 / 2 : ℝ) ^ n) := by
  /- 几何序列收敛于0，所以是柯西序列 -/
  apply convergent_imp_cauchy
  /- 证明收敛于0 -/
  apply tendsto_pow_atTop_nhds_zero_of_lt_one
  all_goals norm_num

### 例子2：调和级数不满足柯西条件

theorem harmonic_series_not_cauchy :
    ¬ CauchySeq (fun n : ℕ => ∑ k in Finset.range n, (1 : ℝ) / (k + 1)) := by
  /- 调和级数发散，所以部分和序列不是柯西序列 -/
  intro h
  rcases cauchy_imp_convergent h with ⟨L, hL⟩
  /- 这与调和级数发散矛盾 -/
  /- 调和级数发散是已知结果 -/
  sorry  -- 需要调和级数发散的完整证明

/-
## 数学意义

柯西收敛准则的重要性：

1. **不依赖极限值**: 判断收敛不需要知道极限是什么
2. **构造实数**: 通过柯西序列等价类构造实数（Cantor构造）
3. **完备化**: 任何度量空间都可以完备化
4. **泛函分析**: Banach空间（完备赋范空间）的理论基础

## 与其他定理的关系

- **单调收敛定理**: 单调有界序列必收敛
- **Bolzano-Weierstrass定理**: 有界序列必有收敛子列
- **闭区间套定理**: 闭区间套的交非空
- **确界原理**: 有上界的集合必有上确界

这些都是实数完备性的等价表述。

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `Mathlib.Topology.UniformSpace.Complete`: 完备空间理论
- `Mathlib.Analysis.SpecificLimits.Basic`: 具体极限
- `Mathlib.Topology.MetricSpace.Cauchy`: 度量空间中的柯西序列
- `cauchySeq_tendsto_of_complete`: 完备空间中柯西序列收敛
-/
