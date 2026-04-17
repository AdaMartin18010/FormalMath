/-
# 柯西收敛准则的形式化证明 / Cauchy Convergence Criterion

## Mathlib4对应
- **模块**: `Mathlib.Topology.MetricSpace.CauSeq`, `Mathlib.Topology.UniformSpace`
- **核心定理**: `Metric.complete_of_cauchy_sequences_complete`
- **相关定义**:
  - `CauSeq`: 柯西序列
  - `CompleteSpace`: 完备空间
  - `UniformSpace`: 一致空间

## 定理陈述

### 实数版本的柯西收敛准则
实数序列 (aₙ) 收敛 ⟺ (aₙ) 是柯西序列

即：序列收敛当且仅当对于任意 ε > 0，存在 N，使得对于所有 m, n ≥ N，
有 |aₙ - aₘ| < ε。

### 一般度量空间版本
在完备度量空间中，柯西序列收敛。

## 数学意义

柯西收敛准则是分析学的基础定理，它提供了不依赖极限值的收敛判定方法。
它是实数完备性的等价刻画之一。

## 历史背景

由奥古斯丁-路易·柯西(Augustin-Louis Cauchy, 1789-1857)在19世纪提出，
为分析学的严格化奠定了基础。

## 证明复杂度分析
- **难度等级**: P2 (本科高级)
- **证明行数**: ~200行
- **关键引理**: 4个
- **主要策略**: 完备性论证 + 构造性证明
-/

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.CauSeq
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Cauchy

universe u v

namespace CauchyConvergence

open Metric Filter Set Topology

/-
## 第一部分：柯西序列的定义

在度量空间中，柯西序列是指：随着序列推进，元素之间的距离可以任意小。
-/

variable {α : Type*} [MetricSpace α]

-- 柯西序列的定义（使用Mathlib4的标准定义）
def IsCauchySeq (a : ℕ → α) : Prop :=
  CauchySeq a

-- 柯西序列的ε-δ定义
theorem cauchy_seq_iff (a : ℕ → α) :
    IsCauchySeq a ↔ ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n → dist (a m) (a n) < ε := by
  rw [Metric.cauchySeq_iff]
  rfl

/-
## 第二部分：实数空间的完备性

实数空间ℝ是完备的：每个柯西序列都收敛。

**证明思路**:
1. 首先证明柯西序列有界
2. 利用Bolzano-Weierstrass定理，有界序列有收敛子列
3. 证明原序列收敛到同一极限
-/

-- 柯西序列有界
theorem cauchy_seq_bounded {a : ℕ → ℝ} (h : IsCauchySeq a) :
    ∃ M, ∀ n, |a n| ≤ M := by
  /- 利用柯西条件取 ε = 1 -/
  rcases Metric.cauchySeq_iff.mp h 1 (by norm_num) with ⟨N, hN⟩
  
  /- 构造界 M -/
  let M₁ := Finset.sup (Finset.Icc 0 N) (fun i => |a i|)
  let M₂ := |a N| + 1
  let M := max M₁ M₂
  
  use M
  intro n
  by_cases hn : n ≤ N
  · /- 对于 n ≤ N，|a n| ≤ M₁ ≤ M -/
    have h₁ : |a n| ≤ M₁ := by
      apply Finset.le_sup
      simp
      omega
    have h₂ : M₁ ≤ M := by apply le_max_left
    linarith
  · /- 对于 n > N，利用柯西条件 -/
    have hN' := hN n N (by omega) (by rfl)
    have h_dist : |a n - a N| < 1 := by
      simpa [dist_eq_norm, norm_eq_abs] using hN'
    have h₁ : |a n| ≤ |a N| + 1 := by
      have h : |a n| - |a N| ≤ |a n - a N| := by
        apply abs_sub_abs_le_abs_sub
      have h' : |a n - a N| < 1 := h_dist
      linarith [abs_nonneg (a n - a N)]
    have h₂ : |a N| + 1 ≤ M₂ := by rfl
    have h₃ : M₂ ≤ M := by apply le_max_right
    linarith

-- 柯西序列的收敛性（实数版本）
theorem cauchy_seq_converges_real {a : ℕ → ℝ} (h : IsCauchySeq a) :
    ∃ L : ℝ, Tendsto a atTop (𝓝 L) := by
  /- 使用Mathlib4的完备性定理 -/
  apply cauchySeq_tendsto_of_complete
  exact h

-- 柯西收敛准则（⇒方向）
theorem converges_implies_cauchy {a : ℕ → ℝ} {L : ℝ}
    (h : Tendsto a atTop (𝓝 L)) : IsCauchySeq a := by
  /- 收敛序列是柯西序列 -/
  apply cauchySeq_of_tendsto_nhds
  exact h

/-
## 第三部分：柯西收敛准则的完整表述

**柯西收敛准则**: 实数序列收敛 ⟺ 它是柯西序列
-/

-- 柯西收敛准则（完整版本）
theorem cauchy_convergence_criterion (a : ℕ → ℝ) :
    (∃ L : ℝ, Tendsto a atTop (𝓝 L)) ↔ IsCauchySeq a := by
  constructor
  · -- 收敛 ⇒ 柯西
    rintro ⟨L, hL⟩
    exact converges_implies_cauchy hL
  · -- 柯西 ⇒ 收敛
    intro hCauchy
    exact cauchy_seq_converges_real hCauchy

/-
## 第四部分：完备度量空间

在一般的完备度量空间中，柯西序列同样收敛。
-/

-- 完备度量空间的定义检查
#check CompleteSpace

-- 完备度量空间中的柯西收敛
theorem cauchy_convergence_general {α : Type*} [MetricSpace α] [CompleteSpace α]
    (a : ℕ → α) (h : IsCauchySeq a) :
    ∃ L : α, Tendsto a atTop (𝓝 L) := by
  /- 使用完备空间的定义 -/
  apply CompleteSpace.complete
  unfold IsCauchySeq at h
  exact h

-- 实数是完备度量空间
instance : CompleteSpace ℝ := by infer_instance

/-
## 第五部分：柯西序列的应用

### 应用1：级数收敛的柯西判别法

级数 ∑aₙ 收敛 ⟺ 部分和序列是柯西序列
-/

-- 级数收敛的柯西条件
theorem series_cauchy_criterion {a : ℕ → ℝ} :
    (∃ S : ℝ, Tendsto (fun n => ∑ i in Finset.range n, a i) atTop (𝓝 S)) ↔
    ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → m ≤ n → |∑ i in Finset.Ico m n, a i| < ε := by
  rw [cauchy_convergence_criterion]
  simp only [IsCauchySeq, Metric.cauchySeq_iff]
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨N, hN⟩
    use N
    intro m n hm hmn
    have h' := hN m n hm (by linarith)
    /- 利用部分和的差等于区间和 -/
    have h_sum : dist (∑ i in Finset.range m, a i) (∑ i in Finset.range n, a i) =
        |∑ i in Finset.Ico m n, a i| := by
      simp [dist_eq_norm, norm_eq_abs]
      rw [Finset.sum_range_eq_add_sum_Ico]
      · ring_nf
        simp [abs_neg]
      · linarith
    rw [h_sum] at h'
    exact h'
  · intro h ε hε
    rcases h ε hε with ⟨N, hN⟩
    use N
    intro m n hm hn
    wlog hmn : m ≤ n generalizing m n
    · /- 若 m > n，交换角色 -/
      have h' := this n m hn (by linarith) (by linarith)
      have h_symm : |∑ i in Finset.Ico n m, a i| = |∑ i in Finset.Ico m n, a i| := by
        have : ∑ i in Finset.Ico n m, a i = - ∑ i in Finset.Ico m n, a i := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr
          · rw [Nat.Ico_union_Ico_eq_Ico (by linarith) (by linarith)]
            have : Finset.Ico n m ∪ Finset.Ico m n = Finset.Ico (min m n) (max m n) := by
              rw [Nat.Ico_union_Ico_eq_Ico (by simp; linarith) (by simp; linarith)]
            have hdisj : Finset.Disjoint (Finset.Ico n m) (Finset.Ico m n) := by
              apply Finset.disjoint_left.mpr
              intro k hk
              simp at hk ⊢
              omega
            have h_eq : ∑ i in Finset.Ico n m, a i + ∑ i in Finset.Ico m n, a i =
                ∑ i in Finset.Ico (min m n) (max m n), a i := by
              rw [← Finset.sum_union hdisj, this]
            have h_min : min m n = n := by linarith
            have h_max : max m n = m := by linarith
            rw [h_min, h_max] at h_eq
            linarith
          · intro i hi
            rfl
        rw [this]
        simp
      have h_dist : dist (∑ i in Finset.range m, a i) (∑ i in Finset.range n, a i) =
          |∑ i in Finset.Ico n m, a i| := by
        simp [dist_eq_norm, norm_eq_abs]
        rw [Finset.sum_range_eq_add_sum_Ico]
        · ring_nf
          simp [abs_neg]
        · linarith
      linarith [h', h_symm, h_dist]
    have h' := hN m n hm hmn
    have h_sum : dist (∑ i in Finset.range m, a i) (∑ i in Finset.range n, a i) =
        |∑ i in Finset.Ico m n, a i| := by
      simp [dist_eq_norm, norm_eq_abs]
      rw [Finset.sum_range_eq_add_sum_Ico]
      · ring_nf
        simp [abs_neg]
      · linarith
    linarith [h', h_sum]

/-
## 第六部分：一致收敛的柯西准则

函数序列一致收敛的柯西判别法。
-/

variable {β : Type*} [TopologicalSpace β]

-- 一致收敛的柯西条件
theorem uniform_cauchy_criterion {f : ℕ → β → ℝ} :
    (∃ f_lim : β → ℝ, TendstoUniformly f f_lim atTop) ↔
    ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n → ∀ x, |f m x - f n x| < ε := by
  constructor
  · -- 一致收敛 ⇒ 一致柯西
    intro h ε hε
    rcases h with ⟨f_lim, h_tendsto⟩
    rcases h_tendsto (by norm_num : 0 < ε / 2) (by norm_num) with ⟨N, hN⟩
    use N
    intro m n hm hn x
    have h1 : |f m x - f_lim x| < ε / 2 := hN m hm x
    have h2 : |f n x - f_lim x| < ε / 2 := hN n hn x
    calc
      |f m x - f n x| = |(f m x - f_lim x) + (f_lim x - f n x)| := by ring_nf
      _ ≤ |f m x - f_lim x| + |f_lim x - f n x| := by apply abs_add
      _ = |f m x - f_lim x| + |f n x - f_lim x| := by rw [abs_sub_comm (f_lim x) (f n x)]
      _ < ε / 2 + ε / 2 := by linarith
      _ = ε := by ring
  · -- 一致柯西 ⇒ 一致收敛（简化版）
    intro h
    /- 对于每个x，f_n(x)是ℝ中的柯西序列，因此收敛 -/
    /- 定义极限函数 -/
    let f_lim : β → ℝ := fun x =>
      Classical.choose (cauchy_seq_converges_real (by
        apply Metric.cauchySeq_iff.mpr
        intro ε hε
        rcases h ε hε with ⟨N, hN⟩
        use N
        intro m n hm hn
        exact hN m n hm hn x
      ))
    use f_lim
    /- 证明一致收敛 -/
    intro ε hε
    rcases h (ε / 2) (by linarith) with ⟨N, hN⟩
    use N
    intro n hn x
    have h_tendsto : Tendsto (fun m => f m x) atTop (𝓝 (f_lim x)) := by
      have h_cauchy : CauchySeq (fun m => f m x) := by
        apply Metric.cauchySeq_iff.mpr
        intro ε' hε'
        rcases h ε' hε' with ⟨N', hN'⟩
        use N'
        intro m n hm hn
        exact hN' m n hm hn x
      exact cauchySeq_tendsto_of_complete h_cauchy
    have h_eventually : ∀ᶠ m in atTop, |f m x - f_lim x| < ε / 2 := by
      have h1 : Tendsto (fun m => f m x) atTop (𝓝 (f_lim x)) := h_tendsto
      have h2 : ∀ᶠ m in atTop, dist (f m x) (f_lim x) < ε / 2 := by
        apply h1.eventually_lt_const
        linarith
      simp [dist_eq_norm, norm_eq_abs] at h2
      exact h2
    rcases h_eventually.exists with ⟨M, hM⟩
    have h1 : |f (max N M) x - f_lim x| < ε / 2 := hM (le_max_right N M)
    have h2 : |f n x - f (max N M) x| < ε / 2 := by
      apply hN n (max N M) hn (le_max_left N M) x
    calc
      |f n x - f_lim x| ≤ |f n x - f (max N M) x| + |f (max N M) x - f_lim x| := by
        rw [show f n x - f_lim x = (f n x - f (max N M) x) + (f (max N M) x - f_lim x) by ring]
        apply abs_add
      _ < ε / 2 + ε / 2 := by linarith
      _ = ε := by ring

end CauchyConvergence

/-
## 数学意义

柯西收敛准则的重要性：

1. **不依赖极限值**：可以直接从序列本身判断收敛性
2. **完备性的刻画**：是实数完备性的等价条件之一
3. **构造性证明**：可以构造出极限值
4. **泛化到抽象空间**：是完备度量空间和巴拿赫空间的基础

## 与其他概念的关系

- **实数完备性公理**：柯西准则等价于实数的完备性
- **Bolzano-Weierstrass定理**：共同构成实数分析的基础
- **一致收敛**：函数空间中的柯西准则
- **完备化**：任意度量空间可以完备化

## 应用示例

### 例1：证明序列收敛
证明 aₙ = 1 + 1/2² + 1/3² + ... + 1/n² 收敛。

```lean
example : IsCauchySeq (fun n => ∑ i in Finset.Icc 1 n, (1 : ℝ) / i^2) := by
  /- 该级数收敛，所以部分和序列是柯西序列 -/
  rw [cauchy_convergence_criterion]
  use Real.pi ^ 2 / 6
  /- 使用已知结果：∑ 1/n² = π²/6 (Basel问题) -/
  have h : Tendsto (fun n => ∑ i in Finset.Icc 1 n, (1 : ℝ) / i^2) atTop (𝓝 (Real.pi ^ 2 / 6)) := by
    have h1 : ∀ n, ∑ i in Finset.Icc 1 n, (1 : ℝ) / i^2 = ∑ i in Finset.range (n + 1), (1 : ℝ) / (i + 1)^2 := by
      intro n
      apply Finset.sum_bij (fun i _ => i - 1)
      · intro i hi
        simp at hi ⊢
        omega
      · intro i j hi hj h_eq
        simp at h_eq
        omega
      · intro j hj
        use j + 1
        simp at hj ⊢
        omega
      · intro i hi
        simp
    have h2 : Tendsto (fun n => ∑ i in Finset.range (n + 1), (1 : ℝ) / (i + 1)^2) atTop (𝓝 (Real.pi ^ 2 / 6)) := by
      have h3 : ∑' i : ℕ, (1 : ℝ) / (i + 1)^2 = Real.pi ^ 2 / 6 := by
        have h4 : ∑' i : ℕ, (1 : ℝ) / (i + 1)^2 = ∑' i : ℕ, (1 : ℝ) / (i + 1)^2 := rfl
        /- 使用Mathlib的已知结果 -/
        have h5 : ∑' n : ℕ, (1 : ℝ) / (n + 1)^2 = Real.pi ^ 2 / 6 := Real.hasSum_zeta_two.tsum_eq
        exact h5
      have h4 : Tendsto (fun n => ∑ i in Finset.range n, (1 : ℝ) / (i + 1)^2) atTop (𝓝 (∑' i : ℕ, (1 : ℝ) / (i + 1)^2)) := by
        apply Finset.tendsto_sum_tsum
        apply Summable.of_nonneg_of_le
        · intro i; positivity
        · intro i; simp
        · exact summable_nat_add_iff 1 |>.mp (summable_zeta_two (by norm_num))
      have h5 : (fun n => ∑ i in Finset.range (n + 1), (1 : ℝ) / (i + 1)^2) = (fun n => (fun m => ∑ i in Finset.range m, (1 : ℝ) / (i + 1)^2) (n + 1)) := by
        funext n
        rfl
      rw [h5, h3]
      apply Tendsto.comp h4
      apply tendsto_atTop_atTop_of_monotone
      · intro m n hmn
        simp
        omega
      · intro n
        use n
        omega
    simpa [h1] using h2
  exact h
```

### 例2：构造实数
通过有理数柯西序列的等价类构造实数。

## 历史发展

| 年份 | 数学家 | 贡献 |
|------|--------|------|
| 1821 | 柯西 | 提出柯西准则 |
| 1872 | 戴德金 | 戴德金分割构造实数 |
| 1872 | 康托尔 | 用柯西序列构造实数 |
| 现代 | - | 推广到抽象空间 |

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `Mathlib.Topology.MetricSpace.CauSeq`: 柯西序列
- `Mathlib.Topology.UniformSpace.Cauchy`: 一致空间中的柯西滤子
- `Mathlib.Topology.MetricSpace.Completion`: 度量空间完备化

## 相关定理链接

- [波尔查诺-魏尔斯特拉斯定理](./BolzanoWeierstrass.lean) - 有界序列的收敛子列
- [中间值定理](./IntermediateValueTheorem.lean) - 连续函数的性质
- [隐函数定理](./ImplicitFunctionTheorem.lean) - 多元分析基础
-/
