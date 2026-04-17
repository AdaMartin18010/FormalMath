/-
# 代数基本定理的形式化证明 / Fundamental Theorem of Algebra

## Mathlib4对应
- **模块**: `Mathlib.Analysis.Complex.Polynomial`
- **核心定理**: `Complex.isAlgClosed`
- **相关定义**:
  - `IsAlgClosed`: 代数封闭域
  - `splits`: 多项式完全分裂
  - `roots`: 多项式的根

## 定理陈述
每个次数大于0的复系数多项式都在复数域中至少有一个根。
等价表述：复数域 ℂ 是代数封闭域。

## 数学意义
代数基本定理是代数学的基石，它保证了复数域的"完备性"。
它连接了代数和分析，有多种不同的证明方法。

## 历史背景
代数基本定理最早由达朗贝尔(1746)提出，
高斯在1799年给出了第一个被普遍接受的证明。
历史上有很多不同的证明方法，包括：
- 拓扑证明（基于Brouwer不动点定理）
- 分析证明（基于Liouville定理）
- 代数证明（基于Galois理论）
- 复分析证明（基于幅角原理）
-/

import Mathlib.Analysis.Complex.Polynomial
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Polynomial.Degree.Definitions

universe u

namespace FundamentalTheoremAlgebra

open Complex Polynomial

-- 代数基本定理：非零次复系数多项式必有根
theorem fundamental_theorem_of_algebra (P : Polynomial ℂ) (hdeg : P.degree > 0) :
    ∃ z : ℂ, P.IsRoot z := by
  /- 使用Mathlib4的代数基本定理 -/
  have h : P.Splits (RingHom.id ℂ) := IsAlgClosed.splits (RingHom.id ℂ) P
  /- 完全分裂意味着所有根都在 ℂ 中 -/
  rw [Polynomial.splits_iff_card_roots] at h
  · /- 根的数量等于次数（计重数），所以必有根 -/
    have h_deg_pos : P.natDegree > 0 := by
      have : P.natDegree > 0 := by
        have h1 : P.degree > 0 := hdeg
        have h2 : P.natDegree > 0 := by
          have h3 : P.degree = ↑P.natDegree := by
            rw [Polynomial.degree_eq_natDegree]
            intro h4
            rw [h4] at h1
            simp at h1
          rw [h3] at h1
          exact WithBot.coe_pos.mp h1
        exact h2
      exact this
    have h_roots_nonempty : P.roots.Nonempty := by
      rw [Multiset.nonempty_iff_ne_empty]
      intro h_empty
      rw [h_empty] at h
      simp at h
      linarith
    /- 取一个根 -/
    rcases h_roots_nonempty with ⟨z, hz⟩
    use z
    exact (Polynomial.mem_roots (by intro h0; rw [h0] at hdeg; simp at hdeg)).mp hz
  · /- 首项系数非零 -/
    exact P.leadingCoeff_ne_zero (by intro h0; rw [h0] at hdeg; simp at hdeg)

-- 复数域是代数封闭域
theorem complex_is_alg_closed : IsAlgClosed ℂ := by
  /- 使用Mathlib4的实例 -/
  infer_instance

-- 多项式在复数域上完全分裂
theorem polynomial_splits_over_complex (P : Polynomial ℂ) :
    Splits (RingHom.id ℂ) P := by
  /- 使用Mathlib4的定理 -/
  exact IsAlgClosed.splits (RingHom.id ℂ) P

-- 实系数多项式的共轭根定理
theorem complex_conjugate_root_theorem {P : Polynomial ℝ} (z : ℂ)
    (hz : (P.map (algebraMap ℝ ℂ)).IsRoot z) :
    (P.map (algebraMap ℝ ℂ)).IsRoot (star z) := by
  /- 证明：P(z̄) = P̄(z̄) = P(z)̄ = 0̄ = 0 -/
  have h : (P.map (algebraMap ℝ ℂ)).eval (star z) = star ((P.map (algebraMap ℝ ℂ)).eval z) := by
    rw [Polynomial.eval_map, Polynomial.eval_map]
    simp [map_sum, Complex.star_def]
  rw [h, hz]
  simp

end FundamentalTheoremAlgebra

/-
## 数值示例

```lean
-- 多项式 z² + 1 的根是 i 和 -i
example : (X ^ 2 + 1 : Polynomial ℂ).roots = {Complex.I, -Complex.I} := by
  have h_roots : (X ^ 2 + 1 : Polynomial ℂ).roots.card = 2 := by
    rw [card_roots]
    simp
    norm_num

  have h_i : (X ^ 2 + 1 : Polynomial ℂ).IsRoot Complex.I := by
    simp [Polynomial.IsRoot, Complex.I_sq]

  have h_neg_i : (X ^ 2 + 1 : Polynomial ℂ).IsRoot (-Complex.I) := by
    simp [Polynomial.IsRoot, Complex.I_sq]

  have : (X ^ 2 + 1 : Polynomial ℂ).roots = {Complex.I, -Complex.I} := by
    have h_card : (X ^ 2 + 1 : Polynomial ℂ).roots.card = 2 := h_roots
    have h_subset : (X ^ 2 + 1 : Polynomial ℂ).roots ⊆ {Complex.I, -Complex.I} := by
      intro z hz
      simp [Polynomial.mem_roots] at hz
      have : z^2 + 1 = 0 := hz
      have : z^2 = -1 := by
        calc
          z^2 = z^2 + 1 - 1 := by ring
          _ = 0 - 1 := by rw [this]
          _ = -1 := by ring
      have : z = Complex.I ∨ z = -Complex.I := by
        have h_eq : z^2 = -1 := this
        have : z^2 - (-1) = 0 := by
          rw [sub_eq_zero]
          exact h_eq
        have : z^2 - (-1) = z^2 + 1 := by ring_nf
        rw [this] at this
        have : z^2 + 1 = (z - Complex.I) * (z + Complex.I) := by
          ring_nf
          simp [Complex.I_sq]
          ring
        rw [this] at this
        cases (mul_eq_zero.mp this) with
        | inl h =>
          left
          have : z = Complex.I := by
            calc
              z = (z - Complex.I) + Complex.I := by ring
              _ = 0 + Complex.I := by rw [h]
              _ = Complex.I := by ring
          exact this
        | inr h =>
          right
          have : z = -Complex.I := by
            calc
              z = (z + Complex.I) - Complex.I := by ring
              _ = 0 - Complex.I := by rw [h]
              _ = -Complex.I := by ring
          exact this
      simp [this]
    have h_eq : (X ^ 2 + 1 : Polynomial ℂ).roots = {Complex.I, -Complex.I} := by
      apply Finset.subset_of_card_le
      · rw [h_card]
        simp
      · exact h_subset
    exact h_eq
  exact this
```

## 数学意义

代数基本定理的重要性：

1. **复数完备性**：复数域是最大的代数闭域之一
2. **多项式理论**：保证了多项式根的存在性
3. **线性代数**：n×n复矩阵必有n个特征值（计重数）
4. **动力系统**：保证了某些动力系统的周期点存在

## 与其他定理的联系

- **Brouwer不动点定理**：拓扑证明的基础
- **Liouville定理**：分析证明的核心
- **Galois理论**：代数证明的工具
- **幅角原理**：复分析证明的关键

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `Complex.isAlgClosed`: 复数域代数封闭性的实例
- `IsAlgClosed.splits`: 代数封闭域上多项式分裂
- `Polynomial.roots`: 多项式根的定义
- `Polynomial.IsRoot`: 多项式根的判断
-/
