---
title: "Lean4 待形式化定理清单"
msc_primary: "03"
---

# Lean4 待形式化定理清单（银层核心课程）

> 本文档列出与 MIT 18.100A、MIT 18.701、MIT 18.06 银层核心课程对齐、但当前 `docs/09-形式化证明/Lean4/` 目录下**尚无独立 `.lean` 实现**的核心定理。每个定理均提供 `sorry` 框架，供后续形式化填充。

---

## MIT 18.100A（实分析）

### EVT-1 极值定理（Extreme Value Theorem）

```lean
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Order.IntermediateValue

open Set Topology

-- 闭区间上连续函数必取得最大值与最小值
theorem extreme_value_theorem {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) :
    ∃ x ∈ Icc a b, ∀ y ∈ Icc a b, f y ≤ f x := by
  sorry
```

### UCT-1 一致连续性定理（Uniform Continuity on Compact Interval）

```lean
import Mathlib.Topology.UniformSpace.Basic

open Set Topology

-- 闭区间上的连续函数必一致连续
theorem uniform_continuity_on_Icc {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) :
    UniformContinuousOn f (Icc a b) := by
  sorry
```

### IMT-1 积分中值定理（Integral Mean Value Theorem）

```lean
import Mathlib.MeasureTheory.Integral.IntervalIntegral

open MeasureTheory

-- 连续函数在闭区间上的积分等于函数在某点的值乘以区间长度
theorem integral_mean_value {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) :
    ∃ c ∈ Icc a b, ∫ x in a..b, f x = f c * (b - a) := by
  sorry
```

### SCT-1 级数比较判别法（Comparison Test）

```lean
import Mathlib.Analysis.SpecificLimits.Basic

-- 若 0 ≤ aₙ ≤ bₙ 且 Σbₙ 收敛，则 Σaₙ 收敛
theorem comparison_test {a b : ℕ → ℝ} (h0 : ∀ n, 0 ≤ a n ∧ a n ≤ b n)
    (hb : Summable b) : Summable a := by
  sorry
```

---

## MIT 18.701（代数 I）

### ORS-1 轨道-稳定子定理（Orbit-Stabilizer Theorem）

```lean
import Mathlib.GroupTheory.GroupAction.Basic

open Fintype

-- 有限群作用下，轨道大小等于指数 |G| / |Stab(x)|
theorem orbit_stabilizer {G X : Type*} [Group G] [MulAction G X] [Fintype G] [DecidableEq X]
    (x : X) :
    card (orbit G x) * card (stabilizer G x) = card G := by
  sorry
```

### FIT-2 环的第一同构定理（First Isomorphism Theorem for Rings）

```lean
import Mathlib.RingTheory.Ideal.Quotient

open RingTheory Ideal

-- 环同态 f : R → S 诱导 R/ker(f) ≃* range(f)
theorem ring_first_isomorphism {R S : Type*} [Ring R] [Ring S] (f : R →+* S) :
    R ⧸ (ker f) ≃+* f.range := by
  sorry
```

### SYL-2 Sylow 第二定理

```lean
import Mathlib.GroupTheory.Sylow

open Group

-- 任意两个 Sylow p-子群彼此共轭
theorem sylow_second {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : Nat.Prime p)
    (P Q : Sylow p G) :
    ∃ g : G, Q = P.map (MulAut.conj g) := by
  sorry
```

### SYL-3 Sylow 第三定理

```lean
import Mathlib.GroupTheory.Sylow

open Group Nat

-- Sylow p-子群的数量 n_p 满足 n_p | |G| 且 n_p ≡ 1 [MOD p]
theorem sylow_third {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : Nat.Prime p) :
    card (Sylow p G) ∣ card G ∧ card (Sylow p G) ≡ 1 [MOD p] := by
  sorry
```

---

## MIT 18.06（线性代数）

### RND-1 秩-零化度定理（Rank-Nullity Theorem）

```lean
import Mathlib.LinearAlgebra.FiniteDimensional

open FiniteDimensional LinearMap

-- dim(range f) + dim(ker f) = dim(V)
theorem rank_nullity {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] (f : V →ₗ[K] W) :
    finrank K (range f) + finrank K (ker f) = finrank K V := by
  sorry
```

### SVD-1 奇异值分解（Singular Value Decomposition）

```lean
import Mathlib.LinearAlgebra.Matrix.Spectrum

open Matrix

-- 任意 m×n 实矩阵 A 可分解为 U·Σ·Vᵀ
theorem svd_decomposition {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ (U : Matrix (Fin m) (Fin m) ℝ) (S : Matrix (Fin m) (Fin n) ℝ)
      (V : Matrix (Fin n) (Fin n) ℝ),
    U.Orthogonal ∧ V.Orthogonal ∧ S.diagonal ∧ A = U * S * Vᵀ := by
  sorry
```

### QR-1 QR 分解

```lean
import Mathlib.LinearAlgebra.Matrix.PosDef

open Matrix

-- 可逆实矩阵 A 可分解为正交矩阵 Q 与上三角矩阵 R
theorem qr_decomposition {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Invertible A) :
    ∃ (Q R : Matrix (Fin n) (Fin n) ℝ),
    Q.Orthogonal ∧ (∀ i j, j < i → R i j = 0) ∧ A = Q * R := by
  sorry
```

### GSP-1 格拉姆-施密特正交化（Gram-Schmidt Process）

```lean
import Mathlib.LinearAlgebra.Matrix.GramSchmidtOrtho

open Matrix

-- 线性无关向量组可通过 Gram-Schmidt 得到标准正交组
theorem gram_schmidt_orthogonalization {n : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin n))
    (hli : LinearIndependent ℝ v) :
    ∃ (e : Fin n → EuclideanSpace ℝ (Fin n)),
    Orthonormal ℝ e ∧ ∀ k, span ℝ (Set.image e (Set.Iic k)) = span ℝ (Set.image v (Set.Iic k)) := by
  sorry
```

---

## 说明

- 所有 `sorry` 均标记了对应的数学课程代码，便于后续按课程优先级分批填充。
- 若 Mathlib4 中已存在对应定理，建议直接 `exact` 引用；若只有部分结果，可在 `sorry` 处展开细节证明。
- 本清单将随 P2-Lean4-修复 任务进展定期更新。
