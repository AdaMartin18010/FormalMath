---
title: "Cauchy-Schwarz 不等式 自然语言与 Lean4 对照"
level: "silver"
target_courses:
  - "MIT 18.06 / 18.100A"
---

## 定理陈述

**自然语言**：设 \(V\) 是实（或复）内积空间，对于任意向量 \(u, v \in V\)，有
\[
|\langle u, v \rangle| \leq \|u\| \cdot \|v\|
\]
等号成立当且仅当 \(u\) 和 \(v\) 线性相关。

**Lean4**：

```lean
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic

universe u v
namespace CauchySchwarzInequality
open InnerProductSpace Real Complex

variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]

-- 柯西-施瓦茨不等式：核心形式
theorem cauchy_schwarz_inequality (u v : E) :
    ‖inner u v‖ ≤ ‖u‖ * ‖v‖ := by
  exact norm_inner_le_norm u v  -- 直接调用 Mathlib4 的标准结果
```

## 证明思路

**自然语言**：柯西-施瓦茨不等式的经典证明之一是利用二次型的非负性。对于实内积空间，考虑关于实数 \(t\) 的二次函数
\[
f(t) = \langle u + tv, u + tv \rangle = \|v\|^2 t^2 + 2\langle u, v \rangle t + \|u\|^2 \geq 0
\]
由于该二次函数对所有 \(t\) 非负，其判别式必须小于或等于零，即
\[
(2\langle u, v \rangle)^2 - 4\|v\|^2 \|u\|^2 \leq 0
\]
整理后即得 \( |\langle u, v \rangle| \leq \|u\| \|v\| \)。

**Lean4**：在 Mathlib4 中，该不等式已经有成熟的形式化实现 `norm_inner_le_norm`。下面的代码展示了一个教学性的“求和形式”证明，更接近本科生熟悉的代数推导：

```lean
-- ℝⁿ 中的求和形式
theorem cauchy_schwarz_rn {n : ℕ} (x y : Fin n → ℝ) :
    (∑ i : Fin n, x i * y i) ^ 2 ≤ (∑ i : Fin n, (x i) ^ 2) * (∑ i : Fin n, (y i) ^ 2) := by
  -- 将 Fin n → ℝ 视为实内积空间
  have h := cauchy_schwarz_sq (𝕜 := ℝ) (E := Fin n → ℝ) x y
  -- 利用内积与求和的关系化简
  simp [Finset.sum_mul_sum, inner, EuclideanSpace.inner_product_space] at h ⊢
  exact h
```

## 关键 tactic 教学

- `exact`：当目标与某个已知引理或假设完全一致时，直接以此结束证明。例：`exact norm_inner_le_norm u v`。
- `simp`：使用化简规则集（simplifier）自动重写表达式。在 `cauchy_schwarz_rn` 中，`simp [...]` 将内积空间的语言翻译回有限求和的语言。
- `have`：引入一个局部辅助命题，便于分步论证。常用于把大目标拆成小引理。

## 练习

1. 在 Lean4 中证明：若 \(u, v\) 线性相关，则柯西-施瓦茨不等式取等号（提示：使用 `inner_eq_norm_mul_norm_iff`）。
2. 利用柯西-施瓦茨不等式证明三角不等式：\(\|u + v\| \leq \|u\| + \|v\|\)。
3. 写出积分形式的柯西-施瓦茨不等式的 Lean4 陈述（使用 `MeasureSpace` 和 `L²` 空间）。
