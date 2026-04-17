/-
# 正交投影与最小二乘 / Orthogonal Projection and Least Squares

## Mathlib4 对应
- **模块**: `Mathlib.Analysis.InnerProductSpace.Projection`, `Mathlib.LinearAlgebra.Matrix.PosDef`
- **核心定理**: `exists_norm_eq_iInf_of_complete_convex`, `orthogonalProjection_eq_linear_proj`

## 定理陈述
设 $V$ 是内积空间，$W \subseteq V$ 是完备子空间，则对任意 $v \in V$，存在唯一的 $w \in W$ 使得
$$\|v - w\| = \inf_{w' \in W} \|v - w'\|.$$
该 $w$ 称为 $v$ 在 $W$ 上的正交投影，且满足 $(v - w) \perp W$。

## 最小二乘法
对于不相容方程组 $Ax = b$，最小二乘解满足正规方程 $A^T A x = A^T b$。
-/

import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace OrthogonalProjection

open InnerProductSpace Real

-- 正交投影的存在唯一性
theorem orthogonal_projection_exists {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {K : Submodule 𝕜 E} [CompleteSpace K] (u : E) :
    ∃! v : K, ‖u - v‖ = ⨅ w : K, ‖u - w‖ := by
  /- 这是内积空间投影定理的核心结论 -/
  exact exists_norm_eq_iInf_of_complete_convex K u

-- 正交条件：误差与子空间正交
theorem orthogonal_condition {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {K : Submodule 𝕜 E} [CompleteSpace K] {u : E} {v : K}
    (hv : ‖u - v‖ = ⨅ w : K, ‖u - w‖) :
    ∀ w : K, ⟪u - v, w⟫_𝕜 = 0 := by
  /- 由投影的极小性导出正交条件。
     这是内积空间投影的基本性质。 -/
  intro w
  have h := orthogonalProjection_fnorm_sq K u
  have h' := orthogonalProjection_inner_eq_zero K u w
  simpa using h'

-- 最小二乘法的正规方程（矩阵形式，框架版）
-- 注：当 A 列满秩时，A^T A 正定可逆，正规方程有唯一解
theorem normal_equations {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hA : Matrix.rank A = n) :
    ∃! x : Fin n → ℝ, Aᵀ * A * vec x = Aᵀ * vec b := by
  /- 当 A 列满秩时，A^T A 是 n×n 正定矩阵，从而可逆。
     因此正规方程 N x = A^T b（其中 N = A^T A）有唯一解 x = N^{-1} A^T b。
     完整的形式化证明需要 Mathlib 中关于矩阵正定性、可逆性和 vec 运算的深入结果。 -/
  -- 列满秩保证 A^T A 可逆
  -- 使用存在唯一性框架
  sorry

end OrthogonalProjection
