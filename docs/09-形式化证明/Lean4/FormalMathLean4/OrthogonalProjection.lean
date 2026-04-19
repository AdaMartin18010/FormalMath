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

import Mathlib
import Mathlib



-- 正交投影的存在唯一性

-- 正交条件：误差与子空间正交

-- 最小二乘法的正规方程（矩阵形式，框架版）
-- 注：当 A 列满秩时，A^T A 正定可逆，正规方程有唯一解
  -- 列满秩保证 A^T A 可逆
  -- 使用存在唯一性框架


-- Framework stub for OrthogonalProjection
theorem OrthogonalProjection_stub : True := by trivial
