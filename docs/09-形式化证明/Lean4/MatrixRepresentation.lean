/-
# 线性变换的矩阵表示 / Matrix Representation of Linear Maps

## Mathlib4 对应
- **模块**: `Mathlib.LinearAlgebra.Matrix.ToLin`, `Mathlib.LinearAlgebra.Basis`
- **核心定理**: `LinearMap.toMatrix`, `Matrix.toLin`

## 定理陈述
设 $T: V \to W$ 是有限维向量空间之间的线性变换，给定 $V$ 的基 $\mathcal{B}$ 和 $W$ 的基 $\mathcal{C}$，
则存在唯一的矩阵 $[T]_{\mathcal{B}}^{\mathcal{C}}$ 使得对任意 $v \in V$ 有
$$[T(v)]_{\mathcal{C}} = [T]_{\mathcal{B}}^{\mathcal{C}} [v]_{\mathcal{B}}.$$
映射 $T \mapsto [T]_{\mathcal{B}}^{\mathcal{C}}$ 是线性同构。
-/

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Basis

namespace MatrixRepresentation

open LinearMap Matrix Module

variable {𝕜 : Type*} [Field 𝕜] {V W : Type*}
  [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
  [AddCommGroup W] [Module 𝕜 W] [FiniteDimensional 𝕜 W]

-- 给定基
variable (B : Basis (Fin (FiniteDimensional.finrank 𝕜 V)) 𝕜 V)
variable (C : Basis (Fin (FiniteDimensional.finrank 𝕜 W)) 𝕜 W)

-- 线性变换到矩阵的映射
theorem lin_to_matrix_exists (T : V →ₗ[𝕜] W) :
    ∃! M : Matrix (Fin (FiniteDimensional.finrank 𝕜 W)) (Fin (FiniteDimensional.finrank 𝕜 V)) 𝕜,
      ∀ v : V, C.repr (T v) = M *ᵥ B.repr v := by
  /- Mathlib4 中由 toMatrix 直接给出 -/
  use toMatrix B C T
  constructor
  · intro v
    simp [toMatrix]
  · intro M hM
    apply Matrix.ext
    intro i j
    /- 验证唯一性 -/
    sorry

-- 矩阵到线性变换的映射
theorem matrix_to_lin_exists
    (M : Matrix (Fin (FiniteDimensional.finrank 𝕜 W)) (Fin (FiniteDimensional.finrank 𝕜 V)) 𝕜) :
    ∃! T : V →ₗ[𝕜] W, toMatrix B C T = M := by
  use toLin B C M
  constructor
  · simp [toLin]
  · intro T hT
    rw [← hT]
    simp [toLin_toMatrix]

-- 复合映射对应矩阵乘法
theorem matrix_of_comp {U : Type*} [AddCommGroup U] [Module 𝕜 U] [FiniteDimensional 𝕜 U]
    (D : Basis (Fin (FiniteDimensional.finrank 𝕜 U)) 𝕜 U)
    (T : V →ₗ[𝕜] W) (S : W →ₗ[𝕜] U) :
    toMatrix B D (S.comp T) = toMatrix C D S * toMatrix B C T := by
  /- 这是 toMatrix 的基本性质 -/
  simp [toMatrix_comp]

end MatrixRepresentation
