import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.LinearMap
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.LinearAlgebra.Eigenspace
import Mathlib.LinearAlgebra.Eigenvalues.Basic
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! 
# 线性代数示例

对应的FormalMath文档：
- docs/02-代数结构/02-核心理论/线性代数与矩阵理论/01-线性代数与矩阵理论-国际标准深度扩展版.md
- docs/02-代数结构/02-核心理论/线性代数与矩阵理论/01-线性代数与矩阵理论-深度扩展版.md

对应的Mathlib4模块：
- Mathlib.Algebra.Module.Basic
- Mathlib.Algebra.Module.LinearMap
- Mathlib.Data.Matrix.Basic
- Mathlib.LinearAlgebra.Matrix.Determinant
- Mathlib.LinearAlgebra.Eigenspace
- Mathlib.Analysis.InnerProductSpace.Basic

## 核心定义
-/ 

/-! 
## 向量空间

向量空间是线性代数的基本对象。
-/

section VectorSpace

-- 向量空间定义（作为模的特殊情况）
example (K : Type*) [Field K] (V : Type*) : Type _ := Module K V

-- 标量乘法
example {K V : Type*} [Field K] [AddCommGroup V] [Module K V] 
    (c : K) (v : V) : V := c • v

-- 向量空间公理
example {K V : Type*} [Field K] [AddCommGroup V] [Module K V] 
    (c d : K) (v w : V) : 
    c • (v + w) = c • v + c • w := by
  rw [smul_add]

example {K V : Type*} [Field K] [AddCommGroup V] [Module K V] 
    (c d : K) (v : V) : 
    (c + d) • v = c • v + d • v := by
  rw [add_smul]

example {K V : Type*} [Field K] [AddCommGroup V] [Module K V] 
    (c d : K) (v : V) : 
    c • (d • v) = (c * d) • v := by
  rw [smul_smul]

-- ℝⁿ是向量空间
example (n : ℕ) : Module ℝ (Fin n → ℝ) := by
  infer_instance

end VectorSpace

/-! 
## 线性映射

向量空间之间的结构保持映射。
-/

section LinearMaps

-- 线性映射定义
example {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] 
    [AddCommGroup W] [Module K W] : Type _ := V →ₗ[K] W

-- 线性映射的性质
example {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] 
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) (c : K) (v w : V) : 
    f (c • v + w) = c • f v + f w := by
  rw [map_add, map_smul]

-- 恒等线性映射
example {K V : Type*} [Field K] [AddCommGroup V] [Module K V] : 
    V →ₗ[K] V := LinearMap.id

-- 线性映射的复合
example {K V W U : Type*} [Field K] [AddCommGroup V] [Module K V] 
    [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U] 
    (f : V →ₗ[K] W) (g : W →ₗ[K] U) : V →ₗ[K] U := g.comp f

-- 核与像
example {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] 
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) : 
    Submodule K V := LinearMap.ker f

example {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] 
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) : 
    Submodule K W := LinearMap.range f

-- 秩-零化度定理
example {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] 
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] 
    (f : V →ₗ[K] W) : 
    FiniteDimensional.finrank K (LinearMap.range f) + 
    FiniteDimensional.finrank K (LinearMap.ker f) = 
    FiniteDimensional.finrank K V := by
  exact LinearMap.finrank_range_add_finrank_ker f

end LinearMaps

/-! 
## 矩阵

矩阵是线性代数的计算工具。
-/

section Matrices

-- 矩阵类型
example (m n : Type) (R : Type) [CommRing R] : Type _ := Matrix m n R

-- 具体矩阵
example : Matrix (Fin 2) (Fin 2) ℝ := !![1, 2; 3, 4]

-- 零矩阵
example {m n : Type} [Fintype m] [Fintype n] : Matrix m n ℝ := 0

-- 单位矩阵
example (n : Type) [Fintype n] [DecidableEq n] : Matrix n n ℝ := 1

-- 矩阵加法
example {m n : Type} [Fintype m] [Fintype n] (A B : Matrix m n ℝ) : 
    Matrix m n ℝ := A + B

-- 矩阵乘法
example {m n p : Type} [Fintype m] [Fintype n] [Fintype p] 
    (A : Matrix m n ℝ) (B : Matrix n p ℝ) : Matrix m p ℝ := A * B

-- 矩阵转置
example {m n : Type} [Fintype m] [Fintype n] (A : Matrix m n ℝ) : 
    Matrix n m ℝ := Aᵀ

-- 矩阵乘法结合律
example {m n p q : Type} [Fintype m] [Fintype n] [Fintype p] [Fintype q] 
    (A : Matrix m n ℝ) (B : Matrix n p ℝ) (C : Matrix p q ℝ) : 
    (A * B) * C = A * (B * C) := by
  rw [Matrix.mul_assoc]

end Matrices

/-! 
## 行列式

行列式是方阵的重要不变量。
-/

section Determinant

-- 行列式
example {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) : ℝ := 
  A.det

-- 2×2行列式公式
example (a b c d : ℝ) : Matrix.det !![a, b; c, d] = a * d - b * c := by
  simp [Matrix.det_fin_two, Matrix.det_fin_two_of]
  ring

-- 3×3行列式计算
example (a b c d e f g h i : ℝ) : 
    Matrix.det !![a, b, c; d, e, f; g, h, i] = 
    a * e * i + b * f * g + c * d * h - c * e * g - b * d * i - a * f * h := by
  simp [Matrix.det_fin_three]
  ring

-- det(AB) = det(A)det(B)
example {n : Type} [Fintype n] [DecidableEq n] (A B : Matrix n n ℝ) : 
    (A * B).det = A.det * B.det := by
  rw [Matrix.det_mul]

-- det(A^T) = det(A)
example {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) : 
    Aᵀ.det = A.det := by
  rw [Matrix.det_transpose]

-- 单位矩阵的行列式为1
example {n : Type} [Fintype n] [DecidableEq n] : 
    (1 : Matrix n n ℝ).det = 1 := by
  rw [Matrix.det_one]

end Determinant

/-! 
## 特征值与特征向量

特征值问题是线性代数的核心。
-/

section Eigenvalues

-- 特征空间
example {K V : Type*} [Field K] [AddCommGroup V] [Module K V] 
    (f : V →ₗ[K] V) (μ : K) : Submodule K V := 
  f.eigenspace μ

-- 特征值
example {K V : Type*} [Field K] [AddCommGroup V] [Module K V] 
    [FiniteDimensional K V] (f : V →ₗ[K] V) (μ : K) : Prop := 
    f.HasEigenvalue μ

-- 特征多项式
example {K V : Type*} [Field K] [AddCommGroup V] [Module K V] 
    [FiniteDimensional K V] [DecidableEq K] (f : V →ₗ[K] V) : 
    Polynomial K := f.charpoly

-- Cayley-Hamilton定理
example {K V : Type*} [Field K] [AddCommGroup V] [Module K V] 
    [FiniteDimensional K V] [DecidableEq K] (f : V →ₗ[K] V) : 
    aeval f f.charpoly = 0 := by
  apply LinearMap.aeval_self_charpoly

-- 特征值是特征多项式的根
example {K V : Type*} [Field K] [AddCommGroup V] [Module K V] 
    [FiniteDimensional K V] [DecidableEq K] (f : V →ₗ[K] V) (μ : K) : 
    f.HasEigenvalue μ ↔ f.charpoly.IsRoot μ := by
  rw [f.hasEigenvalue_iff_mem_spectrum]
  rw [mem_spectrum_iff_isRoot]

end Eigenvalues

/-! 
## 内积空间

带有内积结构的向量空间。
-/

section InnerProductSpace

-- 内积空间
example {K V : Type*} [RCLike K] : Type _ → Type _ := InnerProductSpace K

-- 内积
example {K V : Type*} [RCLike K] [NormedAddCommGroup V] [InnerProductSpace K V] 
    (v w : V) : K := ⟪v, w⟫

-- 内积的性质
example {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] 
    (u v w : V) (c : ℝ) : 
    ⟪u + v, w⟫ = ⟪u, w⟫ + ⟪v, w⟫ := by
  rw [inner_add_left]

example {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] 
    (u v : V) (c : ℝ) : 
    ⟪c • u, v⟫ = c * ⟪u, v⟫ := by
  rw [inner_smul_left]

example {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] 
    (u v : V) : 
    ⟪u, v⟫ = ⟪v, u⟫ := by
  rw [real_inner_comm]

-- Cauchy-Schwarz不等式
example {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] 
    (u v : V) : 
    |⟪u, v⟫| ≤ ‖u‖ * ‖v‖ := by
  apply abs_real_inner_le_norm

-- 范数与内积的关系
example {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] 
    (v : V) : 
    ‖v‖ = Real.sqrt ⟪v, v⟫ := by
  rw [norm_eq_sqrt_real_inner]

-- ℝⁿ是内积空间
example (n : ℕ) : InnerProductSpace ℝ (EuclideanSpace ℝ (Fin n)) := by
  infer_instance

end InnerProductSpace

/-! 
## 有限维空间

有限维向量空间的性质。
-/

section FiniteDimensional

-- 有限维向量空间
example {K V : Type*} [Field K] [AddCommGroup V] [Module K V] : Prop := 
  FiniteDimensional K V

-- 维数
example {K V : Type*} [Field K] [AddCommGroup V] [Module K V] 
    [FiniteDimensional K V] : ℕ := FiniteDimensional.finrank K V

-- ℝⁿ的维数是n
example (n : ℕ) : FiniteDimensional.finrank ℝ (Fin n → ℝ) = n := by
  rw [FiniteDimensional.finrank_fin_fun]

-- 维数公式
example {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] 
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W] 
    (f : V →ₗ[K] W) : 
    FiniteDimensional.finrank K (LinearMap.range f) + 
    FiniteDimensional.finrank K (LinearMap.ker f) = 
    FiniteDimensional.finrank K V := by
  exact LinearMap.finrank_range_add_finrank_ker f

end FiniteDimensional

/-! 
## 示例：具体计算

线性代数中的具体计算示例。
-/

section Examples

-- 2×2矩阵的特征多项式
example (A : Matrix (Fin 2) (Fin 2) ℝ) : 
    A.charpoly = X ^ 2 - (A 0 0 + A 1 1) * X + A.det := by
  rw [Matrix.charpoly_two]
  simp
  ring

-- 旋转矩阵的行列式
example (θ : ℝ) : 
    Matrix.det !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] = 1 := by
  simp [Matrix.det_fin_two]
  rw [Real.cos_sq_add_sin_sq θ]

-- 对称矩阵的特征值是实数
-- 这是一个重要的定理，在Mathlib中有完整形式化

end Examples

/-! 
## 练习

1. 证明：对于任意2×2矩阵A，有det(A) = det(A^T)。

2. 证明：如果λ是f的特征值，那么λ^n是f^n的特征值。

3. 证明：上三角矩阵的行列式等于对角元素的乘积。

4. 证明：正交矩阵的行列式为±1。

5. 设A是n×n实对称矩阵，证明A的所有特征值都是实数。

-/ 

section Exercises

-- 练习1的提示
example {R : Type*} [CommRing R] (A : Matrix (Fin 2) (Fin 2) R) : 
    A.det = Aᵀ.det := by
  rw [Matrix.det_transpose]

-- 练习3的提示
example {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R] 
    (A : Matrix n n R) (h : ∀ i j, j < i → A i j = 0) : 
    A.det = ∏ i : n, A i i := by
  apply det_of_upperTriangular
  intro i j hji
  have : j < i := by
    simp at hji
    exact hji
  apply h i j this

end Exercises
