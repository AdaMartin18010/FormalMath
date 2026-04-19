---
title: "线性代数核心示例 自然语言与 Lean4 对照"
msc_primary: 68V20
level: "silver"
target_courses:
  - "MIT 18.06"
---

## 定理陈述

**自然语言**：线性代数研究向量空间、线性映射、矩阵与特征值。以下是 MIT 18.06 中的几个核心事实：

1. 向量空间满足八条公理（如分配律、结合律）。
2. 秩-零化度定理：对有限维向量空间上的线性映射 \(f : V \to W\)，有
   \(\dim(\text{range } f) + \dim(\ker f) = \dim V\)。
3. 矩阵乘法满足结合律：\((AB)C = A(BC)\)。

**Lean4**：

```lean
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.LinearMap
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.FiniteDimensional

section VectorSpace
-- 标量乘法对加法的分配律
example {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (c : K) (v w : V) :
    c • (v + w) = c • v + c • w := by
  rw [smul_add]   -- 直接调用模公理
end VectorSpace

section LinearMaps
-- 秩-零化度定理
example {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V]
    (f : V →ₗ[K] W) :
    FiniteDimensional.finrank K (LinearMap.range f) +
    FiniteDimensional.finrank K (LinearMap.ker f) =
    FiniteDimensional.finrank K V := by
  exact LinearMap.finrank_range_add_finrank_ker f
end LinearMaps

section Matrices
-- 矩阵乘法结合律
example {m n p q : Type} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    (A : Matrix m n ℝ) (B : Matrix n p ℝ) (C : Matrix p q ℝ) :
    (A * B) * C = A * (B * C) := by
  rw [Matrix.mul_assoc]
end Matrices
```

## 证明思路

**自然语言**：秩-零化度定理的证明依赖于线性映射基本定理（第一同构定理）：\(V / \ker f \cong \text{range } f\)。由于商空间的维数满足 \(\dim(V / \ker f) = \dim V - \dim(\ker f)\)，代入即得结论。

**Lean4**：Mathlib4 将上述抽象代数证明封装在 `LinearMap.finrank_range_add_finrank_ker` 中。以下展示特征值与特征向量的基本用法：

```lean
section Eigenvalues
-- 特征值是特征多项式的根
example {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [DecidableEq K] (f : V →ₗ[K] V) (μ : K) :
    f.HasEigenvalue μ ↔ f.charpoly.IsRoot μ := by
  rw [f.hasEigenvalue_iff_mem_spectrum]
  rw [mem_spectrum_iff_isRoot]
end Eigenvalues
```

## 关键 tactic 教学

- `rw [lemma1, lemma2]`：连续重写，按从左到右的顺序应用多个等式。
- `exact`：直接提供与目标类型完全一致的证明项，无需进一步分解目标。
- `infer_instance`：当 Lean 需要某个类型类实例（如 `Module ℝ (Fin n → ℝ)`）时，让系统自动推断。

## 练习

1. 在 Lean4 中证明：对任意 \(2 \times 2\) 矩阵，\(\det(A^T) = \det(A)\)。
2. 验证旋转矩阵 \(\begin{pmatrix}\cos\theta & -\sin\theta \\ \sin\theta & \cos\theta\end{pmatrix}\) 的行列式为 \(1\)。
3. 利用 `LinearMap.finrank_range_add_finrank_ker` 解释为什么单射线性映射保持维数（当 \(V = W\) 时）。
