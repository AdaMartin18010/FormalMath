/-
# 凯莱-哈密顿定理的形式化证明 / Cayley-Hamilton Theorem

## 领域
线性代数 (Linear Algebra)

## Mathlib4对应
- **模块**: `Mathlib.LinearAlgebra.Matrix.Charpoly.CayleyHamilton`
- **核心定理**: `Matrix.aeval_self_charpoly`
- **相关定义**:
  - `Matrix.charpoly`: 特征多项式
  - `Matrix.eval`: 矩阵多项式求值
  - `aeval`: 代数同态求值

## MSC2020编码
- **Primary**: 15A24
- **Secondary**: 15A18

## 对齐课程
- MIT 18.06 (Linear Algebra)
- Harvard Math 21b (Linear Algebra and Differential Equations)
- Princeton MAT 202 (Linear Algebra with Applications)
- ETH 401-0131-00L (Linear Algebra I)

## 定理陈述
设 A 是域 𝕂 上的 n×n 矩阵，p(λ) = det(λI - A) 是 A 的特征多项式，则：
p(A) = 0

即每个方阵都满足自己的特征方程。

## 数学意义
凯莱-哈密顿定理是线性代数中最优美的定理之一，它将矩阵与多项式理论紧密联系起来。

## 历史背景
由Arthur Cayley在1858年对2×2矩阵证明，William Rowan Hamilton在1853年对四元数证明了相关结果，一般情形由Ferdinand Frobenius在1878年证明。
-/

import Mathlib.LinearAlgebra.Matrix.Charpoly.CayleyHamilton
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Data.Matrix.Basic
import Mathlib.RingTheory.Polynomial.Basic

universe u v w

namespace CayleyHamiltonTheorem

open Matrix Polynomial

/-
## 核心概念

### 特征多项式 (Characteristic Polynomial)
对于 n×n 矩阵 A，其特征多项式定义为：
χ_A(λ) = det(λI_n - A)

这是一个 n 次首一多项式。

### 矩阵多项式 (Matrix Polynomial)
若 p(x) = a₀ + a₁x + ... + aₙxⁿ，则矩阵多项式为：
p(A) = a₀I + a₁A + ... + aₙAⁿ

### 凯莱-哈密顿定理
每个方阵都满足自己的特征多项式：χ_A(A) = 0
-/

variable {R : Type u} [CommRing R] {n : Type v} [Fintype n] [DecidableEq n]

-- 特征多项式的定义（使用Mathlib4的实现）
def CharacteristicPolynomial (A : Matrix n n R) : R[X] :=
  A.charpoly

-- 凯莱-哈密顿定理：p(A) = 0
theorem cayley_hamilton (A : Matrix n n R) :
    aeval A A.charpoly = 0 := by
  /- 使用Mathlib4的凯莱-哈密顿定理 -/
  exact Matrix.aeval_self_charpoly A

-- 等价表述：矩阵满足自己的特征方程
theorem matrix_satisfies_charpoly (A : Matrix n n R) :
    A.charpoly.eval A = 0 := by
  /- eval与aeval的等价形式 -/
  exact Matrix.eval_self_charpoly A

-- 2×2矩阵的凯莱-哈密顿定理（显式计算）
theorem cayley_hamilton_2x2 {R : Type u} [CommRing R] (A : Matrix (Fin 2) (Fin 2) R) :
    A ^ 2 - (A 0 0 + A 1 1) • A + (A 0 0 * A 1 1 - A 0 1 * A 1 0) • 1 = 0 := by
  /- 对于2×2矩阵，特征多项式为 λ² - tr(A)λ + det(A) -/
  have h := cayley_hamilton A
  /- 展开特征多项式在A处的求值 -/
  simp [charpoly, charmatrix, Matrix.det_fin_two] at h
  /- 整理得到显式形式 -/
  simpa using h

/-
## 应用：矩阵的幂

凯莱-哈密顿定理可用于将高次幂的矩阵表示为低次幂的线性组合。
对于 n×n 矩阵 A，任何 A^k (k ≥ n) 都可以表示为 I, A, ..., A^(n-1) 的线性组合。
-/

-- 若 A 满足 p(A) = 0，则 A^n 可用低次幂表示（axiom占位）
axiom matrix_power_reduction (A : Matrix n n R) (k : ℕ) (hk : Fintype.card n ≤ k) :
    ∃ (c : Fin (Fintype.card n) → R), A ^ k = ∑ i : Fin (Fintype.card n), c i • A ^ i.val

/-
## 应用：逆矩阵公式

对于可逆矩阵 A，其逆矩阵可以用特征多项式的系数表示。
由 χ_A(A) = Aⁿ + c_{n-1}A^{n-1} + ... + c₁A + c₀I = 0
若 A 可逆，则 det(A) = (-1)ⁿc₀ ≠ 0，于是：
A⁻¹ = -1/c₀ (A^{n-1} + c_{n-1}A^{n-2} + ... + c₁I)
-/

-- 可逆矩阵的逆可用A的幂表示（axiom占位）
axiom inverse_from_charpoly {R : Type u} [Field R] {n : Type v} [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (hA : Invertible A) :
    ∃ (c : Fin (Fintype.card n) → R), A⁻¹ = ∑ i : Fin (Fintype.card n), c i • A ^ i.val

end CayleyHamiltonTheorem

/-
## 应用示例

### 计算矩阵的幂

```lean
-- 设 A 是 2×2 矩阵，则 A² = tr(A)·A - det(A)·I
example {R : Type*} [CommRing R] (A : Matrix (Fin 2) (Fin 2) R) :
    A ^ 2 = (A 0 0 + A 1 1) • A - (A 0 0 * A 1 1 - A 0 1 * A 1 0) • 1 := by
  have h := cayley_hamilton_2x2 A
  linear_combination -h
```

## 数学意义

凯莱-哈密顿定理的重要性：

1. **结构定理**: 揭示矩阵与多项式之间的深刻联系
2. **计算工具**: 将高次矩阵幂降为低次组合
3. **最小多项式**: 最小多项式整除特征多项式
4. **若尔当标准形**: 是若尔当标准形理论的基础之一

## 与其他定理的关系

- **特征值理论**: 特征多项式的根就是特征值
- **最小多项式**: 最小多项式也满足 p(A) = 0
- **有理标准形**: 基于不变因子的矩阵分类
- **若尔当标准形**: 基于初等因子的矩阵分类

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `Mathlib.LinearAlgebra.Matrix.Charpoly.CayleyHamilton`: 凯莱-哈密顿定理
- `Matrix.aeval_self_charpoly`: 代数求值版本的核心定理
- `Matrix.eval_self_charpoly`: 直接求值版本
- `Matrix.charpoly`: 特征多项式的定义
-/
