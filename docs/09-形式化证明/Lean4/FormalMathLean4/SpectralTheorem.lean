import Mathlib
/-
# 谱定理的形式化证明 / Spectral Theorem

## 定理信息
- **定理名称**: 谱定理（Spectral Theorem）/ 对角化定理
- **数学领域**: 线性代数 / 泛函分析
- **MSC2020编码**: 15A18, 47A10
- **难度级别**: P2

## 定理陈述
设 A 是有限维内积空间上的自伴（厄米特）算子（或矩阵），则：
1. A 的所有特征值都是实数。
2. A 有由特征向量组成的标准正交基。
3. A 可以酉对角化：A = UDU*，其中 U 是酉矩阵，D 是对角矩阵。

## 数学意义
谱定理是线性代数和泛函分析的基石：
1. 保证了自伴算子可以正交对角化
2. 是量子力学中可观测量的数学基础
3. 是主成分分析（PCA）的理论基础
4. 为 C*-代数中的连续函数演算奠定基础

## 历史背景
- 1830s: Cauchy 研究实对称矩阵的特征值
- 1850s: Weierstrass 和 Kronecker 完善了矩阵理论
- 1900s: Hilbert 和 von Neumann 将谱理论推广到无穷维空间
-/

/-
## 核心概念

### 自伴算子 (Self-Adjoint Operator)
内积空间上的线性算子 T 称为自伴的，如果对所有 u, v：
⟨Tu, v⟩ = ⟨u, Tv⟩

### 厄米特矩阵 (Hermitian Matrix)
复方阵 A 称为厄米特的，如果 A = A*（共轭转置）。

### 酉对角化 (Unitary Diagonalization)
矩阵 A 可以表示为 A = UDU*，其中 U 是酉矩阵，D 是对角矩阵。
-/

/-
## 谱定理的证明思路

**有限维版本**:
1. 证明自伴算子的特征值都是实数。
2. 证明不同特征值对应的特征向量正交。
3. 用归纳法证明存在由特征向量组成的标准正交基。
4. 在该基下，算子的矩阵是对角矩阵。

**无穷维版本**（需要更多工具）:
1. 谱测度（Spectral Measure）
2. 泛函演算（Functional Calculus）
-/

/-
## 应用

### 量子力学
自伴算子对应物理可观测量的数学表示，特征值对应测量结果。

### 主成分分析 (PCA)
协方差矩阵是实对称矩阵，谱定理保证了其可以正交对角化。

### 图论
图拉普拉斯矩阵的谱分析依赖于谱定理。
-/

## 与其他定理的关系

| 定理 | 关系 |
|------|------|
| 正规矩阵对角化 | 谱定理的特例（自伴矩阵是正规矩阵） |
| 奇异值分解 (SVD) | 对任意矩阵的推广 |
| Cayley-Hamilton 定理 | 特征多项式的性质 |
| 最小多项式 | 对角化与最小多项式的关系 |

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `Mathlib.LinearAlgebra.Matrix.Spectrum`: 矩阵谱定理
- `Mathlib.Analysis.InnerProductSpace.Spectrum`: 内积空间谱定理
- `Matrix.IsHermitian.spectral_theorem`: 厄米特矩阵的酉对角化
- `LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply`: 自伴算子的特征基
-/

/-
========================================
 Mathlib4 实质化引用 / Materialized References
========================================
本文件已升级为引用 Mathlib4 中的实际定理和定义。
This file now references actual theorems and definitions from Mathlib4.
-
- 模块 / Module: `Mathlib.LinearAlgebra.Matrix.Spectrum`
- 模块 / Module: `Mathlib.Analysis.InnerProductSpace.Spectrum`
- 定理 / Theorem: `Matrix.IsHermitian.spectral_theorem`
-/

#check Matrix.IsHermitian.spectral_theorem

-- Spectral Theorem for Hermitian Matrices
-- 厄米特矩阵的谱定理：A = U D U*，其中 U 是酉矩阵，D 是实对角矩阵
-- Mathlib4 已在 `Mathlib.LinearAlgebra.Matrix.Spectrum` 中完整证明。
open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

-- 谱定理的核心形式：厄米特矩阵可以酉对角化
theorem SpectralTheorem {A : Matrix n n 𝕜} (hA : IsHermitian A) :
    A = (IsHermitian.eigenvectorUnitary hA : Matrix n n 𝕜)
      * diagonal (RCLike.ofReal ∘ IsHermitian.eigenvalues hA)
      * (star (IsHermitian.eigenvectorUnitary hA : Matrix n n 𝕜)) := by
  exact hA.spectral_theorem
