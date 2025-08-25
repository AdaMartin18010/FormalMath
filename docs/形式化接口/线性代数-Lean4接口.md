# 线性代数 - Lean 4 形式化接口

## 概述

本文档提供线性代数核心概念在 Lean 4 中的最小可用接口。

## 基础类型声明

```lean
-- 向量空间类型
class VectorSpace (V : Type v) (α : Type u) [Field α] where
  zero : V
  add : V → V → V
  smul : α → V → V

-- 线性变换类型
structure LinearMap (V W : Type*) [VectorSpace V ℝ] [VectorSpace W ℝ] where
  toFun : V → W
  map_add : ∀ x y, toFun (x + y) = toFun x + toFun y
  map_smul : ∀ c x, toFun (c • x) = c • toFun x

-- 矩阵类型
def Matrix (m n : ℕ) (α : Type*) := Fin m → Fin n → α
```

## 核心概念

```lean
-- 核（Kernel）
def kernel {V W : Type*} [VectorSpace V ℝ] [VectorSpace W ℝ] 
  (T : LinearMap V W) : Set V :=
  { x : V | T.toFun x = 0 }

-- 像（Image）
def image {V W : Type*} [VectorSpace V ℝ] [VectorSpace W ℝ] 
  (T : LinearMap V W) : Set W :=
  { y : W | ∃ x : V, T.toFun x = y }

-- 核的维度
def nullity {V W : Type*} [VectorSpace V ℝ] [VectorSpace W ℝ] 
  (T : LinearMap V W) : ℕ := sorry

-- 像的维度（秩）
def rank {V W : Type*} [VectorSpace V ℝ] [VectorSpace W ℝ] 
  (T : LinearMap V W) : ℕ := sorry
```

## Rank-Nullity 定理

```lean
-- Rank-Nullity 定理
theorem rank_nullity_theorem {V W : Type*} [VectorSpace V ℝ] [VectorSpace W ℝ] 
  (T : LinearMap V W) [FiniteDimensional V ℝ] :
  rank T + nullity T = FiniteDimensional.finrank V ℝ := sorry
```

## 正定矩阵与 Cholesky 分解

```lean
-- 正定矩阵
def positive_definite {α : Type*} [Field α] [LinearOrder α] (A : Matrix n n α) : Prop :=
  symmetric A ∧ ∀ x : Fin n → α, x ≠ 0 → 
    Finset.sum Finset.univ (fun i => 
      Finset.sum Finset.univ (fun j => x i * A i j * x j)) > 0

-- Cholesky 分解
theorem cholesky_decomposition {α : Type*} [Field α] [LinearOrder α] 
  (A : Matrix n n α) (h : positive_definite A) :
  ∃ L : Matrix n n α, lower_triangular L ∧ 
    (∀ i, L i i > 0) ∧ A = matrix_mul L (matrix_transpose L) := sorry
```

## 接口说明

### 设计原则

1. **最小可用**: 只提供核心接口
2. **声明优先**: 重点在类型声明和定理陈述
3. **教学导向**: 便于理解线性代数的形式化表达

### 扩展方向

1. **完整实现**: 补充具体的算法实现
2. **应用扩展**: 扩展到机器学习等领域
3. **验证增强**: 增加更多的定理证明
