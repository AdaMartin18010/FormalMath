---
title: "SVD 存在定理 自然语言与 Lean4 对照"
level: "silver"
target_courses:
  - "MIT 18.06"
---

## 定理陈述

**自然语言**：设 \(A\) 是 \(m \times n\) 实矩阵，则存在正交矩阵 \(U \in \mathbb{R}^{m \times m}\)、\(V \in \mathbb{R}^{n \times n}\) 和一个对角矩阵 \(\Sigma \in \mathbb{R}^{m \times n}\)（其对角线元素 \(\sigma_1 \geq \sigma_2 \geq \dots \geq 0\) 称为奇异值），使得
\[
A = U \Sigma V^{\mathsf{T}}.
\]

**Lean4**：

```lean
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

universe u
namespace SVDTheorem
open Matrix Real

variable {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)

-- 对角矩阵（矩形版本，仅在 min m n 范围内有对角线元素）
structure RectDiagonal (m n : ℕ) (R : Type*) [Zero R] where
  vals : Fin (min m n) → R
  toMatrix : Matrix (Fin m) (Fin n) R :=
    fun i j => if h : i.val = j.val then vals ⟨i.val, by simp [h]⟩ else 0

-- SVD 存在定理（框架）
theorem svd_existence :
    ∃ (U : Matrix (Fin m) (Fin m) ℝ) (Σ : Matrix (Fin m) (Fin n) ℝ)
      (V : Matrix (Fin n) (Fin n) ℝ),
      Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧
      ∃ (σ : Fin (min m n) → ℝ),
        (∀ i, σ i ≥ 0) ∧
        (∀ i j, Σ i j = if h : i.val = j.val then σ ⟨i.val, by simp [h]⟩ else 0) ∧
        A = U * Σ * Vᵀ := by
  sorry
end SVDTheorem
```

## 证明思路

**自然语言**：奇异值分解（SVD）的存在性证明通常基于实对称矩阵的谱定理，具体步骤如下。

1. 考虑矩阵 \(A^{\mathsf{T}} A\)，它是 \(n \times n\) 实对称半正定矩阵。由谱定理，存在正交矩阵 \(V\) 和对角矩阵 \(D = \operatorname{diag}(\lambda_1, \dots, \lambda_n)\) 使得 \(A^{\mathsf{T}} A = V D V^{\mathsf{T}}\)，其中 \(\lambda_i \geq 0\)。
2. 定义奇异值 \(\sigma_i = \sqrt{\lambda_i}\)。令 \(\Sigma\) 为 \(m \times n\) 矩阵，其对角线前 \(r = \operatorname{rank}(A)\) 个元素为 \(\sigma_1, \dots, \sigma_r\)，其余为 0。
3. 对 \(i = 1, \dots, r\)，令 \(\mathbf{u}_i = \frac{1}{\sigma_i} A \mathbf{v}_i\)。可以验证 \(\{\mathbf{u}_1, \dots, \mathbf{u}_r\}\) 是 \(\mathbb{R}^m\) 中的标准正交组。
4. 将 \(\{\mathbf{u}_1, \dots, \mathbf{u}_r\}\) 扩充为 \(\mathbb{R}^m\) 的标准正交基 \(\{\mathbf{u}_1, \dots, \mathbf{u}_m\}\)，令 \(U = [\mathbf{u}_1, \dots, \mathbf{u}_m]\)。
5. 验证 \(A \mathbf{v}_i = \sigma_i \mathbf{u}_i\) 对所有 \(i\) 成立（对 \(i > r\)，两边均为 0）。因此 \(A V = U \Sigma\)，即 \(A = U \Sigma V^{\mathsf{T}}\)。

**Lean4**：SVD 的完整形式化在 Mathlib4 中尚未成熟，上述代码以 `sorry` 框架给出了定理的精确陈述，包括正交矩阵 \(U, V\)、奇异值序列 \(\sigma\) 以及矩形对角矩阵 \(\Sigma\) 的构造。

## 关键 tactic/概念 教学

- `Aᵀ * A`：构造 Gram 矩阵，它是 SVD 证明的出发点。
- `min m n`：奇异值的个数由矩阵的行数和列数中较小者决定。
- `if h : i.val = j.val then ... else 0`：在 Lean 中定义矩形对角矩阵的常用技巧。
- SVD 与谱定理的关系：\(A^{\mathsf{T}} A\) 的特征值开方即得奇异值。

## 练习

1. 证明：\(A\) 的秩等于其非零奇异值的个数。
2. 设 \(A\) 是 \(2 \times 2\) 可逆矩阵，写出其 SVD 中奇异值与 \(A^{\mathsf{T}} A\) 特征值的关系。
3. 在 Lean4 中构造一个具体的 \(2 \times 3\) 矩阵，并尝试写出其 SVD 的显式形式（手工计算）。
