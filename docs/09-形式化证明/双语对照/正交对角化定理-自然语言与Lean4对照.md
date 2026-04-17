---
title: "正交对角化定理（实对称矩阵谱定理） 自然语言与 Lean4 对照"
level: "silver"
target_courses:
  - "MIT 18.06"
---

## 定理陈述

**自然语言**：设 \(A\) 是 \(n \times n\) 实对称矩阵（即 \(A^{\mathsf{T}} = A\)），则存在正交矩阵 \(Q\)（即 \(Q^{\mathsf{T}} Q = I\)）和对角矩阵 \(D\)，使得
\[
A = Q D Q^{\mathsf{T}}.
\]
等价地，实对称矩阵的所有特征值都是实数，且不同特征值对应的特征向量彼此正交。

**Lean4**：

```lean
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Analysis.InnerProductSpace.PiL2

universe u
namespace SpectralTheoremRealSymmetric
open Matrix Real

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)

-- 实对称矩阵的定义
def IsSymmetricMatrix : Prop := Aᵀ = A

-- 正交对角化定理（框架）
theorem spectral_theorem_real_symmetric (hA : IsSymmetricMatrix A) :
    ∃ (Q D : Matrix (Fin n) (Fin n) ℝ),
      Qᵀ * Q = 1 ∧ D.IsDiagonal ∧
      A = Q * D * Qᵀ := by
  sorry

-- 特征值均为实数（框架）
theorem eigenvalues_real (hA : IsSymmetricMatrix A) (μ : ℂ)
    (hμ : A.charpoly.IsRoot μ) :
    μ.im = 0 := by
  sorry
end SpectralTheoremRealSymmetric
```

## 证明思路

**自然语言**：对矩阵阶数 \(n\) 使用数学归纳法。

1. **基例**：\(n=1\) 时，\(1 \times 1\) 矩阵本身就是对角矩阵，结论显然成立。
2. **归纳步骤**：假设结论对 \(n-1\) 阶实对称矩阵成立。
   - **存在实特征值**：实对称矩阵的特征多项式是实系数多项式。对任意特征值 \(\lambda\) 及对应的特征向量 \(\mathbf{v}\)（可能为复向量），利用对称性有
     \[
     \lambda \langle \mathbf{v}, \mathbf{v} \rangle = \langle A\mathbf{v}, \mathbf{v} \rangle = \langle \mathbf{v}, A\mathbf{v} \rangle = \bar{\lambda} \langle \mathbf{v}, \mathbf{v} \rangle,
     \]
     故 \(\lambda = \bar{\lambda}\)，即 \(\lambda\) 是实数。
   - **构造正交矩阵**：取对应于 \(\lambda_1\) 的单位实特征向量 \(\mathbf{q}_1\)，将其扩充为 \(\mathbb{R}^n\) 的一组标准正交基 \(\{\mathbf{q}_1, \dots, \mathbf{q}_n\}\)。令 \(Q_1 = [\mathbf{q}_1, \dots, \mathbf{q}_n]\)，则 \(Q_1\) 是正交矩阵，且
     \[
     Q_1^{\mathsf{T}} A Q_1 = \begin{pmatrix} \lambda_1 & 0 \\ 0 & A_1 \end{pmatrix},
     \]
     其中 \(A_1\) 是 \((n-1) \times (n-1)\) 实对称矩阵。
   - **应用归纳假设**：对 \(A_1\) 应用归纳假设，得到正交矩阵 \(Q_2\) 使得 \(Q_2^{\mathsf{T}} A_1 Q_2\) 为对角矩阵。从而
     \[
     A = Q_1 \begin{pmatrix} 1 & 0 \\ 0 & Q_2 \end{pmatrix} D \begin{pmatrix} 1 & 0 \\ 0 & Q_2^{\mathsf{T}} \end{pmatrix} Q_1^{\mathsf{T}},
     \]
     令 \(Q = Q_1 \begin{pmatrix} 1 & 0 \\ 0 & Q_2 \end{pmatrix}\)，即得 \(A = QDQ^{\mathsf{T}}\)。

**Lean4**：由于实对称矩阵的谱定理在 Mathlib4 中的完整形式化涉及较深的分析学和内积空间理论，目前以框架形式给出定理陈述。`spectral_theorem_real_symmetric` 断言了正交矩阵 \(Q\) 和对角矩阵 \(D\) 的存在性；`eigenvalues_real` 断言了特征值的实性。

## 关键 tactic/概念 教学

- `Aᵀ = A`：在 Lean 中表达实对称矩阵的条件。
- `Qᵀ * Q = 1`：正交矩阵的定义（\(Q^{\mathsf{T}} Q = I\)）。
- `D.IsDiagonal`：对角矩阵的性质。
- `charpoly.IsRoot`：特征值作为特征多项式的根的定义。
- 谱定理的证明核心在于**归纳法**、**实特征值的存在性**以及**正交基的扩充**（Gram-Schmidt 过程）。

## 练习

1. 证明：实对称矩阵不同特征值对应的特征向量必然正交。
2. 写出一个 \(2 \times 2\) 实对称矩阵 \(A = \begin{pmatrix} a & b \\ b & d \end{pmatrix}\) 的特征值显式公式，并构造正交对角化 \(A = QDQ^{\mathsf{T}}\)。
3. 在 Lean4 中验证：若 \(A\) 是实对称矩阵且正定，则其所有特征值严格大于 0。
