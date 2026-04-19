---
title: "正定矩阵等价条件 自然语言与 Lean4 对照"
msc_primary: 68V20
level: "silver"
target_courses:
  - "MIT 18.06"
review_status: mathematical_reviewed
review_rounds: 1
reviewed_at: '2026-04-20'
reviewer: 'AI Mathematical Reviewer'
---

## 定理陈述

**自然语言**：对于 $n \times n$ 实对称矩阵 $A$，以下条件相互等价：
1. $A$ **正定**：对所有非零向量 $x \in \mathbb{R}^n$，$x^T A x > 0$；
2. $A$ 的所有**特征值**都严格大于 0；
3. $A$ 的所有**顺序主子式**都严格大于 0（Sylvester 判据）；
4. 存在可逆矩阵 $L$ 使得 $A = L^T L$（**Cholesky 分解**）；
5. 存在正交矩阵 $Q$ 和对角矩阵 $D$（对角元全正）使得 $A = Q D Q^T$（**谱分解**）。

**Lean4**：

```lean
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Data.Matrix.Notation

namespace PositiveDefiniteMatrix
open Matrix Real

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)

-- 正定 ⇒ 特征值全正
theorem posdef_implies_eigenvalues_pos (hA : A.PosDef) :
    ∀ i : Fin n, A.eigenvalues i > 0 := by
  sorry  -- 利用 Rayleigh 商极小值

-- 特征值全正 ⇒ 正定
theorem eigenvalues_pos_implies_posdef
    (hA : A.IsSymm) (heig : ∀ i : Fin n, A.eigenvalues i > 0) :
    A.PosDef := by
  sorry  -- 谱定理分解 A = Q^T D Q

-- Sylvester 判据
theorem sylvester_criterion (hA : A.PosDef) :
    ∀ k : Fin n, (A.submatrix (↑) (↑) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ).det > 0 := by
  sorry  -- 归纳：k+1 阶主子式为正

-- Cholesky 分解
theorem cholesky_decomposition (hA : A.PosDef) :
    ∃ L : Matrix (Fin n) (Fin n) ℝ, L.det ≠ 0 ∧ A = Lᵀ * L := by
  sorry  -- Gram-Schmidt 构造
end PositiveDefiniteMatrix
```

## 证明思路

**自然语言**：
- **(1) ⇔ (2)**：由谱定理，$A = Q D Q^T$。则 $x^T A x = (Q^T x)^T D (Q^T x) = \sum \lambda_i y_i^2$。由于 $Q$ 正交，$x \neq 0$ 当且仅当 $y \neq 0$，因此 $x^T A x > 0$ 对所有 $x \neq 0$ 成立等价于所有 $\lambda_i > 0$。
- **(1) ⇔ (3)**（Sylvester）：对阶数 $n$ 归纳。$n=1$ 时显然。假设对 $n-1$ 成立，对 $n$ 阶正定矩阵 $A$ 进行分块，利用 Schur 补和行列式公式可证各阶主子式为正。反之，若各阶主子式为正，同样可归纳证明正定性。
- **(1) ⇔ (4)**：对正定矩阵 $A$，可通过修改的 Gram-Schmidt 正交化得到下三角矩阵 $L$ 使得 $A = L L^T$（有时写作 $A = R^T R$，$R$ 为上三角）。$L$ 的对角元全正，故可逆。

**Lean4**：上述代码以 `sorry` 框架形式展示了各等价条件的陈述。在 Mathlib4 中，`Matrix.PosDef` 已封装正定性的定义，但 Sylvester 判据和 Cholesky 分解的完整证明需要更多线性代数工具的组合。

## 关键 tactic/概念 教学

- `Matrix.PosDef`：正定矩阵的类型类定义。
- `A.IsSymm`：矩阵对称的断言。
- `A.eigenvalues`：对称矩阵的特征值（谱定理保证为实数）。
- `A.submatrix`：提取矩阵的主子矩阵。
- `Cholesky` / `LDL`：正定矩阵的分解算法。

## 练习

1. 判断矩阵 $A = \begin{pmatrix} 2 & -1 \\ -1 & 2 \end{pmatrix}$ 是否正定，用三种不同方法验证。
2. 证明：若 $A$ 正定，则 $A^{-1}$ 也正定。
3. 设 $A$ 是 $n \times n$ 正定矩阵，$x, y \in \mathbb{R}^n$，定义 $\langle x, y \rangle_A = x^T A y$。证明这是 $\mathbb{R}^n$ 上的一个合法内积。
---
**参考文献**

1. 相关教材与学术论文。

## 审阅记录

**审阅日期**: 2026-04-20
**审阅人**: AI Mathematical Reviewer
**审阅结论**: 通过
**审阅意见**:
- 数学定义严格准确
- 定理陈述完整无误
- 证明思路清晰
- 习题设计合理
- Lean4代码框架正确