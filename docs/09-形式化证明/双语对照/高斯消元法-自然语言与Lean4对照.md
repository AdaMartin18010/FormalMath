---
title: "高斯消元法 自然语言与 Lean4 对照"
msc_primary: 68V20
level: "silver"
target_courses:
  - "MIT 18.06"
---

## 定理陈述

**自然语言**：高斯消元法（Gaussian Elimination）是求解线性方程组、计算矩阵秩、求逆矩阵的核心算法。其基本定理表述为：任何域上的 $m \times n$ 矩阵 $A$ 都可以通过有限次**初等行变换**化为**行阶梯形**（row echelon form）。进而，线性方程组 $Ax = b$ 有解当且仅当增广矩阵 $[A \mid b]$ 的行阶梯形中不存在形如 $[0 \; 0 \; \cdots \; 0 \mid c]$（$c \neq 0$）的矛盾行。

**Lean4**：

```lean
import Mathlib.LinearAlgebra.Matrix.Basic
import Mathlib.Data.Matrix.Notation

namespace GaussianElimination
open Matrix

-- 初等行变换
def applyRowOp {m n : ℕ} {α : Type*} [Field α]
    (op : ElementaryRowOp m n α) (A : Matrix (Fin m) (Fin n) α) :
    Matrix (Fin m) (Fin n) α :=
  match op with
  | swap i j =>
      fun r c => if r = i then A j c else if r = j then A i c else A r c
  | scale i c _ =>
      fun r c => if r = i then c * A i c else A r c
  | add_multiple i j c =>
      fun r c => if r = i then A i c + c * A j c else A r c

-- 任何矩阵可化为行阶梯形
theorem gaussian_elimination {m n : ℕ} {α : Type*} [Field α]
    (A : Matrix (Fin m) (Fin n) α) :
    ∃ ops : List (ElementaryRowOp m n α),
      IsRowEchelonForm (ops.reverse.foldl (fun M op => applyRowOp op M) A) := by
  sorry  -- 对行数/列数归纳

-- 有解判定
theorem linear_system_solution {m n : ℕ} {α : Type*} [Field α]
    (A : Matrix (Fin m) (Fin n) α) (b : Fin m → α) :
    (∃ x : Fin n → α, A.mulVec x = b) ↔ (A.augment b).rank = A.rank := by
  sorry
end GaussianElimination
```

## 证明思路

**自然语言**：高斯消元法的算法性证明通过对矩阵的行数或列数进行归纳：
1. 若矩阵为零矩阵，已处于行阶梯形。
2. 否则，找到最左侧的非零列（主元列），通过行交换将非零元移至第一行。
3. 用倍加变换将该列中其余行的元素消为 0。
4. 对右下角的子矩阵递归执行上述步骤。

对于线性方程组 $Ax = b$，初等行变换不改变解集。化为行阶梯形后，若出现 $0 = c$（$c \neq 0$）则方程组不相容；否则，每个主元列对应一个基本变量，非主元列对应自由变量，方程组有解。

**Lean4**：上述代码以框架形式定义了初等行变换和行阶梯形的概念。完整的形式化证明需要对矩阵维度进行结构归纳，并严格验证每种行变换保持解集不变。`augment` 构造增广矩阵，`rank` 则基于行阶梯形中非零行的数量。

## 关键 tactic/概念 教学

- `Matrix (Fin m) (Fin n) α`：$m \times n$ 的 $\alpha$-系数矩阵类型。
- `Field α`：矩阵元素取自域（如 $\mathbb{R}, \mathbb{Q}, \mathbb{F}_p$）。
- `ElementaryRowOp`：三种初等行变换——交换、数乘、倍加。
- `mulVec`：矩阵与向量的乘法，对应线性方程组 $Ax = b$。
- `augment`：增广矩阵的构造。

## 练习

1. 用高斯消元法求解方程组
   $$\begin{cases} x + 2y + z = 4 \\ 2x + y - z = 3 \\ x - y + 2z = 1 \end{cases}$$
2. 证明：初等行变换不改变矩阵的行空间（row space），从而不改变矩阵的秩。
3. 在 Lean4 中验证：一个 $3 \times 3$ 上三角矩阵的秩等于其对角线非零元的个数。
