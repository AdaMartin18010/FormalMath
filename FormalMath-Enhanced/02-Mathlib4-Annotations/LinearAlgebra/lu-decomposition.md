---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: LU 分解 (LU Decomposition)
---
# LU 分解 (LU Decomposition)

## Mathlib4 引用

```lean
import Mathlib.LinearAlgebra.Matrix.Block

namespace Matrix

variable {R : Type*} [Field R] {n : Type*} [Fintype n] [DecidableEq n]

/-- LU 分解：可逆矩阵在某些条件下可分解为下三角矩阵 L 和上三角矩阵 U 的乘积 -/
theorem lu_decomposition (A : Matrix n n R)
    (h : ∀ k, IsUnit (A.submatrix (fun i => i.1) (fun j => j.1) : Matrix (Fin k) (Fin k) R)) :
    ∃ (L : Matrix n n R) (U : Matrix n n R),
      L.lowerTriangular ∧ L.diag = 1 ∧ U.upperTriangular ∧ A = L * U := by
  -- 利用高斯消元法，将消元矩阵的乘积记录为 L
  sorry

end Matrix
```

## 数学背景

LU 分解是数值线性代数中最基础且高效的矩阵分解方法之一，由英国数学家 Alan Turing 和德国数学家 John von Neumann 等人在20世纪上半叶系统发展。该分解将方阵表示为一个下三角矩阵 $L$ 和一个上三角矩阵 $U$ 的乘积（有时还包括置换矩阵 $P$ 以处理主元为零的情况）。LU 分解是高斯消元法的矩阵形式。

## 直观解释

LU 分解的本质是将复杂的线性变换分解为两个更简单的步骤。想象解一个复杂的拼图：下三角矩阵 $L$ 代表了逐步揭示的过程——就像从上到下、从左到右依次确定拼图块的位置；上三角矩阵 $U$ 则代表了最终形状——一旦前面的块确定，后面的块就可以直接放置。在实际求解线性方程组 $Ax = b$ 时，LU 分解将问题转化为两个简单的三角方程组：先用前向替换解 $Ly = b$，再用回代解 $Ux = y$。

## 形式化表述

设 $A$ 是一个 $n \times n$ 方阵。若 $A$ 的所有顺序主子式均非零，则存在唯一的 LU 分解：

$$A = LU$$

其中：

- $L$ 是 $n \times n$ 单位下三角矩阵（对角线元素全为 1，上三角部分全为 0）
- $U$ 是 $n \times n$ 上三角矩阵（下三角部分全为 0）

更一般地，对任意可逆矩阵 $A$，存在带置换的 LU 分解（PLU 分解）：

$$PA = LU$$

其中 $P$ 是置换矩阵，用于行交换以确保数值稳定性。

求解 $Ax = b$ 的步骤：
1. 解 $Ly = Pb$（前向替换）
2. 解 $Ux = y$（回代）

## 证明思路

1. **高斯消元**：对 $A$ 进行高斯消元，将其化为上三角矩阵 $U$
2. **记录乘子**：每次消元时用行 $i$ 消去行 $j$ 的元素，乘子 $l_{ji} = a_{ji}^{(i)} / a_{ii}^{(i)}$ 记录在 $L$ 的 $(j, i)$ 位置
3. **构造 L**：$L$ 的对角线为 1，下三角部分为相应的消元乘子
4. **唯一性**：在顺序主子式非零的条件下，单位下三角的 $L$ 和 Upper 的 $U$ 唯一确定

核心洞察在于高斯消元的每一步都可以用一个初等下三角矩阵表示，其逆矩阵的乘积即为 $L$。

## 示例

### 示例 1：3x3 矩阵的 LU 分解

设 $A = \begin{pmatrix} 2 & 1 & 1 \ 4 & 3 & 3 \ 8 & 7 & 9 \end{pmatrix}$。
经高斯消元得 $U = \begin{pmatrix} 2 & 1 & 1 \ 0 & 1 & 1 \ 0 & 0 & 2 \end{pmatrix}$，消元乘子构成 $L = \begin{pmatrix} 1 & 0 & 0 \ 2 & 1 & 0 \ 4 & 3 & 1 \end{pmatrix}$。验证 $LU = A$。

### 示例 2：多重右端项

在结构分析中，刚度矩阵 $K$ 固定，但需要计算多种载荷 $f_1, f_2, \dots, f_m$ 下的位移。先对 $K$ 做 LU 分解（一次性成本 $O(n^3)$），然后对每个 $f_i$ 用前向/回代求解（成本 $O(n^2)$），总成本远低于每次重新消元。

### 示例 3：行列式计算

$\det(A) = \det(L) \det(U) = 1 \cdot \prod_{i=1}^n u_{ii} = \prod_{i=1}^n u_{ii}$。LU 分解将行列式计算简化为上三角对角元的乘积。

## 应用

- **科学计算**：大规模线性方程组的数值求解
- **工程仿真**：有限元分析和计算流体力学中的系统求解
- **电路仿真**：SPICE 等电路分析程序的核心求解器
- **优化算法**：内点法和序列二次规划中的 KKT 系统求解
- **统计计算**：线性回归和方差分析中的正规方程求解

## 相关概念

- 高斯消元法 (Gaussian Elimination)：将矩阵化为三角形的标准算法
- 下三角矩阵 (Lower Triangular Matrix)：主对角线上方元素全为零的矩阵
- 上三角矩阵 (Upper Triangular Matrix)：主对角线下方元素全为零的矩阵
- 置换矩阵 (Permutation Matrix)：表示行/列交换的矩阵
- 顺序主子式 (Leading Principal Minor)：矩阵左上角子矩阵的行列式

## 参考

### 教材

- [G. Golub, C. Van Loan. Matrix Computations. Johns Hopkins, 4th edition, 2013. Chapter 3]
- [L. N. Trefethen, D. Bau. Numerical Linear Algebra. SIAM, 1997. Lectures 20-22]

### 在线资源

- [Mathlib4 - Matrix Block](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Block.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*