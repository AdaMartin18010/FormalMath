---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: QR 分解 (QR Decomposition)
---
# QR 分解 (QR Decomposition)

## Mathlib4 引用

```lean
import Mathlib.LinearAlgebra.Matrix.QR

namespace Matrix

variable {𝕜 : Type*} [IsROrC 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- QR 分解：列满秩矩阵可分解为正交矩阵 Q 和上三角矩阵 R 的乘积 -/
theorem qr_decomposition (A : Matrix m n 𝕜) (hrank : A.rank = n) :
    ∃ (Q : Matrix m m 𝕜) (R : Matrix m n 𝕜),
      Q.orthonormalColumns ∧ R.upperTriangular ∧ A = Q * R := by
  -- 利用 Gram-Schmidt 正交化过程构造 Q 和 R
  sorry

end Matrix
```

## 数学背景

QR 分解是数值线性代数中最重要、应用最广泛的矩阵分解之一。它将一个列满秩矩阵分解为一个正交（或酉）矩阵 $Q$ 和一个上三角矩阵 $R$ 的乘积。QR 分解最早由 Schmidt 和 Gram 在研究正交化过程中奠基，后由 Francis 和 Kublanovskaya 在1960年代发展为求解特征值问题的 QR 算法。

## 直观解释

QR 分解可以直观地理解为将一组倾斜的坐标轴转化为标准正交坐标轴的过程。想象一个由矩阵列向量张成的平行多面体，它的体积可能扭曲变形。QR 分解将这个变换分解为两步：第一步 $R$ 是在原有倾斜坐标轴内的伸缩和剪切（上三角矩阵保持了坐标的层次结构），第二步 $Q$ 是一个刚体旋转或反射（正交变换保持长度和角度），将倾斜轴对齐到标准正交轴。

## 形式化表述

设 $A$ 是一个 $m \times n$（$m \geq n$）的列满秩实（或复）矩阵，则存在分解：

$$A = QR$$

其中：

- $Q$ 是 $m \times m$ 正交矩阵（实情形）或酉矩阵（复情形），满足 $Q^T Q = I$（或 $Q^* Q = I$）
- $R$ 是 $m \times n$ 上三角矩阵（当 $m > n$ 时，下半部分为零）

经济型 QR 分解：$A = Q_1 R_1$，其中 $Q_1$ 是 $m \times n$ 列正交矩阵，$R_1$ 是 $n \times n$ 上三角矩阵。

若 $A$ 的列向量为 $a_1, a_2, \dots, a_n$，则 QR 分解等价于对这组向量应用 Gram-Schmidt 正交化：$Q$ 的列是标准正交化后的向量，$R$ 记录了原向量在新基下的坐标。

## 证明思路

1. **Gram-Schmidt 正交化**：对 $A$ 的列向量逐列进行正交化，得到标准正交列向量组 $q_1, \dots, q_n$
2. **构造 Q**：将 $q_1, \dots, q_n$ 扩充为 $\mathbb{R}^m$ 的标准正交基，组成矩阵 $Q$
3. **构造 R**：令 $R_{ij} = \langle q_i, a_j \rangle$（当 $i \leq j$），$R_{ij} = 0$（当 $i > j$）
4. **验证**：直接计算 $(QR)_j = \sum_i R_{ij} q_i = a_j$

数值计算中通常使用 Householder 反射或 Givens 旋转来避免 Gram-Schmidt 的数值不稳定性。

## 示例

### 示例 1：最小二乘问题

求 $\min_x ||Ax - b||_2$。利用 QR 分解 $A = QR$，问题化为 $\min_x ||Rx - Q^T b||_2$。由于 $R$ 是上三角矩阵，可以通过回代法快速求解。

### 示例 2：2x2 矩阵的 QR 分解

设 $A = \begin{pmatrix} 3 & 1 \ 4 & 2 \end{pmatrix}$。通过 Gram-Schmidt 过程：$q_1 = (3/5, 4/5)^T$，$q_2 = (-4/5, 3/5)^T$。
$Q = \begin{pmatrix} 3/5 & -4/5 \ 4/5 & 3/5 \end{pmatrix}$, $R = \begin{pmatrix} 5 & 11/5 \ 0 & 2/5 \end{pmatrix}$。验证 $QR = A$。

### 示例 3：特征值计算

QR 算法通过反复计算 $A_k = Q_k R_k$，然后令 $A_{k+1} = R_k Q_k$，在正交相似变换下收敛到上三角（或拟上三角）矩阵，其对角元即为特征值。这是现代数值软件计算矩阵特征值的标准方法。

## 应用

- **最小二乘法**：超定线性方程组的最优解计算
- **特征值算法**：QR 算法——计算矩阵全部特征值的标准方法
- **信号处理**：自适应滤波、波束形成和子空间方法
- **数值优化**：非线性最小二乘问题（如 Levenberg-Marquardt 算法）
- **机器学习**：主成分分析（PCA）和正交回归

## 相关概念

- 正交矩阵 (Orthogonal Matrix)：列向量构成标准正交基的方阵
- 酉矩阵 (Unitary Matrix)：复数域上的正交矩阵
- 上三角矩阵 (Upper Triangular Matrix)：主对角线下方元素全为零的矩阵
- Gram-Schmidt 正交化 (Gram-Schmidt Process)：构造正交基的标准算法
- Householder 变换 (Householder Reflection)：数值稳定的 QR 分解实现方法

## 参考

### 教材

- [G. Golub, C. Van Loan. Matrix Computations. Johns Hopkins, 4th edition, 2013. Chapter 5]
- [L. N. Trefethen, D. Bau. Numerical Linear Algebra. SIAM, 1997. Lectures 7-10]

### 在线资源

- [Mathlib4 - Matrix QR](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/QR.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*