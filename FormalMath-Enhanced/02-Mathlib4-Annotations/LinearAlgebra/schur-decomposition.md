---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: Schur 分解 (Schur Decomposition)
---
# Schur 分解 (Schur Decomposition)

## Mathlib4 引用

```lean
import Mathlib.LinearAlgebra.Matrix.Schur

namespace Matrix

variable {𝕜 : Type*} [IsROrC 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- Schur 分解：任意复方阵可酉相似于上三角矩阵 -/
theorem schur_decomposition (A : Matrix n n 𝕜) :
    ∃ (U : Matrix n n 𝕜) (T : Matrix n n 𝕜),
      U.unitary ∧ T.upperTriangular ∧ A = U * T * Uᴴ := by
  -- 对维数 n 进行归纳，利用特征向量的存在性和酉扩充
  sorry

end Matrix
```

## 数学背景

Schur 分解是线性代数中的经典结果，由德国数学家 Issai Schur 于1909年证明。该定理断言：任意复方阵都可以通过酉相似变换化为上三角矩阵。这一定理是矩阵标准型理论的重要里程碑，为谱分析、矩阵函数计算和数值算法提供了强有力的工具。

## 直观解释

Schur 分解告诉我们：虽然一般的复方阵不一定能对角化，但它总可以近似对角化为一个上三角矩阵。想象一个复杂的线性变换，它可能在某些方向上存在耦合——即变换一个向量时，它会沿着其他方向也产生分量。Schur 分解通过巧妙地选择一个酉坐标系（保持几何结构的旋转/反射），将这些耦合全部压缩到上三角部分。

## 形式化表述

设 $A$ 是一个 $n \times n$ 复方阵，则存在酉矩阵 $U$ 和上三角矩阵 $T$，使得：

$$A = U T U^*$$

其中：

- $U$ 是 $n \times n$ 酉矩阵，满足 $U^* U = U U^* = I$
- $T$ 是 $n \times n$ 上三角矩阵
- $U^*$ 表示 $U$ 的共轭转置
- $T$ 的对角线元素 $t_{ii}$ 就是 $A$ 的特征值（可任意排列）

若 $A$ 是实矩阵且所有特征值都是实数，则 $U$ 可取为正交矩阵。

对于一般实矩阵，存在拟 Schur 分解（实 Schur 形式），其中 $T$ 是拟上三角矩阵（对角块为 $1 \times 1$ 或 $2 \times 2$ 块，后者对应一对共轭复特征值）。

## 证明思路

1. **归纳基础**：$1 \times 1$ 矩阵本身就是上三角的
2. **特征向量**：由代数基本定理，$A$ 至少有一个特征值 $\lambda$ 和对应的单位特征向量 $v$
3. **酉扩充**：将 $v$ 扩充为 $\mathbb{C}^n$ 的标准正交基，构成酉矩阵 $U_1$
4. **分块化**：$U_1^* A U_1 = \begin{pmatrix} \lambda & * \ 0 & A_1 \end{pmatrix}$，其中 $A_1$ 是 $(n-1) \times (n-1)$ 矩阵
5. **归纳步骤**：对 $A_1$ 应用归纳假设，得到其 Schur 分解，然后组合得到 $A$ 的 Schur 分解

核心洞察在于通过特征向量逐步剥离特征值，同时保持变换的酉等价性。

## 示例

### 示例 1：不可对角化矩阵的 Schur 分解

设 $A = \begin{pmatrix} 1 & 1 \ 0 & 1 \end{pmatrix}$。这是 Jordan 块，本身已是上三角矩阵。取 $U = I$，则 $T = A$ 就是 Schur 分解。

### 示例 2：正规矩阵的特殊性

若 $A$ 是正规矩阵（$A^* A = A A^*$），则 Schur 分解中的上三角矩阵 $T$ 实际上是对角矩阵。这说明正规矩阵必可对角化，且特征向量构成标准正交基。

### 示例 3：实 Schur 形式

设 $A = \begin{pmatrix} 0 & 1 \ -1 & 0 \end{pmatrix}$，特征值为 $\pm i$。其拟 Schur 分解为 $A = Q R Q^T$，其中 $Q$ 是正交矩阵，$R = A$ 本身就是 $2 \times 2$ 的拟上三角块。

## 应用

- **数值线性代数**：QR 算法和特征值计算的理论基础
- **矩阵函数**：通过上三角化计算矩阵指数、对数和幂次
- **控制理论**：Riccati 方程和 Lyapunov 方程的数值求解
- **信号处理**：协方差矩阵的特征结构和谱估计
- **量子计算**：量子门的分解和量子电路设计

## 相关概念

- 酉相似 (Unitary Similarity)：通过酉矩阵进行的相似变换
- 上三角矩阵 (Upper Triangular Matrix)：主对角线下方全为零的矩阵
- 正规矩阵 (Normal Matrix)：满足 $A^* A = A A^*$ 的矩阵
- 拟上三角矩阵 (Quasi-Upper Triangular Matrix)：允许 $2 \times 2$ 对角块的实上三角形式
- QR 算法 (QR Algorithm)：基于 Schur 分解计算特征值的迭代算法

## 参考

### 教材

- [G. Golub, C. Van Loan. Matrix Computations. Johns Hopkins, 4th edition, 2013. Chapter 7]
- [R. A. Horn, C. R. Johnson. Matrix Analysis. Cambridge, 2nd edition, 2013. Chapter 2]

### 在线资源

- [Mathlib4 - Matrix Schur](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Schur.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*