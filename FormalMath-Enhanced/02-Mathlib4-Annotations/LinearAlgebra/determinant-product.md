---
msc_primary: 00A99
processed_at: '2026-04-15'
title: 行列式乘积公式 (Determinant Product Formula)
---
# 行列式乘积公式 (Determinant Product Formula)

## Mathlib4 引用

```lean
import Mathlib.LinearAlgebra.Matrix.Determinant

namespace Matrix

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

/-- 行列式乘积公式：det(AB) = det(A) det(B) -/
theorem det_mul (A B : Matrix n n R) :
    det (A * B) = det A * det B := by
  -- 利用行列式的多线性和交错性，或 Laplace 展开证明
  sorry

end Matrix
```

## 数学背景

行列式乘积公式是线性代数中的核心结果之一，它建立了矩阵乘法与行列式之间的基本联系：两个方阵乘积的行列式等于它们各自行列式的乘积。这一定理不仅在理论上深刻揭示了行列式作为群同态的性质（从一般线性群到乘法群），也是计算高阶行列式、研究特征多项式和矩阵相似不变量的基本工具。

## 直观解释

行列式乘积公式有一个非常直观的几何解释。行列式表示线性变换对体积的缩放比例。如果把矩阵 $A$ 看作是对空间的一次线性变换，矩阵 $B$ 看作是对同空间的另一次线性变换，那么先做 $B$ 再做 $A$（即 $AB$）的复合变换，对体积的总缩放比例显然应该等于两次变换各自缩放比例的乘积。就像先按 2 倍比例放大，再按 3 倍比例放大，总体效果就是 6 倍放大。

## 形式化表述

设 $A$ 和 $B$ 是域 $\mathbb{F}$（或交换环 $R$）上的 $n \times n$ 方阵，则：

$$\det(AB) = \det(A) \det(B)$$

推论：

1. $\det(A^k) = (\det A)^k$（对任意非负整数 $k$）
2. 若 $A$ 可逆，则 $\det(A^{-1}) = (\det A)^{-1}$
3. 若 $A$ 和 $B$ 相似，则 $\det(A) = \det(B)$

其中：

- $\det(A)$ 表示方阵 $A$ 的行列式
- $A, B \in \mathbb{F}^{n \times n}$（或 $R^{n \times n}$）
- 该公式说明行列式映射 $\det: GL_n(\mathbb{F}) \to \mathbb{F}^\times$ 是一个群同态

## 证明思路

1. **Binet-Cauchy 公式**：将 $\det(AB)$ 展开为多重线性和交错形式
2. **初等矩阵分解**：利用任何矩阵都可以分解为初等矩阵的乘积，而初等矩阵的行列式容易直接验证
3. **归纳法**：对矩阵维数进行归纳，利用分块矩阵或 Laplace 展开
4. **Leibniz 公式**：直接从行列式的置换定义出发计算 $\det(AB)$

核心洞察在于行列式是矩阵群到乘法群的同态映射。

## 示例

### 示例 1：2x2 矩阵验证

设 $A = \begin{pmatrix} 1 & 2 \ 3 & 4 \end{pmatrix}$, $B = \begin{pmatrix} 0 & 1 \ 2 & 3 \end{pmatrix}$。
$\det(A) = -2$, $\det(B) = -2$, $\det(A)\det(B) = 4$。
$AB = \begin{pmatrix} 4 & 7 \ 8 & 15 \end{pmatrix}$, $\det(AB) = 60 - 56 = 4$。验证成立。

### 示例 2：可逆矩阵的逆

设 $A$ 可逆且 $\det(A) = 5$。由 $AA^{-1} = I$ 得 $\det(A)\det(A^{-1}) = \det(I) = 1$，因此 $\det(A^{-1}) = 1/5$。

### 示例 3：正交矩阵

正交矩阵 $Q$ 满足 $Q^T Q = I$，因此 $\det(Q)^2 = 1$，即 $\det(Q) = \pm 1$。这对应于正交变换保持体积（允许反射）的几何事实。

## 应用

- **特征多项式**：$\det(AB - \lambda I)$ 与 $\det(A)\det(B - \lambda A^{-1})$ 的关系
- **几何变换**：复合线性变换的体积缩放因子的计算
- **微分方程**：Liouville 公式中基本解矩阵行列式的演化
- **代数拓扑**：映射度（mapping degree）的计算和映射的复合
- **编码理论**：某些线性码的校验矩阵行列式分析

## 相关概念

- 行列式 (Determinant)：方阵的反对称多重线性形式
- 初等矩阵 (Elementary Matrix)：对应行/列初等变换的矩阵
- 一般线性群 (General Linear Group)：可逆 $n \times n$ 矩阵构成的群 $GL_n$
- 特征多项式 (Characteristic Polynomial)：$p_A(\lambda) = \det(A - \lambda I)$
- Binet-Cauchy 公式：行列式乘积公式的更一般形式

## 参考

### 教材

- [S. Axler. Linear Algebra Done Right. Springer, 3rd edition, 2015. Section 10D]
- [G. Strang. Introduction to Linear Algebra. Wellesley-Cambridge, 5th edition, 2016. Section 5.2]

### 在线资源

- [Mathlib4 - Matrix Determinant](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Determinant.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*