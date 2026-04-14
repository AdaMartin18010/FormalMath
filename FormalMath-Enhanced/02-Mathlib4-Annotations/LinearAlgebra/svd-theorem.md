---
msc_primary: 00A99
processed_at: '2026-04-03'
title: 奇异值分解 (Singular Value Decomposition)
---
# 奇异值分解 (Singular Value Decomposition)

## Mathlib4 引用

```lean
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.SVD

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜] {A : Matrix m n 𝕜}

/-- 奇异值分解定理 -/
theorem svd (A : Matrix m n 𝕜) :
    ∃ (U : Matrix m m 𝕜) (S : Matrix m n ℝ) (V : Matrix n n 𝕜),
      U.Unitary ∧ V.Unitary ∧ S = diag (singularValues A) ∧
      A = U * (S.map (RCLike.ofReal 𝕜)) * Vᴴ := by
  -- SVD 的存在性
  sorry

/-- 紧 SVD（仅非零奇异值）-/
theorem compactSVD {r : ℕ} (hr : A.rank = r) :
    ∃ (U : Matrix m (Fin r) 𝕜) (S : Matrix (Fin r) (Fin r) ℝ)
      (V : Matrix n (Fin r) 𝕜),
      U.OrthonormalCols ∧ V.OrthonormalCols ∧ S.PosDef ∧
      A = U * (S.map (RCLike.ofReal 𝕜)) * Vᴴ := by
  sorry

end Matrix
```

## 数学背景

奇异值分解（SVD）是线性代数中最重要和最实用的工具之一，由意大利数学家欧金尼奥·贝尔特拉米（Eugenio Beltrami）和法国数学家卡米尔·若尔当（Camille Jordan）于19世纪70年代独立发现，后由埃尔米特、西尔维斯特和魏尔斯特拉斯等人发展。20世纪中期，随着计算机的发展，SVD 成为数值线性代数的核心算法，在数据科学、图像处理和机器学习中有广泛应用。

## 直观解释

SVD 告诉我们：**任何线性变换都可以分解为旋转-缩放-旋转的组合**。具体来说，任何矩阵 $A$ 可以写成：

$$A = U \Sigma V^*$$

其中 $U$ 和 $V$ 是酉矩阵（正交矩阵的复数推广，表示旋转/反射），$\Sigma$ 是对角矩阵（表示沿坐标轴的缩放）。

想象一张照片（矩阵），SVD 将其分解为：先将坐标轴旋转到"最佳方向"（$V^*$），然后沿坐标轴缩放（$\Sigma$），最后再旋转到目标方向（$U$）。

## 形式化表述

设 $A$ 是 $m \times n$ 复矩阵，则存在分解：

$$A = U \Sigma V^*$$

其中：

- $U$ 是 $m \times m$ 酉矩阵（左奇异向量）
- $\Sigma$ 是 $m \times n$ 对角矩阵，对角线元素 $\sigma_1 \geq \sigma_2 \geq \cdots \geq 0$（奇异值）
- $V$ 是 $n \times n$ 酉矩阵（右奇异向量）

### 几何解释

矩阵 $A$ 将单位球映射为椭球，奇异值是椭球的半轴长度，奇异向量是半轴方向。

## 证明思路

1. **$A^*A$ 的特征值**：证明 $A^*A$ 半正定，特征值非负
2. **奇异值定义**：$\sigma_i = \sqrt{\lambda_i(A^*A)}$
3. **右奇异向量**：$V$ 的列是 $A^*A$ 的特征向量
4. **左奇异向量**：$U$ 的列由 $u_i = \frac{Av_i}{\sigma_i}$ 定义
5. **验证分解**：验证 $A = U\Sigma V^*$

关键点在于 $A^*A$ 的半正定性和谱定理的应用。

## 示例

### 示例 1：2×2 矩阵

$$A = \begin{pmatrix} 3 & 0 \\ 4 & 5 \end{pmatrix}$$

计算 $A^TA = \begin{pmatrix} 25 & 20 \\ 20 & 25 \end{pmatrix}$

特征值：$\lambda_1 = 45$，$\lambda_2 = 5$

奇异值：$\sigma_1 = \sqrt{45} \approx 6.71$，$\sigma_2 = \sqrt{5} \approx 2.24$

### 示例 2：图像压缩

一张 $m \times n$ 的灰度图像存储为矩阵 $A$。

使用秩 $k$ 近似：$A_k = \sum_{i=1}^k \sigma_i u_i v_i^T$

存储量从 $mn$ 减少到 $k(m + n + 1)$。

例如，$1000 \times 1000$ 图像，秩 $k=50$ 近似，压缩比约 10:1，质量损失可控。

### 示例 3：主成分分析 (PCA)

数据中心化后，数据矩阵 $X$ 的 SVD 给出：

$$X = U \Sigma V^T$$

$V$ 的列是主成分方向，$\frac{\sigma_i^2}{\sum \sigma_j^2}$ 是第 $i$ 主成分的方差解释率。

## 应用

- **数据降维**：PCA、t-SNE、潜在语义分析
- **图像压缩**：JPEG、Eigenfaces
- **推荐系统**：矩阵补全、协同过滤
- **信号处理**：降噪、滤波、逆问题
- **机器学习**：正则化、低秩近似

## 相关概念

- 特征值分解 (Eigenvalue Decomposition)：方阵的分解
- 伪逆 (Moore-Penrose Pseudoinverse)：通过 SVD 计算
- 低秩近似 (Low-Rank Approximation)：截断 SVD
- 谱范数 (Spectral Norm)：最大奇异值
- 条件数 (Condition Number)：最大与最小奇异值之比

## 参考

### 教材

- [Golub & Van Loan. Matrix Computations. Johns Hopkins, 4th edition, 2013. Chapter 2]
- [Trefethen & Bau. Numerical Linear Algebra. SIAM, 1997. Lecture 4-5]

### 历史文献

- [Beltrami. Sulle funzioni bilineari. 1873]
- [Jordan. Mémoire sur les formes bilinéaires. 1874]

### 在线资源

- [Mathlib4 文档 - SVD][https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/SVD.html](需更新)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
