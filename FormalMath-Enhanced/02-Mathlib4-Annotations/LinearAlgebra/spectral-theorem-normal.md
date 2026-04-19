---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: 正规算子谱定理 (Spectral Theorem for Normal Operators)
---
# 正规算子谱定理 (Spectral Theorem for Normal Operators)

## Mathlib4 引用

```lean
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.SpectralTheorem

namespace LinearMap

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V)

/-- 正规算子的谱定理 -/
theorem spectralTheoremNormal (hT : T.IsNormal) :
    ∃ b : OrthonormalBasis (Fin (finrank ℂ V)) ℂ V,
      ∀ i, ∃ α : ℂ, T (b i) = α • (b i) := by
  -- 正规算子可对角化，且存在规范正交特征基
  sorry

/-- 厄米特算子的谱定理（特征值实数） -/
theorem spectralTheoremHermitian (hT : T.IsHermitian) :
    ∃ b : OrthonormalBasis (Fin (finrank ℂ V)) ℂ V,
      ∀ i, ∃ α : ℝ, T (b i) = α • (b i) := by
  -- 厄米特算子有实特征值和正交特征基
  sorry

/-- 酉算子的谱定理（特征值模为 1） -/
theorem spectralTheoremUnitary (hT : T.IsUnitary) :
    ∃ b : OrthonormalBasis (Fin (finrank ℂ V)) ℂ V,
      ∀ i, ∃ α : ℂ, ‖α‖ = 1 ∧ T (b i) = α • (b i) := by
  sorry

end LinearMap
```

## 数学背景

谱定理是线性代数和分析的巅峰定理之一，描述了正规算子（包括厄米特算子和酉算子）的结构。该定理的历史可追溯至柯西、埃尔米特和魏尔斯特拉斯的工作，20世纪初由希尔伯特和冯·诺伊曼在泛函分析框架下完善。谱定理连接了线性代数、泛函分析、量子力学和调和分析，是现代数学物理的基石。

## 直观解释

谱定理告诉我们：**正规算子（与伴随算子交换的算子）可以通过选择适当的坐标系（特征向量基）对角化**。想象一个线性变换像一个"拉伸-旋转"操作，谱定理说我们可以找到一组互相垂直的坐标轴，使得变换只是沿着这些轴的简单缩放。

对于厄米特算子（自伴算子），所有缩放因子（特征值）都是实数；对于酉算子，所有缩放因子的模都是 1（纯旋转）。

## 形式化表述

设 $V$ 是有限维复内积空间，$T: V \to V$ 是正规算子（即 $T^*T = TT^*$），则：

- 存在 $V$ 的规范正交基由 $T$ 的特征向量组成
- $T$ 在此基下表示为对角矩阵
- 特征值是 $T$ 的谱（特征多项式的根）

### 特殊情形

**厄米特算子**（$T = T^*$）：所有特征值为实数

**酉算子**（$T^*T = I$）：所有特征值满足 $|\lambda| = 1$

**正定算子**：所有特征值为正实数

## 证明思路

### 有限维证明（归纳法）：

1. **特征值存在性**：复数域上特征多项式必有根
2. **不变子空间**：特征空间是 $T$ 和 $T^*$ 的不变子空间
3. **正交补约化**：$T$ 限制在正交补上是正规算子
4. **归纳假设**：对正交补应用归纳假设
5. **基合并**：特征基合并为整个空间的规范正交基

关键在于正规性保证特征空间与正交补的约化相容。

## 示例

### 示例 1：实对称矩阵

$$A = \begin{pmatrix} 2 & 1 \\ 1 & 2 \end{pmatrix}$$

特征值：$\det(A - \lambda I) = (2-\lambda)^2 - 1 = 0$，得 $\lambda_1 = 3, \lambda_2 = 1$

特征向量：$v_1 = (1, 1)^T / \sqrt{2}$，$v_2 = (1, -1)^T / \sqrt{2}$

正交对角化：$A = QDQ^T$，其中 $Q = \frac{1}{\sqrt{2}}\begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}$，$D = \begin{pmatrix} 3 & 0 \\ 0 & 1 \end{pmatrix}$

### 示例 2：量子力学中的可观测量

位置算符 $X$ 和动量算符 $P$ 满足 $[X, P] = i\hbar I$（不对易，故不能同时对角化）。

哈密顿算符 $H = \frac{P^2}{2m} + V(X)$（厄米特）可对角化，特征值对应能量本征值。

### 示例 3：主成分分析 (PCA)

数据协方差矩阵 $C = \frac{1}{n} X^TX$（实对称）。

谱定理保证 $C = VDV^T$，主成分是特征向量，方差解释率是特征值。

## 应用

- **量子力学**：可观测量对应厄米特算子，测量结果是特征值
- **信号处理**：傅里叶变换是酉算子的对角化
- **数据科学**：PCA、谱聚类、图神经网络
- **偏微分方程**：分离变量法和本征函数展开
- **数值分析**：迭代法的收敛性分析

## 相关概念

- 正规算子 (Normal Operator)：$T^*T = TT^*$
- 厄米特算子 (Hermitian Operator)：$T = T^*$
- 酉算子 (Unitary Operator)：$T^*T = TT^* = I$
- 特征值与特征向量 (Eigenvalue and Eigenvector)
- 函数演算 (Functional Calculus)：算子的函数

## 参考

### 教材

- [Axler. Linear Algebra Done Right. Springer, 3rd edition, 2015. Chapter 7]
- [Lax. Functional Analysis. Wiley, 2002. Chapter 31]

### 历史文献

- [Hilbert. Grundzüge einer allgemeinen Theorie der linearen Integralgleichungen. 1912]
- [von Neumann. Mathematische Grundlagen der Quantenmechanik. 1932]

### 在线资源

- [Mathlib4 文档 - SpectralTheorem](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/SpectralTheorem.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*
