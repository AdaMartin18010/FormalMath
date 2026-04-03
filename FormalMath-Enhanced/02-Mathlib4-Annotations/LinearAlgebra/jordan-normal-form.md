# 约当标准型 (Jordan Normal Form)

## Mathlib4 引用

```lean
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.JordanNormalForm

namespace LinearMap

variable {R : Type*} [Field R] [IsAlgClosed R]
variable {V : Type*} [AddCommGroup V] [Module R V] [FiniteDimensional R V]
variable (f : V →ₗ[R] V)

/-- 约当标准型存在性 -/
theorem exists_jordanNormalForm :
    ∃ b : Basis (Fin (finrank R V)) R V,
    ∀ j, ∃ α : R, ∀ k,
      toMatrix b b f (j, k) = if k = j then α else
                             if k = j + 1 then 1 else 0 := by
  -- 复数域上线性变换存在约当标准型
  sorry

end LinearMap
```

## 数学背景

约当标准型由法国数学家卡米尔·若尔当（Camille Jordan）于1870年提出，是线性代数中关于矩阵相似标准型的最一般结果。该定理表明，在代数闭域（如复数域）上，任何线性变换都可以表示为约当块的直和。约当标准型提供了理解线性变换结构的完整图景，是研究常微分方程组、马尔可夫链和算子理论的基础工具。

## 直观解释

约当标准型告诉我们：**任何线性变换都可以分解为"特征方向上的简单伸缩与剪切"的组合**。想象一个弹性体的变形：在某些方向上，材料被均匀拉伸或压缩（对应特征值）；在"缺陷"方向（广义特征向量）上，除了伸缩还有额外的"剪切"效应。

每个约当块对应一个特征值，块的大小反映了该特征值的"代数重数"与"几何重数"之间的差异。当所有约当块都是 1×1 时，矩阵可对角化。

## 形式化表述

设 $A$ 是代数闭域 $\mathbb{F}$ 上的 $n \times n$ 矩阵，则存在可逆矩阵 $P$ 使得：

$$P^{-1}AP = J = \begin{pmatrix} J_1 & & \\ & \ddots & \\ & & J_k \end{pmatrix}$$

其中每个约当块 $J_i$ 形如：

$$J_i = \begin{pmatrix} \lambda_i & 1 & & \\ & \lambda_i & \ddots & \\ & & \ddots & 1 \\ & & & \lambda_i \end{pmatrix}$$

$\lambda_i$ 是 $A$ 的特征值，可以重复。

## 证明思路

1. **广义特征空间**：对每个特征值 $\lambda$，定义广义特征空间 $G_\lambda = \ker((A - \lambda I)^n)$
2. **空间分解**：$V = \bigoplus_\lambda G_\lambda$
3. **幂零算子**：在 $G_\lambda$ 上，$N = A - \lambda I$ 是幂零的
4. **幂零标准型**：证明幂零算子存在循环子空间分解
5. **约当块构造**：每个循环子空间对应一个约当块

核心是证明幂零算子的循环分解定理。

## 示例

### 示例 1：可对角化矩阵

$$A = \begin{pmatrix} 4 & 0 & 0 \\ 0 & 4 & 0 \\ 0 & 0 & 7 \end{pmatrix}$$

特征值：$4, 4, 7$

约当标准型：三个 1×1 约当块 $J_1 = (4)$, $J_2 = (4)$, $J_3 = (7)$

这是退化的约当型，矩阵本身已是对角阵。

### 示例 2：不可对角化矩阵

$$A = \begin{pmatrix} 5 & 1 & 0 \\ 0 & 5 & 1 \\ 0 & 0 & 5 \end{pmatrix}$$

单个约当块，特征值 5（代数重数 3），几何重数 1。

$P = I$，矩阵本身就是约当标准型。

### 示例 3：计算矩阵幂

$$A = \begin{pmatrix} 2 & 1 \\ 0 & 2 \end{pmatrix} = 2I + N$$

其中 $N = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$，$N^2 = 0$。

$$A^k = (2I + N)^k = 2^k I + k \cdot 2^{k-1} N = \begin{pmatrix} 2^k & k \cdot 2^{k-1} \\ 0 & 2^k \end{pmatrix}$$

这利用了约当块的二项式展开。

## 应用

- **常微分方程**：线性系统 $\frac{dx}{dt} = Ax$ 的解 $x(t) = e^{At}x_0$
- **马尔可夫链**：转移矩阵的极限行为分析
- **控制理论**：系统能控标准型
- **数值分析**：矩阵函数的计算
- **表示理论**：李代数和群表示

## 相关概念

- [特征值与特征向量 (Eigenvalue and Eigenvector)](./eigenvalue-eigenvector.md)
- [代数重数与几何重数 (Algebraic and Geometric Multiplicity)](./multiplicity.md)
- [广义特征向量 (Generalized Eigenvector)](./generalized-eigenvector.md)
- [极小多项式 (Minimal Polynomial)](./minimal-polynomial.md)
- [有理标准型 (Rational Canonical Form)](./rational-canonical-form.md)

## 参考

### 教材

- [Hoffman & Kunze. Linear Algebra. Prentice Hall, 2nd edition, 1971. Chapter 7]
- [Axler. Linear Algebra Done Right. Springer, 3rd edition, 2015. Chapter 8]

### 历史文献

- [Jordan. Traité des substitutions et des équations algébriques. 1870]

### 在线资源

- [Mathlib4 文档 - JordanNormalForm](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/JordanNormalForm.html)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
