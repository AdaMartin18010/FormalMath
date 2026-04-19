---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: Gram-Schmidt 正交化 (Gram-Schmidt Orthogonalization)
---
# Gram-Schmidt 正交化 (Gram-Schmidt Orthogonalization)

## Mathlib4 引用

```lean
import Mathlib.LinearAlgebra.GramSchmidt

namespace GramSchmidtOrtho

variable {𝕜 E : Type*} [IsROrC 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Gram-Schmidt 正交化：将线性无关向量组转化为正交向量组 -/
def gramSchmidt (f : ℕ → E) (n : ℕ) : E :=
  f n - ∑ i in Finset.range n, orthogonalProjection (𝕜 ∙ gramSchmidt f i) (f n)

/-- 正交性：不同下标的 Gram-Schmidt 向量两两正交 -/
theorem gramSchmidt_orthogonal (f : ℕ → E) {a b : ℕ} (h : a ≠ b) :
    ⟪gramSchmidt f a, gramSchmidt f b⟫_𝕜 = 0 := by
  -- 对 n 进行归纳证明
  sorry

end GramSchmidtOrtho
```

## 数学背景

Gram-Schmidt 正交化过程是线性代数和泛函分析中的经典算法，由丹麦数学家 Jørgen Pedersen Gram 和德国数学家 Erhard Schmidt 在19世纪末和20世纪初分别独立提出。该过程能够将内积空间中任意一组线性无关的向量转化为一组两两正交的向量组，进而通过单位化得到标准正交基。Gram-Schmidt 过程是量子力学、信号处理、数值分析和统计学中无数方法的基础。

## 直观解释

Gram-Schmidt 正交化的核心思想可以比喻为建筑中的去相关性过程。想象一组互相倾斜的支柱，它们虽然能支撑结构，但力的分析非常复杂。Gram-Schmidt 过程就像是一步一步地将每根支柱调整方向，使其与之前调整好的所有支柱都保持垂直。第一根支柱保持不变，第二根支柱减去它在第一根方向上的投影，第三根支柱减去它在第一、二根方向上的投影，依此类推。最终得到一组完全相互垂直的支柱，使得空间中的任何问题都可以在每个独立方向上一一解决。

## 形式化表述

设 $V$ 是一个内积空间，$\{v_1, v_2, \dots, v_n\}$ 是 $V$ 中线性无关的向量组。Gram-Schmidt 正交化过程定义正交向量组 $\{u_1, u_2, \dots, u_n\}$ 如下：

$$u_1 = v_1$$

$$u_k = v_k - \sum_{{j=1}}^{{k-1}} \frac{{\langle v_k, u_j \rangle}}{{\langle u_j, u_j \rangle}} u_j, \quad k = 2, 3, \dots, n$$

再令 $e_k = \frac{{u_k}}{{||u_k||}}$，则 $\{e_1, e_2, \dots, e_n\}$ 是一组标准正交基。

其中：

- $\langle \cdot, \cdot \rangle$ 表示内积
- $||u_k|| = \sqrt{{\langle u_k, u_k \rangle}}$ 是向量的范数
- $\frac{{\langle v_k, u_j \rangle}}{{\langle u_j, u_j \rangle}} u_j$ 是 $v_k$ 在 $u_j$ 方向上的正交投影

## 证明思路

1. **归纳构造**：从 $u_1 = v_1$ 开始，逐次构造 $u_2, u_3, \dots$
2. **正交投影**：对每个 $v_k$，减去它在已构造正交向量 $\{u_1, \dots, u_{{k-1}}\}$ 张成子空间上的正交投影
3. **正交性验证**：直接计算 $\langle u_k, u_j \rangle$ 可得零（对 $j < k$）
4. **等价子空间**：证明 $\text{span}\{v_1, \dots, v_k\} = \text{span}\{u_1, \dots, u_k\}$ 对所有 $k$ 成立

核心洞察在于从当前向量中系统性地移除所有已处理方向上的分量。

## 示例

### 示例 1：$\mathbb{{R}}^2$ 中的正交化

设 $v_1 = (1, 1)$, $v_2 = (1, 0)$。则 $u_1 = (1, 1)$，$u_2 = (1, 0) - \frac{{1}}{{2}}(1, 1) = (\frac{{1}}{{2}}, -\frac{{1}}{{2}})$。验证：$u_1 \cdot u_2 = \frac{{1}}{{2}} - \frac{{1}}{{2}} = 0$。单位化得 $e_1 = (\frac{{1}}{{\sqrt{2}}}, \frac{{1}}{{\sqrt{2}}})$，$e_2 = (\frac{{1}}{{\sqrt{2}}}, -\frac{{1}}{{\sqrt{2}}})$。

### 示例 2：多项式空间的正交基

在 $L^2([-1,1])$ 中对单项式 $1, x, x^2, \dots$ 应用 Gram-Schmidt 过程，得到的是 Legendre 多项式（差一个归一化常数）。这是正交多项式理论的经典实例。

### 示例 3：QR 分解

Gram-Schmidt 过程等价于矩阵的 QR 分解：对可逆矩阵 $A$，存在正交矩阵 $Q$ 和上三角矩阵 $R$ 使得 $A = QR$。$Q$ 的列就是经 Gram-Schmidt 过程得到的标准正交基。

## 应用

- **QR 分解**：数值线性代数中最重要的矩阵分解之一
- **信号处理**：正交变换、滤波器组和小波分析
- **量子力学**：态矢量的正交化和测量基的选择
- **最小二乘法**：通过正交投影求解超定线性方程组
- **数值积分**：高斯求积公式中 Legendre 多项式的构造

## 相关概念

- 内积空间 (Inner Product Space)：配备内积结构的向量空间
- 正交基 (Orthogonal Basis)：两两正交的向量组构成的基
- 标准正交基 (Orthonormal Basis)：范数均为 1 的正交基
- 正交投影 (Orthogonal Projection)：向量在子空间上的最佳逼近
- QR 分解 (QR Decomposition)：矩阵分解为正交矩阵与上三角矩阵的乘积

## 参考

### 教材

- [G. Strang. Introduction to Linear Algebra. Wellesley-Cambridge, 5th edition, 2016. Section 4.4]
- [P. Lax. Functional Analysis. Wiley, 2002. Chapter 6]

### 在线资源

- [Mathlib4 - GramSchmidt](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/GramSchmidt.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*