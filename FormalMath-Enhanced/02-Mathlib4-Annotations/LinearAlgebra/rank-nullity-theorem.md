---
msc_primary: 00A99
processed_at: '2026-04-03'
title: 秩-零化度定理 (Rank-Nullity Theorem)
---
# 秩-零化度定理 (Rank-Nullity Theorem)

## Mathlib4 引用

```lean
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace LinearMap

variable {R : Type*} [DivisionRing R]
variable {V W : Type*} [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] [Module.Finite R V]

/-- 秩-零化度定理 -/
theorem rank_nullity (f : V →ₗ[R] W) :
    finrank R (LinearMap.ker f) + finrank R (LinearMap.range f) = finrank R V := by
  -- 核心定理：零空间与像空间的维度之和等于原空间维度
  exact Eq.symm (finrank_range_add_finrank_ker f)

end LinearMap
```

## 数学背景

秩-零化度定理是线性代数中最基本和优雅的定理之一，描述了线性映射的核空间（零空间）与像空间（值域）维度之间的基本关系。该定理可追溯至19世纪中叶，是向量空间维数理论的自然结果，由格拉斯曼（Hermann Grassmann）等人在发展线性代数基础时建立。它是理解线性方程组解的结构和线性映射性质的钥匙。

## 直观解释

秩-零化度定理告诉我们：**线性变换"压缩"的维度加上"保留"的维度等于原始维度**。想象一个投影变换，一部分信息被"压扁"到零（核空间），另一部分被投影到目标空间（像空间），两者维度之和恒等于原始空间维度。

数学上，若线性映射 $f: V \to W$ 将空间 $V$ 映射到 $W$，则被"消灭"的维度（零化度）与"存活"的维度（秩）之和，恰好等于 $V$ 的总维度。

## 形式化表述

设 $f: V \to W$ 是有限维向量空间之间的线性映射，则：

$$\dim(\ker f) + \dim(\text{im } f) = \dim(V)$$

或用秩和零化度表示：

$$\text{nullity}(f) + \text{rank}(f) = \dim(V)$$

其中：

- 零化度 $\text{nullity}(f) = \dim(\ker f)$ 是核空间的维数
- 秩 $\text{rank}(f) = \dim(\text{im } f)$ 是像空间的维数

## 证明思路

### 构造性证明：

1. **核的基**：取 $\ker f$ 的基 $\{v_1, \ldots, v_k\}$
2. **扩充为 V 的基**：扩充为 $V$ 的基 $\{v_1, \ldots, v_k, w_1, \ldots, w_r\}$
3. **像空间的生成**：证明 $\{f(w_1), \ldots, f(w_r)\}$ 生成 $\text{im } f$
4. **线性无关性**：证明 $\{f(w_1), \ldots, f(w_r)\}$ 线性无关
5. **结论**：$\dim(\text{im } f) = r$，$\dim(\ker f) = k$，$\dim(V) = k + r$

### 短正合序列视角：

$$0 \to \ker f \to V \to \text{im } f \to 0$$

短正合序列的维度可加性直接给出结论。

## 示例

### 示例 1：矩阵表示

设 $A = \begin{pmatrix} 1 & 2 & 3 \\ 2 & 4 & 6 \end{pmatrix}$

- 行简化后：$\begin{pmatrix} 1 & 2 & 3 \\ 0 & 0 & 0 \end{pmatrix}$
- 秩：$\text{rank}(A) = 1$（非零行数）
- 零化度：$\text{nullity}(A) = 3 - 1 = 2$

核空间：$\{(x, y, z) : x + 2y + 3z = 0\}$，维度为 2（两个自由变量）。

### 示例 2：微分算子

设 $D: P_n \to P_n$ 是微分算子，$P_n$ 是次数不超过 $n$ 的多项式空间。

- $\dim(P_n) = n + 1$
- $\ker D = \text{span}\{1\}$（常数多项式），$\dim(\ker D) = 1$
- $\text{im } D = P_{n-1}$（次数不超过 $n-1$ 的多项式），$\dim(\text{im } D) = n$

验证：$1 + n = n + 1$ ✓

### 示例 3：线性方程组

方程组 $Ax = b$，其中 $A$ 是 $m \times n$ 矩阵。

- 若 $\text{rank}(A) = r$，则解空间维度为 $n - r$
- 齐次方程 $Ax = 0$ 有 $n - r$ 个自由变量
- 若 $r = n$，唯一解（或无解）；若 $r < n$，无穷多解

## 应用

- **线性方程组**：解的存在性和唯一性判定
- **矩阵分析**：秩的计算和估计
- **编码理论**：校验矩阵和生成矩阵的关系
- **控制理论**：能控性和能观性判据
- **同调代数**：正合序列的维度分析

## 相关概念

- [核空间 (Kernel/Nullspace)](./kernel.md)：映射到零的向量集合
- [像空间 (Image/Range)](./image.md)：映射的所有输出
- [维数 (Dimension)](./dimension.md)：向量空间的"大小"
- [同构定理 (Isomorphism Theorems)](./isomorphism-theorems.md)：线性代数基本定理
- [弗雷德霍姆选择 (Fredholm Alternative)](./fredholm-alternative.md)：解的存在性理论

## 参考

### 教材

- [Axler. Linear Algebra Done Right. Springer, 3rd edition, 2015. Section 3.5]
- [Friedberg, Insel, Spence. Linear Algebra. Pearson, 4th edition, 2002. Section 2.1]

### 历史文献

- [Grassmann. Die Lineale Ausdehnungslehre. 1844]

### 在线资源

- [Mathlib4 文档 - FiniteDimensional](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/FiniteDimensional.html)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
