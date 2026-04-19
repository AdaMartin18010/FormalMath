---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: C*-代数基础
---
# C*-代数基础

## Mathlib4 引用

```lean
import Mathlib.Analysis.CStarAlgebra.Basic

namespace Analysis

/-- C*-代数的定义 -/
theorem c_star_algebra_def
    {A : Type*} [NormedRing A] [StarRing A]
    [NormedAlgebra ℂ A] [StarModule ℂ A] :
    IsCStarAlgebra A ↔ ∀ (x : A),
      ‖star x * x‖ = ‖x‖^2 := by
  -- C*条件：范数与对合的关系
  rfl

/-- Gelfand-Naimark表示定理 -/
theorem gelfand_naimark
    {A : Type*} [CStarAlgebra A] :
    ∃ (H : Type*) [InnerProductSpace ℂ H]
      [CompleteSpace H] (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)),
    IsometricStarAlgHom π ∧
    Injective π := by
  -- 抽象C*-代数可等距嵌入到Hilbert空间算子代数
  sorry

end Analysis
```

## 数学背景

C*-代数理论由Israel Gelfand和Mark Naimark在1943年奠基，是泛函分析中最重要的分支之一。它统一了局部紧空间的拓扑、测度论和量子力学的代数结构。Gelfand-Naimark定理表明，每个C*-代数都可以实现为Hilbert空间上有界算子的闭*-子代数。这一理论为量子力学提供了严格的数学框架，也在非交换几何、动力系统等领域有深刻应用。

## 直观解释

C*-代数是"带范数的*-代数"，满足关键的C*恒等式：$\|x^*x\| = \|x\|^2$。这一条件将代数结构（乘法和对合）与度量结构（范数）紧密联系。想象C*-代数如同一个"量子空间"——经典拓扑空间对应交换C*-代数，而非交换C*-代数则描述"量子几何"。Gelfand-Naimark定理告诉我们：任何这样的"量子空间"都可以具体实现为Hilbert空间上的算子代数。

## 形式化表述

**C*-代数**：Banach代数 $A$ 配备对合运算 $*: A \to A$ 满足：

1. $(x^*)^* = x$，$(xy)^* = y^*x^*$，$(\lambda x)^* = \bar{\lambda} x^*$
2. **C*恒等式**：$\|x^*x\| = \|x\|^2$

**交换C*-代数**（Gelfand表示）：
$$A \cong C_0(X)$$
其中 $X = \text{Spec}(A)$ 是极大理想空间（局部紧Hausdorff空间）。

**Gelfand-Naimark-Segal (GNS) 构造**：每个C*-代数都可以忠实表示为Hilbert空间算子代数。

## 证明思路

1. **态和表示**：定义正线性泛函（态）
2. **GNS构造**：从态构造循环表示
3. **万有表示**：取所有表示的直和
4. **忠实性证明**：证明映射是单射且等距
5. **交换情形**：应用Gelfand变换

## 示例

### 示例 1：紧算子代数

**问题**：描述Hilbert空间上的紧算子C*-代数。

**解答**：

设 $H$ 是Hilbert空间，$\mathcal{K}(H)$ 是紧算子集合。

$\mathcal{K}(H)$ 是 $B(H)$（有界算子代数）的闭理想。

这是非交换C*-代数的基本例子，在指标理论和K-理论中重要。

### 示例 2：连续函数代数

**问题**：描述 $C(X)$ 的C*-结构，其中 $X$ 是紧Hausdorff空间。

**解答**：

对 $f \in C(X)$：

- 乘法：逐点乘法
- 对合：$f^*(x) = \overline{f(x)}$
- 范数：$\|f\| = \sup_{x \in X} |f(x)|$

验证C*条件：$\|f^*f\| = \sup |\bar{f}f| = \sup |f|^2 = \|f\|^2$ ✓

这是交换C*-代数的典型例子。

## 应用

- **量子力学**：可观测量代数（Heisenberg图景）
- **动力系统**：群C*-代数和变换群C*-代数
- **非交换几何**：Connes的量子空间理论
- **指标理论**：Atiyah-Singer指标定理的算子代数证明
- **量子信息**：量子通道和量子态

## 相关概念

- [von Neumann代数](./von-neumann-algebra.md)：C*-代数的强化
- Gelfand表示：交换C*-代数的结构
- [谱定理](./spectral-theorem-operator.md)：正规算子的函数演算
- AF代数：近似有限维C*-代数
- K-理论：C*-代数的不变量

## 参考

### 教材

- Murphy, G.J. C*-Algebras and Operator Theory. Academic Press, 1990.
- Pedersen, G.K. C*-Algebras and Their Automorphism Groups. Academic Press, 1979.

### 论文

- Gelfand, I.M. & Naimark, M.A. On the embedding of normed rings into the ring of operators in Hilbert space. Mat. Sb., 12: 197-213, 1943.
- Segal, I.E. Irreducible representations of operator algebras. Bull. Amer. Math. Soc., 53: 73-88, 1947.

### 在线资源

- [C*-Algebra Wikipedia](https://en.wikipedia.org/wiki/C*-algebra)
- [nLab - C*-Algebra](https://ncatlab.org/nlab/show/C-star-algebra)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
