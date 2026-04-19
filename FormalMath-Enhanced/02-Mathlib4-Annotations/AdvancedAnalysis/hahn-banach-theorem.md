---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: Hahn-Banach 定理 (Hahn-Banach Theorem)
---
# Hahn-Banach 定理 (Hahn-Banach Theorem)

## Mathlib4 引用

```lean
import Mathlib.Analysis.NormedSpace.HahnBanach

namespace Analysis

variable {𝕜 E : Type*} [IsROrC 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Hahn-Banach 定理：赋范空间上的有界线性泛函可保范延拓到全空间 -/
theorem hahn_banach {p : Subspace 𝕜 E} {f : p →L[𝕜] 𝕜}
    (hf : ∃ M, ∀ x : p, ‖f x‖ ≤ M * ‖x‖) :
    ∃ g : E →L[𝕜] 𝕜, (∀ x : p, g x = f x) ∧ (∀ x : E, ‖g x‖ ≤ M * ‖x‖) := by
  -- 利用 Zorn 引理和凸集分离的几何形式证明
  sorry

end Analysis
```

## 数学背景

Hahn-Banach 定理是泛函分析中最重要、影响最深远的定理之一，由德国数学家汉斯·哈恩（Hans Hahn）和波兰数学家斯特凡·巴拿赫（Stefan Banach）在20世纪20年代末独立证明。该定理断言：赋范向量空间子空间上的有界线性泛函可以保范延拓到整个空间上。Hahn-Banach 定理不仅是 Banach 空间对偶理论的基石，也是凸分析、优化理论、偏微分方程和数理经济学中无数存在性证明的核心工具。

## 直观解释

Hahn-Banach 定理提供了一个强大的存在性保证：如果你在一个向量空间的某个子空间上定义了一个有界的线性泛函，那么就一定可以将它无缝地扩展到整个空间，而且不会增加它的大小（范数）。这就像在一个大楼的某一层安装了一个电梯系统，Hahn-Banach 定理保证你可以把这个电梯系统延伸到整栋大楼的每一层，而且电梯的速度和容量保持不变。

## 形式化表述

设 $E$ 是实数域或复数域上的赋范向量空间，$M$ 是 $E$ 的子空间，$f: M \to \mathbb{K}$ 是 $M$ 上的有界线性泛函，则存在 $E$ 上的有界线性泛函 $F: E \to \mathbb{K}$ 满足：

1. 延拓性：$F|_M = f$，即对任意 $x \in M$，$F(x) = f(x)$
2. 保范性：$||F|| = ||f||$，即 $\sup_{||x|| \leq 1} |F(x)| = \sup_{||x|| \leq 1, x \in M} |f(x)|$

等价表述（几何形式）：若 $A$ 和 $B$ 是拓扑向量空间中不相交的非空凸集，且 $A$ 是开集，则存在一个连续线性泛函将它们严格分离。

其中：

- $||F||$ 表示泛函 $F$ 的算子范数
- 该定理对实空间和复空间均成立
- 保范延拓通常不唯一

## 证明思路

1. **实情形**：首先对一维扩张证明延拓存在，利用 $f(x) \leq p(x)$（$p$ 是次线性泛函）控制范数
2. **Zorn 引理**：将所有可能的延拓按包含关系排序，用 Zorn 引理得到极大延拓
3. **极大性论证**：证明极大延拓必须定义在整个空间上，否则可以继续延拓
4. **复情形**：将复泛函分解为实部和虚部，对实部应用实 Hahn-Banach 定理，然后重构复泛函

核心洞察在于次线性泛函为线性延拓提供了足够灵活的上界控制。

## 示例

### 示例 1：L^∞ 对偶

在 L^∞([0,1]) 中，积分泛函 f(g) = \int_0^1 g(x) dx 可以延拓到更大的空间上。Hahn-Banach 定理保证了这种延拓的存在性，虽然具体构造可能非常复杂。

### 示例 2：凸集分离

在 R^2 中，两个不相交的凸集（如两个不相交的开圆盘）总可以被一条直线严格分离。Hahn-Banach 定理将这个几何直觉推广到无穷维空间。

### 示例 3：对偶空间的丰富性

对任意非零 x \in E，存在 E^* 中的泛函 f 使得 f(x) = ||x|| 且 ||f|| = 1。这说明对偶空间 E^* 足够大，可以区分 E 中的所有点。

## 应用

- **泛函分析**：Banach 空间对偶理论的基石
- **凸分析**：凸集分离定理和次梯度理论
- **偏微分方程**：弱解的存在性和变分原理
- **优化理论**：Lagrange 对偶和 KKT 条件的存在性
- **数理经济学**：均衡价格和效用函数的存在性证明

## 相关概念

- 赋范空间 (Normed Space)：配备范数的向量空间
- 有界线性泛函 (Bounded Linear Functional)：连续线性映射到标量域
- 对偶空间 (Dual Space)：所有连续线性泛函构成的空间
- 次线性泛函 (Sublinear Functional)：满足正齐次性和次可加性的函数
- 凸集分离 (Separation of Convex Sets)：Hahn-Banach 的几何形式

## 参考

### 教材

- [W. Rudin. Functional Analysis. McGraw-Hill, 2nd edition, 1991. Chapter 3]
- [H. Brezis. Functional Analysis, Sobolev Spaces and Partial Differential Equations. Springer, 2011. Chapter 1]

### 在线资源

- [Mathlib4 - HahnBanach](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/NormedSpace/HahnBanach.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*