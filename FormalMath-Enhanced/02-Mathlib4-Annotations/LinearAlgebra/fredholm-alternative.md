---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: Fredholm 择一性 (Fredholm Alternative)
---
# Fredholm 择一性 (Fredholm Alternative)

## Mathlib4 引用

```lean
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace LinearMap

variable {𝕜 E F : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [FiniteDimensional 𝕜 F]

/-- Fredholm 择一性：对有限维空间上的线性映射 T，
    方程 Tx = y 有解当且仅当 y 与 T 的伴随核正交 -/
theorem fredholm_alternative {T : E →ₗ[𝕜] F} {y : F} :
    (∃ x : E, T x = y) ↔ (∀ z : F, (adjoint T) z = 0 → ⟪z, y⟫_𝕜 = 0) := by
  -- 利用值域与核的正交补关系证明
  sorry

end LinearMap
```

## 数学背景

Fredholm 择一性是泛函分析和线性代数中的基本定理，由瑞典数学家 Erik Ivar Fredholm 在研究积分方程时于1900年左右建立。该定理在有限维情形下表述为：对于线性映射 $T: E \to F$，方程 $Tx = y$ 要么有解，要么存在 $z \in F^*$ 使得 $T^* z = 0$ 但 $\langle z, y \rangle \neq 0$（两种情况恰好居其一）。

## 直观解释

Fredholm 择一性可以形象地理解为：如果一个线性系统 $Tx = y$ 没有解，那么一定是 $y$ 中包含了某些 $T$ 的盲向——即那些 $T$ 完全无法看到或生成的方向。定理告诉我们，只要将 $y$ 中与这些盲向相关的分量去除（即 $y$ 与 $T$ 的伴随核正交），解就必然存在。这种非此即彼的二元性是线性问题的核心特征之一。

## 形式化表述

设 $T: E \to F$ 是有限维内积空间之间的线性映射，$T^*: F \to E$ 是其伴随映射。则以下两个命题有且仅有一个成立：

1. 对给定的 $y \in F$，方程 $Tx = y$ 有解 $x \in E$
2. 存在 $z \in F$ 满足 $T^* z = 0$ 但 $\langle z, y \rangle \neq 0$

等价表述：$Tx = y$ 有解当且仅当 $y \perp \ker(T^*)$。

在矩阵形式下，设 $A \in \mathbb{R}^{m \times n}$，则：

$$Ax = b \text{ 有解 } \iff b \perp \ker(A^T)$$

其中：

- $\ker(T^*) = \{z \in F : T^* z = 0\}$ 是伴随映射的核空间
- $\perp$ 表示在内积意义下的正交

## 证明思路

1. **正交补分解**：在有限维内积空间中，$F = \text{Im}(T) \oplus \ker(T^*)$
2. **必要性**：若 $Tx = y$，则对任意 $z \in \ker(T^*)$ 有 $\langle z, y \rangle = \langle z, Tx \rangle = \langle T^* z, x \rangle = 0$
3. **充分性**：若 $y \perp \ker(T^*)$，则 $y \in \ker(T^*)^\perp = \text{Im}(T)$，故存在 $x$ 使 $Tx = y$
4. **互斥性**：若两者同时成立会导致 $\langle z, y \rangle = 0$ 的矛盾

核心洞察在于值域与伴随核构成空间的正交直和分解。

## 示例

### 示例 1：超定方程组

设 $A = \begin{pmatrix} 1 & 1 \ 1 & -1 \ 2 & 0 \end{pmatrix}$, $b = \begin{pmatrix} 3 \ 1 \ 4 \end{pmatrix}$。$A^T$ 的核由 $(1, 1, -1)^T$ 张成。验证 $b \cdot (1, 1, -1) = 0$，故 $Ax = b$ 有解（实际上 $x = (2, 1)^T$）。

### 示例 2：微分方程中的 Green 函数

在边值问题 $Lu = f$ 中，Fredholm 择一性说明解存在的充要条件是 $f$ 与齐次伴随问题 $L^* v = 0$ 的所有解正交。这是构造 Green 函数和求解非齐次边值问题的基础。

### 示例 3：弹性力学

在结构力学中，如果外力做功在任意刚体位移上为零，则平衡方程有解。这对应于 Fredholm 择一性中 $b \perp \ker(A^T)$ 的物理意义。

## 应用

- **偏微分方程**：椭圆型方程边值问题的可解性理论
- **数值分析**：有限元方法中离散方程组的可解性分析
- **量子力学**：本征值问题和微扰理论中的能级分裂
- **积分方程**：第二类 Fredholm 积分方程的解理论
- **结构力学**：弹性体平衡方程和相容性条件的研究

## 相关概念

- 伴随算子 (Adjoint Operator)：在内积空间中对偶的线性映射
- 核空间 (Kernel/Null Space)：映射为零向量的原像集合
- 值域 (Range/Image)：映射所有像的集合
- 正交补 (Orthogonal Complement)：与给定子空间正交的所有向量
- Green 函数 (Green's Function)：非齐次微分方程的积分核表示

## 参考

### 教材

- [P. Lax. Functional Analysis. Wiley, 2002. Chapter 19]
- [E. Kreyszig. Introductory Functional Analysis with Applications. Wiley, 1978. Chapter 8]

### 在线资源

- [Mathlib4 - LinearMap](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*