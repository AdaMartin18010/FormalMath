---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: Stokes 定理 (Stokes' Theorem)
---
# Stokes 定理 (Stokes' Theorem)

## Mathlib4 引用

```lean
import Mathlib.Geometry.Manifold.IntegralCurve

namespace StokesTheorem

-- 注：Mathlib4 中一般 Stokes 定理（微分形式在流形边界上的积分）
-- 目前尚未完整形式化。以下给出标准的微分形式表述框架。

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [SmoothManifoldWithCorners (𝓡 n) M] [Orientable M] [Fact (dim M = n)]
  {ω : Ω^{n-1} M} -- (n-1)-形式

/-- Stokes 定理：dω 在 M 上的积分等于 ω 在 ∂M 上的积分 -/
theorem stokes_theorem (hcomp : HasCompactSupport ω) (hbd : M.HasBoundary) :
    ∫ᵇ x : M, d ω x = ∫ᵇ x : ∂M, pullback (inclusion ∂M) ω x := by
  -- Mathlib4 中一般 Stokes 定理仍在发展中；
  -- 一维情形的 FTC 和散度定理已有形式化。
  sorry

end StokesTheorem
```

## 数学背景

Stokes 定理是微分几何与分析学的巅峰成果之一，由高维推广的众多数学家（包括 George Stokes、William Thomson 等人）在19世纪发展完善。该定理统一了微积分基本定理、Green 定理、Gauss 散度定理和经典 Stokes 定理，断言：一个微分形式的外微分在区域上的积分等于该形式在区域边界上的积分。这一定理不仅是现代物理学（尤其是电磁学与广义相对论）的数学语言，也是代数拓扑中同调理论的几何根源。

## 直观解释

Stokes 定理告诉我们：**一个“场”的“旋转”或“散度”在体积内部的总量，完全由其在该体积边界上的“流动”决定**。想象一个漩涡水池：如果你想知道整个水池中旋转的总量，不需要测量每一点，只需要沿着池壁统计水流进出的净环量即可。在更高维度中，$d\omega$ 描述的是形式 $\omega$ 的“局部变化”，而边界积分则捕捉了这些变化的“全局平衡”。

## 形式化表述

设 $M$ 为 $n$ 维定向带边光滑流形，$\omega$ 为 $M$ 上的 $C^1$ 类 $(n-1)$-形式，则：

$$\int_M d\omega = \int_{\partial M} \omega$$

其中：

- $d\omega$ 为 $\omega$ 的**外微分**（$n$-形式）
- $\partial M$ 为 $M$ 的边界，带有诱导定向
- 右侧的 $\omega$ 实际指 $\iota^*\omega$，即边界嵌入映射的拉回

**特例**：
- $n=1$：微积分基本定理
- $n=2, \omega = P dx + Q dy$：Green 定理
- $n=3, \omega = \mathbf{F} \cdot d\mathbf{S}$：Gauss 散度定理
- $n=3, \omega = \mathbf{F} \cdot d\mathbf{r}$：经典 Stokes 定理

## 证明思路

1. **局部坐标化**：利用单位分解将问题约化为坐标卡中的紧支形式
2. **标准单形情形**：在 $\mathbb{R}^n$ 的标准单形上直接计算外微分的积分
3. **Fubini 与 Newton-Leibniz**：对某一坐标重复应用微积分基本定理，内部项相消，仅剩边界贡献
4. **粘合**：由单位分解的线性性，各坐标卡的结果相加即得全局公式

核心在于外微分的定义恰好使得内部“全微分”项相互抵消，只留下边界项。

## 示例

### 示例 1：Green 定理

设 $D \subseteq \mathbb{R}^2$ 为有界区域，$\omega = P dx + Q dy$，则：

$$d\omega = \left(\frac{\partial Q}{\partial x} - \frac{\partial P}{\partial y}\right) dx \wedge dy$$

Stokes 定理给出：

$$\iint_D \left(\frac{\partial Q}{\partial x} - \frac{\partial P}{\partial y}\right) dx dy = \oint_{\partial D} P dx + Q dy$$

### 示例 2：经典 Stokes 定理

设 $S \subseteq \mathbb{R}^3$ 为有向曲面，$\mathbf{F} = (P, Q, R)$，则：

$$\iint_S (\nabla \times \mathbf{F}) \cdot d\mathbf{S} = \oint_{\partial S} \mathbf{F} \cdot d\mathbf{r}$$

这是电磁学中 Faraday 电磁感应定律的数学表述。

### 示例 3：Gauss 散度定理

设 $V \subseteq \mathbb{R}^3$ 为有界体积，$\mathbf{F}$ 为向量场，则：

$$\iiint_V \nabla \cdot \mathbf{F} \, dV = \iint_{\partial V} \mathbf{F} \cdot d\mathbf{S}$$

在流体力学中，这表示体积内流体源汇的总和等于通过边界的净流量。

## 应用

- **电磁学**：Maxwell 方程组的积分形式与微分形式的统一
- **广义相对论**：Stokes 定理在弯曲时空中的推广用于能量-动量守恒
- **流体力学**：涡量、环量与 Bernoulli 原理的数学基础
- **代数拓扑**：de Rham 上同调与奇异上同调的对偶性
- **规范场论**：Chern-Simons 理论与拓扑量子场论

## 相关概念

- 微分形式 (Differential Form)：流形上可积分的反对称张量场
- 外微分 (Exterior Derivative)：微分形式上的反对称导数算子 $d$
- 流形边界 (Manifold Boundary)：带边流形的拓扑边界
- 诱导定向 (Induced Orientation)：边界上由内部定向导出的定向
- de Rham 上同调 (de Rham Cohomology)：用闭形式与恰当形式研究拓扑不变量

## 参考

### 教材

- [Spivak. Calculus on Manifolds. Benjamin, 1965. Chapter 5]
- [Lee. Introduction to Smooth Manifolds. Springer, 2nd edition, 2012. Chapter 16]

### 在线资源

- [Mathlib4 文档 - Manifold][https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold.html]
- **注意**：Mathlib4 中一般 Stokes 定理（高维微分形式版本）目前仍在发展中；一维 FTC 和散度定理已有形式化。

---

*最后更新：2026-04-15 | 版本：v1.0.0*
