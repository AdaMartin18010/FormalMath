---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# Stokes定理 (Stokes' Theorem)

## Mathlib4 引用

```lean
import Mathlib.Geometry.Manifold.IntegralCurve
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

namespace StokesTheorem

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [SmoothManifoldWithCorners (𝓡 n) M] [Orientable M]

/-- Stokes定理：边界积分与微分形式的外微分 -/
theorem stokes {ω : Ωⁿ⁻¹(M)} [CompactSupport ω] :
    ∫ x in M, (d ω) x = ∫ x in ∂M, ω x := by
  -- 局部化到坐标卡
  sorry

/-- 散度定理（Stokes定理的特例）-/
theorem divergence_theorem {F : VectorField M} [CompactSupport F] :
    ∫ x in M, div F x = ∫ x in ∂M, inner (F x) (normal x) := by
  -- 应用于体积形式
  sorry

/-- 经典Stokes定理（R³中）-/
theorem classical_stokes {F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {S : Set (EuclideanSpace ℝ (Fin 3))} [IsSurface S]
    (hF : ContDiff ℝ 1 F) :
    ∫∫ x in S, curl F x • dS = ∮ x in ∂S, F x • dx := by
  -- 旋度的曲面积分等于边界的环量
  sorry

end StokesTheorem
```

## 数学背景

Stokes定理由George Stokes在1854年（作为Smith奖考题）提出，是微分几何和向量分析中的基本结果。它统一了微积分基本定理、格林定理、高斯散度定理和经典Stokes定理。该定理表明，流形上微分形式的外微分的积分等于形式在边界上的积分，建立了整体（积分）与局部（微分）之间的深刻联系。

## 直观解释

Stokes定理告诉我们：**一个"场"的"旋转"或"散度"在区域内的总效果，等于场在边界上的"环量"或"通量"**。

想象流体流动。Stokes定理说，区域内涡旋（旋度）的总和等于流体沿边界流动的总量；或者区域内源汇（散度）的总和等于穿过边界的净流量。这就像说，观察一个区域的内部变化，等价于观察其边界上的累积效果。

## 形式化表述

设 $M$ 是定向 $n$ 维带边流形，$\omega$ 是紧支 $(n-1)$-形式。

**Stokes定理**：
$$\int_M d\omega = \int_{\partial M} \omega$$

其中：
- $d\omega$ 是 $\omega$ 的外微分
- $\partial M$ 是 $M$ 的边界（诱导定向）

**特例**：
- **微积分基本定理**：$n = 1$，$\int_a^b f'(x)dx = f(b) - f(a)$
- **格林定理**：$n = 2$，$\iint_D (\frac{\partial Q}{\partial x} - \frac{\partial P}{\partial y})dxdy = \oint_{\partial D} Pdx + Qdy$
- **散度定理**：$\iiint_V \nabla \cdot F \, dV = \iint_{\partial V} F \cdot dS$

## 证明思路

1. **局部情形**：
   - $M = \mathbb{R}^n_+$（上半空间）
   - 直接计算外微分和积分
   
2. **坐标卡覆盖**：
   - 用单位分解局部化
   - 在每个坐标卡上应用局部结果
   
3. **边界项消去**：
   - 内部边界的积分方向相反
   - 相互抵消，只剩外边界
   
4. **边界定向**：
   - 验证诱导定向的一致性
   - 保证符号正确

核心洞察是外微分的反称性与边界的定向相容性。

## 示例

### 示例 1：单位圆盘

$D = \{(x,y) : x^2 + y^2 \leq 1\}$，$\omega = x dy$。

$d\omega = dx \wedge dy$（面积元）。

$\int_D dx \wedge dy = \pi$（面积）。

$\int_{\partial D} x dy = \int_0^{2\pi} \cos^2 \theta d\theta = \pi$。

### 示例 2：球面

$S^2$ 上的2-形式，$\int_{S^2} d\omega = 0$（无边界的闭流形）。

### 示例 3：经典Stokes

$S$ 是 $z = 0$ 平面的上半单位圆盘，$\partial S$ 是单位圆。

$F = (-y, x, 0)$，$\nabla \times F = (0, 0, 2)$。

曲面积分：$2 \cdot \pi/2 = \pi$。

线积分：$\oint (-y dx + x dy) = \int_0^{\pi} (\sin^2\theta + \cos^2\theta) d\theta = \pi$。

## 应用

- **电磁学**：Maxwell方程组的积分形式
- **流体力学**：涡旋和守恒定律
- **微分拓扑**：de Rham上同调
- **广义相对论**：能量-动量守恒
- **几何测度论**：极小曲面理论

## 相关概念

- [外微分 (Exterior Derivative)](./exterior-derivative.md)：微分形式的外微分
- [微分形式 (Differential Form)](./differential-form.md)：流形上的反对称张量场
- [de Rham上同调 (de Rham Cohomology)](./de-rham-cohomology.md)：拓扑不变量
- [流形 (Manifold)](./manifold.md)：局部像欧氏空间的空间
- [定向 (Orientation)](./orientation.md)：流形的一致性定向

## 参考

### 教材

- [Spivak. Calculus on Manifolds. Benjamin, 1965. Chapter 5]
- [Lee. Introduction to Smooth Manifolds. Springer, 2nd edition, 2012. Chapter 16]

### 历史文献

- [Stokes. Smith's Prize Exam. 1854]

### 在线资源

- [Mathlib4 文档 - Manifold](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/Basic.html)
- [Wikipedia - Stokes' Theorem](https://en.wikipedia.org/wiki/Stokes%27_theorem)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
