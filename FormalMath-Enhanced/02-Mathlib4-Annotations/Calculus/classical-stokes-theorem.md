---
msc_primary: 00A99
processed_at: '2026-04-03'
title: 经典Stokes定理 (Classical Stokes' Theorem)
---
# 经典Stokes定理 (Classical Stokes' Theorem)

## Mathlib4 引用

```lean
import Mathlib.Geometry.Manifold.IntegralCurve
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace ClassicalStokes

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- R³中的经典Stokes定理 -/
theorem classical_stokes_theorem (F : ℝ³ → ℝ³) (S : Set ℝ³)
    [IsSurface S] [Orientable S] (hF : ContDiff ℝ 1 F)
    (hC : Rectifiable (boundary S)) :
    ∬ x in S, curl F x • dS = ∮ x in boundary S, F x • dx := by
  -- 旋度的曲面积分等于边界的环量
  sorry

/-- 旋度定义 -/
def curl (F : ℝ³ → ℝ³) (x : ℝ³) : ℝ³ :=
  (∂F₃/∂y - ∂F₂/∂z, ∂F₁/∂z - ∂F₃/∂x, ∂F₂/∂x - ∂F₁/∂y)

/-- 旋度的坐标无关定义 -/
theorem curl_invariant (F : ℝ³ → ℝ³) (x : ℝ³) :
    curl F x = limit (ε → 0) (1/volume (ball x ε)) ∮ y in sphere x ε, n y × F y ds := by
  -- 用环量密度定义旋度
  sorry

end ClassicalStokes
```

## 数学背景

经典Stokes定理（也称为旋度定理）是向量微积分中的核心结果，描述了向量场旋度通过曲面的通量与场沿曲面边界的环量之间的关系。虽然以George Stokes（1819-1903）命名，但他本人并未明确表述此定理。该定理是微分形式版本的Stokes定理在三维欧氏空间中的特例，在流体力学和电磁学中有直接应用。

## 直观解释

经典Stokes定理告诉我们：**向量场旋度穿过曲面的总"涡量"等于场沿曲面边界的总"环流"**。想象流体流动：如果你在曲面边缘放置一个小桨轮，它的总旋转量（环量）等于曲面内所有小漩涡（旋度）的总和。这揭示了涡旋的"内部"与"边界"之间的深刻联系。

## 形式化表述

设 $S \subset \mathbb{R}^3$ 是分段光滑的有向曲面，边界 $\partial S$ 是分段光滑的闭曲线（方向由右手法则确定）。设 $F: \mathbb{R}^3 \to \mathbb{R}^3$ 是 $C^1$ 向量场，则：

$$\iint_S (\nabla \times F) \cdot dS = \oint_{\partial S} F \cdot dr$$

其中：
- $\nabla \times F = \left(\frac{\partial F_3}{\partial y} - \frac{\partial F_2}{\partial z}, \frac{\partial F_1}{\partial z} - \frac{\partial F_3}{\partial x}, \frac{\partial F_2}{\partial x} - \frac{\partial F_1}{\partial y}\right)$ 是旋度
- $dS = n\,dA$ 是有向面积元

## 证明思路

1. **参数化曲面**：将曲面积分转化为二重积分
2. **Green定理**：在参数域上应用Green定理
3. **链式法则**：验证旋度与Jacobian的关系
4. **边界对应**：参数域边界映射到曲面边界
5. **定向一致性**：验证方向匹配

## 示例

### 示例 1：平面圆盘

设 $S$ 是 $xy$-平面的单位圆盘，$F = (-y, x, 0)$。

$\nabla \times F = (0, 0, 2)$，曲面积分 $= 2 \cdot \pi = 2\pi$。

边界环量：$\oint (-y\,dx + x\,dy) = \int_0^{2\pi} d\theta = 2\pi$。

### 示例 2：保守场

若 $F = \nabla \phi$，则 $\nabla \times F = 0$。

环量为零，验证了保守场的路径无关性。

## 应用

- **电磁学**：法拉第电磁感应定律
- **流体力学**：涡量守恒、Kelvin环量定理
- **刚体力学**：角动量定理
- **微分拓扑**：映射度理论

## 相关概念

- [Stokes定理（一般形式）](../Geometry/stokes-theorem.md)：微分形式版本
- 旋度 (Curl)：向量场的旋转程度
- 环量 (Circulation)：沿闭曲线的线积分
- [Green定理](./green-theorem.md)：二维版本

## 参考

### 教材

- [Marsden & Tromba. Vector Calculus. Freeman, 6th edition, 2011. Chapter 8]
- [Schey. Div, Grad, Curl, and All That. Norton, 4th edition, 2005]

### 在线资源

- [Mathlib4 文档 - Manifold](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/Basic.html)[需更新]

---

*最后更新：2026-04-03 | 版本：v1.0.0*
