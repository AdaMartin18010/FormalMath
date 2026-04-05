---
msc_primary: 00A99
processed_at: '2026-04-03'
title: 高斯散度定理 (Gauss's Divergence Theorem)
---
# 高斯散度定理 (Gauss's Divergence Theorem)

## Mathlib4 引用

```lean
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Geometry.Manifold.IntegralCurve

namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- 高斯散度定理 -/
theorem divergence_theorem (F : E → E) (V : Set E)
    [Bounded V] [MeasurableSet V] (hV : IsCompact (closure V))
    (hF : ContDiff ℝ 1 F) (hS : MeasurableSet (boundary V)) :
    ∫ x in V, divergence F x = ∫ x in boundary V, inner (F x) (normal x) := by
  -- 应用Stokes定理到(n-1)-形式
  sorry

/-- 三维散度定理的经典形式 -/
theorem divergence_theorem_R3 (F : ℝ³ → ℝ³) (V : Set ℝ³)
    (hF : ContDiff ℝ 1 F) :
    ∭ x in V, (∇ · F) dV = ∯ x in ∂V, F · n dS := by
  -- 直角坐标系下的形式
  sorry

end DivergenceTheorem
```

## 数学背景

高斯散度定理由卡尔·弗里德里希·高斯在1813年提出，也被称为Gauss定理或Ostrogradsky定理（米哈伊尔·奥斯特罗格拉茨基在1826年独立发现）。这是向量分析的基本定理之一，建立了体积积分与曲面积分之间的联系，在物理学中有广泛应用。

## 直观解释

散度定理告诉我们：**向量场穿过闭曲面的通量等于其散度在体积内的积分**。想象流体：通过边界流出的净流量（通量）等于体积内所有源和汇的总和（散度）。源产生流体（正散度），汇吸收流体（负散度）。

## 形式化表述

设 $V \subset \mathbb{R}^3$ 是有界闭区域，边界 $\partial V$ 是分片光滑闭曲面，$n$ 是单位外法向量。设 $F$ 在包含 $V$ 的开集上连续可微，则：

$$\iiint_V \nabla \cdot F\,dV = \iint_{\partial V} F \cdot n\,dS$$

其中散度：$\nabla \cdot F = \frac{\partial F_1}{\partial x} + \frac{\partial F_2}{\partial y} + \frac{\partial F_3}{\partial z}$

## 证明思路

1. **坐标方向分离**：对每个坐标方向分别证明
2. **简单区域**：考虑可以表示为函数图像下方的区域
3. **Fubini定理**：将体积分转化为累次积分
4. **Newton-Leibniz公式**：一维基本定理的应用
5. **区域分解**：一般区域分解为简单区域的并

## 示例

### 示例 1：径向场

设 $F(x) = x$（位置向量场），$V$ 是半径为 $R$ 的球。

$\nabla \cdot F = 3$

体积积分：$3 \cdot \frac{4}{3}\pi R^3 = 4\pi R^3$

曲面积分：$R \cdot 4\pi R^2 = 4\pi R^3$（因为 $F \cdot n = R$）

### 示例 2：重力场

点质量产生的重力场 $F = -\frac{Gm}{r^2}\hat{r}$

在不含原点的区域内 $\nabla \cdot F = 0$（无源场）

## 应用

- **电磁学**：Maxwell方程组的积分形式
- **流体力学**：连续性方程、质量守恒
- **热传导**：能量守恒、热扩散方程
- **引力理论**：高斯定律

## 相关概念

- [Stokes定理](../Geometry/stokes-theorem.md)：旋度版本的类似定理
- [Green定理](./green-theorem.md)：二维版本
- 通量 (Flux)：向量场穿过曲面的量
- 散度 (Divergence)：场的"源"密度

## 参考

### 教材

- [Griffiths. Introduction to Electrodynamics. Cambridge, 4th edition, 2017. Chapter 1]
- [Marsden & Tromba. Vector Calculus. Freeman, 6th edition, 2011. Chapter 8]

### 历史文献

- [Gauss. Theoria attractionis corporum sphaeroidicorum ellipticorum homogeneorum. 1813]

### 在线资源

- [Mathlib4 文档 - Vector Calculus](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/FDeriv/Basic.html)[需更新]

---

*最后更新：2026-04-03 | 版本：v1.0.0*
