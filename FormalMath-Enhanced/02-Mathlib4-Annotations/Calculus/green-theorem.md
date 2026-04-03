# Green定理 (Green's Theorem)

## Mathlib4 引用

```lean
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Geometry.Manifold.IntegralCurve

namespace GreenTheorem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Green定理：平面曲线积分与二重积分的关系 -/
theorem green_theorem (P Q : ℝ × ℝ → ℝ) (D : Set (ℝ × ℝ))
    [Bounded D] [MeasurableSet D] (hD : IsCompact (closure D))
    (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q)
    (hC : Rectifiable (boundary D)) :
    ∮ (x, y) in boundary D, P x y * dx + Q x y * dy =
    ∬ (x, y) in D, (∂Q/∂x - ∂P/∂y) dx dy := by
  -- 将曲线积分转化为参数形式并应用Stokes定理
  sorry

/-- Green定理的散度形式 -/
theorem green_theorem_divergence (F : ℝ × ℝ → ℝ × ℝ) (D : Set (ℝ × ℝ))
    [Bounded D] [MeasurableSet D] (hF : ContDiff ℝ 1 F) :
    ∮ p in boundary D, inner (F p) (tangent p) ds = ∬ p in D, divergence F p dA := by
  -- 通过旋度形式推导
  sorry

end GreenTheorem
```

## 数学背景

Green定理由英国数学家乔治·格林（George Green）于1828年在其自出版的论文《数学分析在电磁理论中的应用》中提出。这是向量分析最早的定理之一，建立了平面区域上的曲线积分与二重积分之间的联系，是Stokes定理在二维的特例。

## 直观解释

Green定理告诉我们：**平面向量场沿闭曲线的环量等于其旋度在区域内的积分**。想象流体流动：沿着边界一周流动的总量，等于区域内所有小漩涡的总和。这反映了局部性质（旋度）如何决定整体行为（环量）。

## 形式化表述

设 $D \subset \mathbb{R}^2$ 是有界闭区域，边界 $\partial D$ 是分段光滑的简单闭曲线，取正向（逆时针）。设 $P, Q$ 在包含 $D$ 的开集上有连续偏导数，则：

$$\oint_{\partial D} P\,dx + Q\,dy = \iint_D \left(\frac{\partial Q}{\partial x} - \frac{\partial P}{\partial y}\right) dx\,dy$$

**散度形式**：
$$\oint_{\partial D} F \cdot n\,ds = \iint_D \nabla \cdot F\,dA$$

## 证明思路

1. **特殊区域**：先证矩形区域，直接计算
2. **单连通区域**：通过坐标变换归约到矩形
3. **一般区域**：用单位分解和局部坐标卡
4. **方向验证**：确保边界定向与区域定向相容

## 示例

### 示例 1：单位圆盘

计算 $\oint_C x\,dy$，其中 $C$ 是单位圆。

$P = 0, Q = x$，则 $\frac{\partial Q}{\partial x} - \frac{\partial P}{\partial y} = 1$

结果：$\iint_D 1\,dA = \pi$（圆盘面积）

### 示例 2：面积公式

区域 $D$ 的面积：$A = \frac{1}{2}\oint_{\partial D} x\,dy - y\,dx$

## 应用

- **电磁学**：安培定律、法拉第定律的积分形式
- **流体力学**：环量与涡量关系
- **复分析**：Cauchy积分定理的基础
- **计算几何**：多边形面积计算

## 相关概念

- [Stokes定理](../Geometry/stokes-theorem.md)：三维推广
- [散度定理](./divergence-theorem.md)：Green定理的三维形式
- [Cauchy积分定理](../Analysis/cauchy-integral-formula.md)：复分析版本
- [单连通区域](./simply-connected-domain.md)：Green定理适用的区域类型

## 参考

### 教材

- [Marsden & Tromba. Vector Calculus. Freeman, 6th edition, 2011. Chapter 8]
- [Spivak. Calculus on Manifolds. Benjamin, 1965. Chapter 5]

### 历史文献

- [Green. An Essay on the Application of Mathematical Analysis to the Theories of Electricity and Magnetism. 1828]

### 在线资源

- [Mathlib4 文档 - Complex Cauchy Integral](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/CauchyIntegral.html)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
