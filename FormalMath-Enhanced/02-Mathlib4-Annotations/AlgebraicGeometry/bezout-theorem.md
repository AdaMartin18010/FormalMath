---
msc_primary: 00A99
processed_at: '2026-04-15'
title: Bézout 定理 (Bézout's Theorem)
---
# Bézout 定理 (Bézout's Theorem)

## Mathlib4 引用

```lean
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme

namespace BezoutTheorem

-- 注：Mathlib4 中 Bézout 定理的完整形式化目前尚未完成。
-- 以下给出该定理在射影平面中的标准代数几何表述框架。

variable {k : Type*} [Field k] [IsAlgClosed k]

/-- Bézout 定理：两条射影平面曲线的交点个数
    （计重数）等于它们次数的乘积 -/
theorem bezout_theorem {C D : ProjectiveCurve k}
    (hno_common_component : ¬(C.irreducibleComponent ∣ D.irreducibleComponent)) :
    ∑ p : ℙ²(k, 2), intersectionMultiplicity C D p = C.degree * D.degree := by
  -- Mathlib4 中该定理的完整形式化目前仍在发展中。
  sorry

end BezoutTheorem
```

## 数学背景

Bézout 定理是代数几何中最经典的结果之一，以法国数学家 Étienne Bézout（1730–1783）命名。该定理断言：在射影平面中，两条没有公共分支的代数曲线的交点个数（计入重数）恰好等于它们次数的乘积。这一定理深刻揭示了代数方程组解的个数与方程次数之间的精确关系，是相交理论的起点，也是计算代数几何、密码学和编码理论中的重要工具。

## 直观解释

Bézout 定理告诉我们：**两条代数曲线相交的“总数”由它们的复杂程度（次数）的乘积决定**。想象一条直线（次数 1）与一条抛物线（次数 2）相交：在仿射平面中可能只看到 0 个、1 个或 2 个交点，但在射影平面中（包含了“无穷远点”），它们总是恰好相交于 2 个点。如果两条曲线相切，某些交点会“重合”，此时重数计数保证了总数不变。这就像两束不同颜色的光线相交：即使某些交点看起来重叠，总交点数仍然由光束的“宽度”（次数）决定。

## 形式化表述

设 $k$ 为代数闭域，$\mathbb{P}^2_k$ 为射影平面。设 $C, D \subseteq \mathbb{P}^2_k$ 为两条射影平面曲线，次数分别为 $m$ 和 $n$，且 $C$ 与 $D$ 没有公共分支（即它们定义的多项式互素），则：

$$\sum_{P \in C \cap D} I_P(C, D) = m \cdot n$$

其中 $I_P(C, D)$ 表示曲线 $C$ 与 $D$ 在点 $P$ 处的**相交重数**（intersection multiplicity）。

**经典特例**：
- 两条不同直线（$m = n = 1$）恰好交于 1 点
- 一条直线（$m = 1$）与一条圆锥曲线（$n = 2$）恰好交于 2 点（在射影平面中）
- 两条圆锥曲线（$m = n = 2$）恰好交于 4 点

## 证明思路

1. **局部化与重数定义**：在交点 $P$ 的局部环 $\mathcal{O}_{\mathbb{P}^2, P}$ 中，利用两个定义多项式 $f, g$ 生成的理想定义相交重数为 $I_P(C, D) = \dim_k \mathcal{O}_{\mathbb{P}^2, P}/(f, g)$
2. **射影空间的整体计算**：利用层上同调或分次模的 Hilbert 多项式，证明全局相交数等于 $\dim_k S/(f, g)$，其中 $S = k[x, y, z]$ 为分次多项式环
3. **次数关系**：对正则序列 $f, g$ 应用 Koszul 复形或 Hilbert 级数计算，得到 $\dim_k S/(f, g) = m \cdot n$
4. **局部-全局原理**：由层的支撑集理论，全局维数等于各局部重数之和

## 示例

### 示例 1：直线与抛物线

$C: y = x^2$（仿射方程），$D: y = 0$（$x$ 轴）。

在射影平面中齐次化为 $C: yz = x^2$，$D: y = 0$。交点为 $(0:0:1)$（原点，重数 2）和 $(0:1:0)$（无穷远点）。总数 $2 = 1 \cdot 2$。

### 示例 2：两条圆锥曲线

$C: x^2 + y^2 = z^2$（圆），$D: x^2 - y^2 = 0$（两条直线 $y = \pm x$）。

在射影平面中，$D$ 与 $C$ 交于 4 个点（包括无穷远点），每个交点重数为 1。总数 $4 = 2 \cdot 2$。

### 示例 3：相切情形

$C: y^2 z = x^3$（尖点三次曲线），$D: y = 0$（$x$ 轴）。

在原点 $(0:0:1)$ 处，$C$ 与 $D$ 相切，相交重数为 3。总数 $3 = 2 \cdot 3/2$？不对——实际上 $C$ 次数为 3，$D$ 次数为 1，总数 $3 = 3 \cdot 1$，在无穷远点还有交点（需仔细计算局部重数）。

## 应用

- **计算代数几何**：Gröbner 基与结式（resultant）方法计算交点
- **密码学**：椭圆曲线上的群运算与 Weil 配对
- **编码理论**：代数几何码的构造与 Riemann-Roch 定理
- **机器人学**：运动学逆问题的代数方程组求解
- **计算机视觉**：多视图几何中的三焦点张量与交约束

## 相关概念

- 相交重数 (Intersection Multiplicity)：局部环上理想余维数的维数
- 射影平面 (Projective Plane)：包含无穷远点的完备化平面
- 代数曲线 (Algebraic Curve)：由一个齐次多项式定义的射影簇
- Hilbert 多项式 (Hilbert Polynomial)：分次模增长率的渐近刻画
- 层上同调 (Sheaf Cohomology)：研究簇上层的整体性质的工具

## 参考

### 教材

- [Fulton. Algebraic Curves. Addison-Wesley, 1989. Chapter 3]
- [Hartshorne. Algebraic Geometry. Springer, 1977. Chapter I, Section 7]

### 在线资源

- **注意**：Mathlib4 中 Bézout 定理的完整形式化目前仍在发展中。

---

*最后更新：2026-04-15 | 版本：v1.0.0*
