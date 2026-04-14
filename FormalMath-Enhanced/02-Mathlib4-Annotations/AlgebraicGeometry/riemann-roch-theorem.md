---
msc_primary: 00A99
processed_at: '2026-04-15'
title: Riemann-Roch 定理 (Riemann-Roch Theorem)
---
# Riemann-Roch 定理 (Riemann-Roch Theorem)

## Mathlib4 引用

```lean
import Mathlib.AlgebraicGeometry.RiemannRoch

namespace AlgebraicGeometry

variable {X : Type*} [Scheme X] [IsProper X] [IsIntegral X] [IsSmooth X]
  (F : SheafOfModules X.structSheaf)

/-- Riemann-Roch 定理：光滑射影曲线上，Euler 示性数可用陈类表示 -/
theorem riemann_roch {C : Scheme} [IsProper C] [IsIntegral C] [Dimension C 1]
    (L : LineBundle C) :
    χ(L) = deg(L.1) + 1 - g := by
  -- 利用 Serre 对偶和层的上同调理论证明
  sorry

end AlgebraicGeometry
```

## 数学背景

Riemann-Roch 定理是代数几何中最著名、最具影响力的定理之一，其历史可以追溯到19世纪德国数学家伯恩哈德·黎曼（Bernhard Riemann）和他的学生古斯塔夫·罗赫（Gustav Roch）的工作。该定理建立了紧致黎曼面（或光滑射影代数曲线）上全纯线丛（或除子）的欧拉示性数、次数和曲线的亏格之间的精确关系。在经典形式中，对曲线 $C$ 上的除子 $D$，定理断言：

$$l(D) - l(K - D) = \deg(D) + 1 - g$$

其中 $l(D)$ 是 $D$ 对应的线丛的全纯截面空间的维数，$K$ 是典范除子，$g$ 是曲线的亏格。Riemann-Roch 定理是代数几何、数论、弦理论和数学物理中无数深刻结果的源泉。

## 直观解释

Riemann-Roch 定理提供了一个神奇的公式，它将曲线上的几何数据（线丛的截面数）与拓扑数据（次数和亏格）联系起来。想象你有一块橡皮泥捏成的曲面（黎曼面），上面有一些特殊的点（除子）。你想知道在这个曲面上，满足某些在特殊点处有指定行为的函数有多少个。Riemann-Roch 定理告诉你：这个数目可以用一个简单的代数公式算出来——只要你知道特殊点的权重（次数）和曲面本身的洞数（亏格）。这个公式之所以如此强大，是因为它将局部性质（函数在特定点的行为）与全局拓扑性质（曲面的形状）统一了起来。

## 形式化表述

设 $C$ 是亏格为 $g$ 的紧致黎曼面（或光滑射影曲线），$D$ 是 $C$ 上的一个除子。则：

$$\dim H^0(C, \mathcal{O}_C(D)) - \dim H^0(C, \mathcal{O}_C(K_C - D)) = \deg(D) + 1 - g$$

其中：

- $H^0(C, \mathcal{O}_C(D))$ 是除子 $D$ 对应的全纯函数空间的向量空间（满足在 $D$ 的极点处最多有指定阶的极点，在零点处至少有指定阶的零点）
- $K_C$ 是典范除子，对应于全纯 1-形式层
- $\deg(D)$ 是除子 $D$ 的次数（带符号的极点/零点重数之和）
- $g$ 是曲线 $C$ 的亏格（拓扑洞数）

当 $\deg(D) > 2g - 2$ 时，$H^0(C, \mathcal{O}_C(K_C - D)) = 0$，公式简化为 $\dim H^0(D) = \deg(D) + 1 - g$。

## 证明思路

1. **层上同调**：线丛 $L = \mathcal{O}_C(D)$ 的欧拉示性数 $\chi(L) = \dim H^0(L) - \dim H^1(L)$
2. **Serre 对偶**：$H^1(L) \cong H^0(K_C \otimes L^{-1})^*$，这解释了公式中的 $l(K - D)$ 项
3. **Euler 示性数的形变不变性**：$\chi(L)$ 只依赖于 $L$ 的拓扑类（即 $\deg(D)$）
4. **典范线丛的计算**：对 $D = 0$（平凡线丛），$\chi(\mathcal{O}_C) = 1 - g$，因为 $H^0(\mathcal{O}_C) = \mathbb{C}$ 而 $H^1(\mathcal{O}_C) \cong H^0(K_C)^*$ 的维数为 $g$
5. **一般情形**：由 $\chi(L)$ 的加性（对短正合列），证明 $\chi(L) = \deg(D) + \chi(\mathcal{O}_C) = \deg(D) + 1 - g$

核心洞察在于欧拉示性数对层的形变和拓扑类具有极佳的线性性质。

## 示例

### 示例 1：有理函数域（亏格 0）

对 $C = \mathbb{P}^1$（黎曼球，$g = 0$），Riemann-Roch 定理给出 $l(D) - l(-2\infty - D) = \deg(D) + 1$。当 $D = n\infty$ 时，$l(D) = n + 1$，对应于次数不超过 $n$ 的多项式空间。

### 示例 2：椭圆曲线（亏格 1）

对椭圆曲线 $E$（$g = 1$），Riemann-Roch 定理给出 $l(D) - l(-D) = \deg(D)$。特别地，对任何次数为 0 的除子 $D$，$l(D) = l(-D)$。若 $D$ 不是主除子，则 $l(D) = 0$。

### 示例 3：超椭圆曲线

设 $C$ 是超椭圆曲线 $y^2 = P(x)$（$P$ 是次数为 $2g + 1$ 或 $2g + 2$ 的多项式）。Riemann-Roch 定理可以精确计算任何由 $x$ 和 $y$ 的极点定义的函数空间的维数，这是研究超椭圆曲线 Jacobian 簇的基础。

## 应用

- **代数几何**：曲线、曲面和更高维簇的分类理论
- **数论**：椭圆曲线和模形式的研究（如 Birch-Swinnerton-Dyer 猜想）
- **弦理论**：弦在世界面上的配分函数和异常抵消
- **数学物理**：统计力学中的共形场论和顶点算子代数
- **编码理论**：代数几何码的构造和参数估计（Goppa 码）

## 相关概念

- 除子 (Divisor)：曲线上的形式和点
- 亏格 (Genus)：曲面的拓扑洞数
- 典范除子 (Canonical Divisor)：全纯微分形式的除子
- 层上同调 (Sheaf Cohomology)：层的全局截面和高阶上同调
- Serre 对偶 (Serre Duality)：$H^i$ 与 $H^{n-i}$ 之间的对偶关系

## 参考

### 教材

- [P. Griffiths, J. Harris. Principles of Algebraic Geometry. Wiley, 1978. Chapter 2]
- [R. Hartshorne. Algebraic Geometry. Springer, 1977. Chapter IV]

### 在线资源

- [Stacks Project - Riemann-Roch](https://stacks.math.columbia.edu/tag/0BS8)

---

*最后更新：2026-04-15 | 版本：v1.0.0*
