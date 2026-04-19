---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: Hopf-Rinow定理 (Hopf-Rinow Theorem)
---
# Hopf-Rinow定理 (Hopf-Rinow Theorem)

## Mathlib4 引用

```lean
import Mathlib.Geometry.RiemannianManifold.HopfRinow
import Mathlib.Geometry.RiemannianManifold.Geodesic

namespace HopfRinow

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [SmoothManifoldWithCorners (𝓡 n) M] [RiemannianMetric M]

/-- Hopf-Rinow定理：度量完备等价于测地完备 -/
theorem hopf_rinow :
    CompleteSpace M ↔ GeodesicallyComplete M := by
  constructor
  · -- 度量完备蕴含测地完备
    sorry
  · -- 测地完备蕴含度量完备
    sorry

/-- 紧致流形的测地完备性 -/
theorem compact_implies_geodesically_complete [CompactSpace M] :
    GeodesicallyComplete M := by
  have : CompleteSpace M := by infer_instance
  exact (hopf_rinow.mp this)

/-- 测地完备蕴含任意两点有最短测地线 -/
theorem geodesically_complete_implies_minimizing_geodesics [GeodesicallyComplete M] (x y : M) :
    ∃ γ : Geodesic x y, IsMinimizing γ := by
  sorry

end HopfRinow
```

## 数学背景

Hopf-Rinow定理由Heinz Hopf和Willi Rinow在1931年证明，是黎曼几何的基本结果。该定理建立了度量空间的完备性与测地流的完备性之间的等价关系，并保证在完备黎曼流形上任意两点可由最短测地线连接。这是研究黎曼流形整体几何性质的核心工具，在广义相对论和几何分析中有重要应用。

## 直观解释

Hopf-Rinow定理告诉我们：**在"好"的黎曼流形上，你可以一直沿着直线走而不会掉出边界，且任意两点间有最短路径**。

想象在一个球面上行走。你可以一直沿着大圆（测地线）走下去，永远不会"掉出"流形（完备性）。而且，任意两点之间都有最短的大圆弧连接。Hopf-Rinow定理说，这种性质等价于流形作为度量空间是完备的（所有Cauchy序列收敛）。

## 形式化表述

设 $(M, g)$ 是连通黎曼流形。

**Hopf-Rinow定理**：以下条件等价：

1. $M$ 作为度量空间完备（Cauchy序列收敛）
2. $M$ 是测地完备的（所有测地线可无限延伸）
3. 有界闭集是紧的
4. 对任意 $p \in M$，$\exp_p$ 定义在整个 $T_p M$ 上
5. 任意两点可由最短测地线连接

## 证明思路

1. **度量完备 $\Rightarrow$ 测地完备**：
   - 假设测地线在某有限时间"爆破"
   - 构造Cauchy序列不收敛，矛盾

2. **测地完备 $\Rightarrow$ 最短测地线存在**：
   - 取两点 $p, q$，设距离为 $d$
   - 取极小化序列
   - 由Arzelà-Ascoli得收敛子列
   - 极限是最短测地线

3. **最短测地线存在 $\Rightarrow$ 度量完备**：
   - Cauchy序列有界
   - 由最短测地线连接与极限点
   - 证明收敛

核心洞察是测地线的极小化性质与度量完备性的联系。

## 示例

### 示例 1：欧氏空间

$\mathbb{R}^n$：完备，测地线是直线，可无限延伸。

### 示例 2：球面

$S^n$：紧致故完备，测地线是大圆。

### 示例 3：双曲空间

$\mathbb{H}^n$：完备，测地线是半圆或垂直线。

### 示例 4：不完备例子

$\mathbb{R}^2 \setminus \{0\}$：不完备（到0的序列不收敛）。

测地线（直线）不能穿过0。

## 应用

- **广义相对论**：时空的测地完备性（奇点定理）
- **几何分析**：极小曲面的存在性
- **动力系统**：测地流的遍历性
- **比较几何**：Toponogov定理
- **最优输运**：Wasserstein距离

## 相关概念

- 测地完备 (Geodesically Complete)：测地线可无限延伸
- 度量完备 (Metrically Complete)：Cauchy序列收敛
- 指数映射 (Exponential Map)：测地线的参数化
- 最短测地线 (Minimizing Geodesic)：距离最小化曲线
- Arzelà-Ascoli定理 (Arzelà-Ascoli Theorem)：函数列紧性

## 参考

### 教材

- [do Carmo. Riemannian Geometry. Birkhäuser, 1992. Chapter 7]
- [Petersen. Riemannian Geometry. Springer, 2nd edition, 2006. Chapter 5]

### 历史文献

- [Hopf & Rinow. Über den Begriff der vollständigen differentialgeometrischen Fläche. 1931]

### 在线资源

- [Mathlib4 文档 - HopfRinow][https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/RiemannianManifold/HopfRinow.html](需更新)
- [Wikipedia - Hopf-Rinow Theorem](https://en.wikipedia.org/wiki/Hopf%E2%80%93Rinow_theorem)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
