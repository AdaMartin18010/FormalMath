---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# Kähler几何基础

## Mathlib4 引用

```lean
import Mathlib.Geometry.Manifold.Kahler

namespace Geometry

/-- Kähler流形的定义 -/
theorem kahler_manifold_def
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    {g : RiemannianMetric M} {J : AlmostComplexStructure M}
    {ω : DifferentialForm M 2} :
    IsKahler M g J ω ↔
      g.IsHermitian J ∧
      ω = FundamentalForm g J ∧
      d ω = 0 := by
  -- Kähler条件：度量是Hermitian，基本形式闭
  rfl

/-- Kähler流形的Hodge分解 -/
theorem hodge_decomposition_kahler
    {M : Type*} [KahlerManifold M] :
    ∀ (k : ℕ),
      DeRhamCohomology M k ≅
        DirectSum (fun (p q : ℕ) => H^{p,q} M) := by
  -- Hodge分解定理
  sorry

end Geometry
```

## 数学背景

Kähler几何由Erich Kähler在1933年引入，是复微分几何中的核心领域。Kähler流形是同时具有复结构、Riemann度量和辛结构的特殊流形，这三种结构以协调的方式相互作用。复代数几何中的射影簇都是Kähler流形。Hodge理论在Kähler流形上达到最完整的形式，揭示了拓扑、分析和代数之间的深刻联系。

## 直观解释

Kähler流形是"三者合一"的几何对象：它既是复流形（有复结构），又是Riemann流形（有度量），还是辛流形（有闭的非退化2-形式）。这三种结构协调一致，使得Kähler几何成为研究代数簇的理想框架。想象Kähler流形如同一个完美的水晶——同时具有复杂的内部结构（复几何）、测量距离的能力（Riemann几何）和守恒的"面积"概念（辛几何）。

## 形式化表述

设 $M$ 是复流形，$J$ 是复结构，$g$ 是Riemann度量，$\omega$ 是2-形式。

**Kähler条件**：

1. $g$ 是**Hermitian度量**：$g(JX, JY) = g(X, Y)$
2. **基本形式**：$\omega(X, Y) = g(JX, Y)$（辛形式）
3. **Kähler条件**：$d\omega = 0$（$\omega$ 是闭形式）

**等价条件**：

- $\nabla J = 0$（复结构关于Levi-Civita联络平行）
- 存在局部Kähler势 $\phi$ 使得 $\omega = i \partial \bar{\partial} \phi$

**Hodge分解**：对紧Kähler流形，
$$H^k(M, \mathbb{C}) = \bigoplus_{p+q=k} H^{p,q}(M)$$
其中 $H^{p,q}(M)$ 是调和 $(p,q)$-形式的空间。

## 证明思路

1. **Hermitian几何**：建立复流形上的度量理论
2. **基本形式的性质**：验证辛结构条件
3. **Kähler恒等式**：$[L, \Lambda]$ 关系
4. **Hodge定理**：紧流形上调和形式与上同调的同构
5. **dd^c-引理**：$(p,q)$-分量的纯性

## 示例

### 示例 1：复射影空间

**问题**：证明 $\mathbb{CP}^n$ 是Kähler流形。

**解答**：

Fubini-Study度量：在齐次坐标 $[z_0: \cdots: z_n]$ 上，
$$\omega_{FS} = \frac{i}{2\pi} \partial \bar{\partial} \log(|z_0|^2 + \cdots + |z_n|^2)$$

这是闭的 $(1,1)$-形式，诱导的度量是Hermitian且正定的。

因此 $(\mathbb{CP}^n, \omega_{FS})$ 是紧Kähler流形。

### 示例 2：复环面

**问题**：描述复环面 $T = \mathbb{C}^n / \Lambda$ 的Kähler结构。

**解答**：

复环面自动继承 $\mathbb{C}^n$ 的平坦度量 $g = \sum dz_i \otimes d\bar{z}_i$。

基本形式 $\omega = \frac{i}{2} \sum dz_i \wedge d\bar{z}_i$ 显然是闭的。

因此任何复环面都是Kähler流形。

## 应用

- **代数几何**：射影簇的Hodge理论
- **弦理论**：Calabi-Yau流形（Kähler的特例）
- **镜像对称**：SYZ猜想的Kähler几何基础
- **几何不变量理论**：Mumford的稳定性
- **算术几何**：p-adic Hodge理论

## 相关概念

- [Hodge分解](./hodge-decomposition.md)：Kähler流形上的精细结构
- [复结构](./complex-structure.md)：Kähler几何的基础
- [辛几何](./symplectic-geometry.md)：与Kähler几何的联系
- [Calabi-Yau流形](./calabi-yau-manifold.md)：Ricci平坦Kähler流形
- [Kähler-Einstein度量](./kahler-einstein-metric.md)：特殊Kähler度量

## 参考

### 教材

- Huybrechts, D. Complex Geometry: An Introduction. Springer, 2005.
- Voisin, C. Hodge Theory and Complex Algebraic Geometry. Cambridge, 2002.

### 论文

- Kähler, E. Über eine bemerkenswerte Hermitesche Metrik. Abh. Math. Sem. Univ. Hamburg, 9: 173-186, 1933.
- Hodge, W.V.D. The Theory and Applications of Harmonic Integrals. Cambridge, 1941.

### 在线资源

- [Kähler Manifold Wikipedia](https://en.wikipedia.org/wiki/Kähler_manifold)
- [nLab - Kähler Manifold](https://ncatlab.org/nlab/show/Kähler+manifold)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
