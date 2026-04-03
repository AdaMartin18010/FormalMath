---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# Gauss-Bonnet定理 (Gauss-Bonnet Theorem)

## Mathlib4 引用

```lean
import Mathlib.Geometry.Manifold.Curvature.GaussBonnet
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

namespace GaussBonnet

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [SmoothManifoldWithCorners (𝓡 2) M] [Orientable M] [CompactSpace M]

/-- Gauss-Bonnet定理：曲率积分与欧拉示性数 -/
theorem gauss_bonnet [hM : IsBoundaryless M] :
    (1 / (2 * π)) • ∫ x in M, sectionalCurvature x = eulerCharacteristic M := by
  -- Poincaré-Hopf定理和曲率的关系
  sorry

/-- Gauss-Bonnet定理（带边界）-/
theorem gauss_bonnet_boundary {γ : M → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    [IsImmersion γ] :
    (1 / (2 * π)) • ∫ x in M, GaussianCurvature x +
    (1 / (2 * π)) • ∫ x in ∂M, geodesicCurvature x +
    ∑ p ∈ corners, exteriorAngle p = eulerCharacteristic M := by
  -- 边界贡献：测地曲率和外角
  sorry

/-- 紧致曲面的分类 -/
theorem compact_surface_classification (hM : CompactSpace M) (hM2 : SecondCountableTopology M) :
    ∃ g k : ℕ, M ≃ₘ (ConnectedSum (g copies of Torus)) # (k copies of Disk) := by
  -- Gauss-Bonnet的推论
  sorry

end GaussBonnet
```

## 数学背景

Gauss-Bonnet定理由Carl Friedrich Gauss在1827年（局部形式）和Pierre Bonnet在1848年（推广到测地多边形）建立。这是微分几何中最深刻的结果之一，连接了局部几何量（曲率）与全局拓扑量（欧拉示性数）。该定理是指标定理、Chern-Weil理论和几何拓扑的出发点，揭示了曲面的几何与拓扑之间的深刻联系。

## 直观解释

Gauss-Bonnet定理告诉我们：**曲面的"弯曲"总量完全由曲面的拓扑决定**。

想象一张橡皮膜（曲面）。你可以拉伸它改变局部曲率，但不能改变曲率的总积分——这由膜的"洞数"（拓扑）固定。正曲率像山峰（球面），负曲率像马鞍（环面），零曲率像平面。定理说，把所有这些曲率加起来（加权积分），结果只取决于曲面有几个洞。

## 形式化表述

设 $M$ 是紧致定向无边黎曼曲面。

**Gauss-Bonnet定理**：
$$\frac{1}{2\pi} \int_M K \, dA = \chi(M) = 2 - 2g$$

其中：

- $K$ 是高斯曲率
- $\chi(M)$ 是欧拉示性数
- $g$ 是亏格（洞的个数）

**带边界形式**：
$$\frac{1}{2\pi}\left(\int_M K \, dA + \int_{\partial M} k_g \, ds + \sum_i \theta_i\right) = \chi(M)$$

其中 $k_g$ 是测地曲率，$\theta_i$ 是外角。

## 证明思路

1. **三角剖分**：
   - 将 $M$ 三角剖分
   - 对每个三角形应用局部Gauss-Bonnet

2. **角度求和**：
   - 内角和与曲率的关系
   - $2\pi - (\alpha + \beta + \gamma) = \int_{\triangle} K \, dA$

3. **整体求和**：
   - 所有三角形的角度和
   - 顶点贡献：$2\pi V$
   - 边贡献：$\pi E$（每条边两次）

4. **欧拉公式**：
   - $V - E + F = \chi(M)$
   - 结合得到定理

核心洞察是角度缺损与曲率的局部-整体关系。

## 示例

### 示例 1：球面

$S^2$：$K = 1$（常曲率），$\text{Area}(S^2) = 4\pi$。

$\frac{1}{2\pi} \int K dA = \frac{4\pi}{2\pi} = 2 = \chi(S^2)$。

亏格 $g = 0$（无洞）。

### 示例 2：环面

$T^2$：$K = 0$（平坦度量）。

$\frac{1}{2\pi} \int K dA = 0 = \chi(T^2) = 2 - 2 \cdot 1$。

亏格 $g = 1$（一个洞）。

### 示例 3：双曲曲面

亏格 $g \geq 2$ 的曲面：存在 $K = -1$ 的度量。

$\text{Area}(M) = 2\pi(2g - 2) = -2\pi \chi(M)$。

## 应用

- **拓扑学**：曲面分类
- **广义相对论**：时空的整体结构
- **统计力学**：缺陷的几何
- **弦理论**：世界面的欧拉示性数
- **离散几何**：多面体的角度和

## 相关概念

- [高斯曲率 (Gaussian Curvature)](./gaussian-curvature.md)：曲面的内在曲率
- [欧拉示性数 (Euler Characteristic)](./euler-characteristic.md)：拓扑不变量
- [亏格 (Genus)](./genus.md)：洞的个数
- [测地曲率 (Geodesic Curvature)](./geodesic-curvature.md)：边界的弯曲
- [三角剖分 (Triangulation)](./triangulation.md)：曲面的分割

## 参考

### 教材

- [do Carmo. Differential Geometry of Curves and Surfaces. Prentice-Hall, 1976. Chapter 6]
- [Lee. Riemannian Manifolds. Springer, 1997. Chapter 9]

### 历史文献

- [Gauss. Disquisitiones generales circa superficies curvas. 1827]
- [Bonnet. Mémoire sur la théorie générale des surfaces. 1848]

### 在线资源

- [Mathlib4 文档 - GaussBonnet](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/Curvature/GaussBonnet.html)
- [Wikipedia - Gauss-Bonnet Theorem](https://en.wikipedia.org/wiki/Gauss%E2%80%93Bonnet_theorem)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
