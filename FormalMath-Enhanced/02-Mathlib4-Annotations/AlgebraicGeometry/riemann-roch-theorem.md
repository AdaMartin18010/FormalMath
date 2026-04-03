---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# Riemann-Roch定理 (Riemann-Roch Theorem)

## Mathlib4 引用

```lean
import Mathlib.AlgebraicGeometry.RiemannRoch
import Mathlib.AlgebraicGeometry.Divisor

namespace RiemannRoch

variable {X : Type*} [Scheme X] [IsCurve X] [IsProper X] [IsSmooth X]

/-- Riemann-Roch定理：曲线上的除子 -/
theorem riemann_roch {D : Divisor X} :
    dim H⁰(X, O_X(D)) - dim H¹(X, O_X(D)) = deg D + 1 - g := by
  -- Serre对偶和Euler示性数
  sorry

/-- 弱Riemann-Roch（存在性形式）-/
theorem weak_riemann_roch {D : Divisor X} (hdeg : 2 * g - 2 < deg D) :
    dim H⁰(X, O_X(D)) = deg D + 1 - g := by
  -- 高次除子情形
  sorry

/-- 典范除子的次数 -/
theorem canonical_degree : deg (canonicalDivisor X) = 2 * g - 2 := by
  -- Riemann-Roch应用于D=0
  sorry

end RiemannRoch
```

## 数学背景

Riemann-Roch定理由Bernhard Riemann在1857年提出（不完整证明），后由Gustav Roch在1865年补全。这是代数曲线理论的中心定理，建立了除子的度数与线丛上整体截面空间维数之间的关系。该定理是代数几何的基石，有许多推广（Hirzebruch-Riemann-Roch、Grothendieck-Riemann-Roch、Atiyah-Singer指标定理）。

## 直观解释

Riemann-Roch定理告诉我们：**曲线上"有特定零点和极点的函数空间"的维数由拓扑（亏格）和几何（度数）决定**。

想象在曲线上放置一些点作为零点和极点。Riemann-Roch说，具有这些限制的亚纯函数空间的维数大致等于"自由度"（度数）减去"拓扑约束"（亏格），再加一。这就像说，你可以在给定零极点条件下找到的函数数量由曲线的"洞数"和你指定的条件共同决定。

## 形式化表述

设 $X$ 是亏格 $g$ 的光滑射影曲线，$D$ 是除子。

**Riemann-Roch定理**：
$$l(D) - l(K - D) = \deg(D) + 1 - g$$

其中：

- $l(D) = \dim H^0(X, \mathcal{O}_X(D))$（截面维数）
- $K$ 是典范除子
- $\deg(D)$ 是除子的度数

**推论**：$\deg(K) = 2g - 2$，$l(K) = g$。

## 证明思路

1. **亚纯函数的 Mittag-Leffler 问题**：
   - 给定主部，寻找亚纯函数

2. **层的上同调**：
   - 用 $H^0$ 和 $H^1$ 表示存在性和障碍

3. **Serre对偶**：
   - $H^1(X, \mathcal{O}_X(D)) \cong H^0(X, \mathcal{O}_X(K-D))^*$
   - 故 $l(K-D) = h^1(D)$

4. **Euler示性数**：
   - $\chi(\mathcal{O}_X(D)) = \deg(D) + 1 - g$
   - Riemann-Roch = $\chi(D) = h^0(D) - h^1(D)$

核心洞察是Serre对偶将上同调配对。

## 示例

### 示例 1：射影直线

$X = \mathbb{P}^1$：$g = 0$，$K = -2[\infty]$。

$l(d[\infty]) = d + 1$（次数 $\leq d$ 的多项式）。

### 示例 2：椭圆曲线

$g = 1$，$K = 0$（典范除子平凡）。

$l(D) - l(-D) = \deg(D)$。

若 $\deg(D) > 0$：$l(D) = \deg(D)$。

### 示例 3：超椭圆曲线

$y^2 = f(x)$，$\deg(f) = 2g + 1$。

计算 $l(n\cdot\infty)$ 得亏格 $g$。

## 应用

- **模空间**：曲线的分类
- **编码理论**：代数几何码（Goppa码）
- **密码学**：椭圆曲线密码
- **弦理论**：弦的世界面
- **计数几何**：Gromov-Witten不变量

## 相关概念

- [除子 (Divisor)](./divisor.md)：形式和的点
- [线丛 (Line Bundle)](./line-bundle.md)：局部自由的秩1层
- [典范除子 (Canonical Divisor)](./canonical-divisor.md)：微分形式的除子
- [Serre对偶 (Serre Duality)](./serre-duality.md)：上同调配对
- [亏格 (Genus)](./genus.md)：曲线的拓扑不变量

## 参考

### 教材

- [Hartshorne. Algebraic Geometry. Springer, 1977. Chapter 4]
- [Fulton. Algebraic Curves. Addison-Wesley, 1969. Chapter 8]

### 历史文献

- [Riemann. Theorie der Abel'schen Functionen. 1857]
- [Roch. Über die Anzahl der willkürlichen Constanten in algebraischen Functionen. 1865]

### 在线资源

- [Mathlib4 文档 - RiemannRoch](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/RiemannRoch.html)
- [Wikipedia - Riemann-Roch Theorem](https://en.wikipedia.org/wiki/Riemann%E2%80%93Roch_theorem)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
