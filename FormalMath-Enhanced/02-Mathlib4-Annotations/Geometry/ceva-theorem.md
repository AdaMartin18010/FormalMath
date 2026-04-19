---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: Ceva 定理 (Ceva's Theorem)
---
# Ceva 定理 (Ceva's Theorem)

## Mathlib4 引用

```lean
import Mathlib.Geometry.Euclidean.Triangle

namespace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- Ceva 定理：三角形中三条 cevian 共点当且仅当 (AF/FB)(BD/DC)(CE/EA) = 1 -/
theorem ceva_theorem (A B C D E F : P)
    (hD : D ∈ line ℝ B C) (hE : E ∈ line ℝ C A) (hF : F ∈ line ℝ A B)
    (hDne : D ≠ B ∧ D ≠ C) (hEne : E ≠ C ∧ E ≠ A) (hFne : F ≠ A ∧ F ≠ B) :
    Collinear ℝ {A, D, midpoint ℝ B C} → Collinear ℝ {B, E, midpoint ℝ C A} →
    Collinear ℝ {C, F, midpoint ℝ A B} ↔
    (dist A F / dist F B) * (dist B D / dist D C) * (dist C E / dist E A) = 1 := by
  -- 利用面积比或 Menelaus 定理证明
  sorry

end EuclideanGeometry
```

## 数学背景

Ceva 定理由意大利数学家乔瓦尼·切瓦（Giovanni Ceva）于1678年发表，是平面几何中关于三角形 cevian 线共点性的核心结果。该定理断言：在三角形 $ABC$ 中，若点 $D, E, F$ 分别位于边 $BC, CA, AB$（或其延长线）上，则三线 $AD, BE, CF$ 共点（或互相平行）的充要条件是：

$$\frac{AF}{FB} \cdot \frac{BD}{DC} \cdot \frac{CE}{EA} = 1$$
Ceva 定理统一了三角形中众多重要的共点定理——如中线共点（重心）、高线共点（垂心）、角平分线共点（内心）——使它们成为该定理的直接推论。

## 直观解释

Ceva 定理提供了一个判断三角形内三条线段是否交于一点的优雅标准。想象三角形的三条边上有三个渡口 $D, E, F$，三条航线 $AD, BE, CF$ 分别从顶点到对边上的渡口。Ceva 定理告诉我们：这三条航线会汇聚于一点（就像三条河流汇入同一个湖泊）当且仅当三个渡口将各边分割成的比例满足一个奇妙的乘积关系——$\frac{AF}{FB} \cdot \frac{BD}{DC} \cdot \frac{CE}{EA} = 1$。这个乘积为 1 的条件意味着三个比例的顺时针影响恰好相互抵消。

## 形式化表述

设 $D, E, F$ 分别是三角形 $ABC$ 的边 $BC, CA, AB$（或其延长线）上的点，则三线 $AD, BE, CF$ 共点或互相平行的充要条件是：

$$\frac{AF}{FB} \cdot \frac{BD}{DC} \cdot \frac{CE}{EA} = 1$$

其中比例是有向线段比（若考虑延长线上的点，比例可能为负）。

若 $D, E, F$ 都在边的内部，则共点的充要条件是无向比例的乘积等于 1。

其中：

- $AD, BE, CF$ 称为 cevian（从顶点到对边或其延长线的线段）
- 比例 $\frac{AF}{FB}$ 表示点 $F$ 分边 $AB$ 的比
- 当乘积为 1 时，三线要么共点，要么互相平行

## 证明思路

1. **面积法**：利用三角形面积比等于底边比（同高时），将各比例转化为面积比，三面积比的乘积恰好相互抵消得 1
2. **Menelaus 定理法**：在适当构造的三角形中应用 Menelaus 定理
3. **质量点法**：在顶点和分点处放置适当质量，利用重心原理证明共点条件
4. **重心坐标法**：在重心坐标系中，$D = (0 : DC : BD)$，$E = (CE : 0 : EA)$，$F = (AF : FB : 0)$，三线共点当且仅当行列式 $AF \cdot BD \cdot CE = FB \cdot DC \cdot EA$

核心洞察在于 cevian 的共点性等价于各边分比的一种循环乘积平衡。

## 示例

### 示例 1：重心

中线交于重心：$D, E, F$ 是三边中点，则 $AF/FB = BD/DC = CE/EA = 1$，乘积为 $1 \times 1 \times 1 = 1$。由 Ceva 定理，三线共点。

### 示例 2：内心

角平分线交于内心：由角平分线定理，$BD/DC = AB/AC$, $CE/EA = BC/AB$, $AF/FB = AC/BC$。乘积为 $(AC/BC) \cdot (AB/AC) \cdot (BC/AB) = 1$。

### 示例 3：垂心

高线交于垂心：利用相似三角形可证 $AF/FB = (AC \cos A)/(BC \cos B)$ 等，三式相乘后利用正弦定理化简得 1。

## 应用

- **三角形几何**：统一证明重心、垂心、内心、外心的共点性质
- **射影几何**：与 Desargues 定理和 Pappus 定理的联系
- **质量点几何**：物理平衡问题中的力矩分析
- **重心坐标**：解析几何中三角形内部点的参数表示
- **数学竞赛**：平面几何奥林匹克问题中的核心工具

## 相关概念

- Cevian (Cevian Line)：从三角形顶点到对边或其延长线的线段
- Menelaus 定理 (Menelaus's Theorem)：关于截线与三角形三边交点的定理
- 重心坐标 (Barycentric Coordinates)：以三角形顶点为参照的坐标系
- 共点 (Concurrency)：多条直线交于同一点
- 角平分线定理 (Angle Bisector Theorem)：角平分线分对边成比例于邻边

## 参考

### 教材

- [H. S. M. Coxeter. Introduction to Geometry. Wiley, 2nd edition, 1969. Section 1.2]
- [R. Honsberger. Episodes in Nineteenth and Twentieth Century Euclidean Geometry. MAA, 1995. Chapter 3]

### 在线资源

- [Mathlib4 - Euclidean Triangle](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Euclidean/Triangle.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*