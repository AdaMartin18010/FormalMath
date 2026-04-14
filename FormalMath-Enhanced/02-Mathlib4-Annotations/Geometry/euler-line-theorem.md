---
msc_primary: 00A99
processed_at: '2026-04-15'
title: 欧拉线定理 (Euler Line Theorem)
---
# 欧拉线定理 (Euler Line Theorem)

## Mathlib4 引用

```lean
import Mathlib.Geometry.Euclidean.Triangle

namespace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- 欧拉线定理：三角形的垂心 H、重心 G、外心 O 共线，且 HG = 2 GO -/
theorem euler_line_theorem (A B C : P) (hnondegenerate : ¬ Collinear ℝ {A, B, C}) :
    Collinear ℝ {orthocenter A B C, centroid A B C, circumcenter A B C} := by
  -- 利用坐标法或向量法证明三点共线
  sorry

end EuclideanGeometry
```

## 数学背景

欧拉线定理由瑞士数学家莱昂哈德·欧拉（Leonhard Euler）于1765年证明，是欧几里得几何中最优美的结果之一。该定理揭示了任意非退化三角形的三个重要中心点——垂心（三条高的交点）、重心（三条中线的交点）和外心（三边垂直平分线的交点）——必定位于同一条直线上，这条直线被称为欧拉线。更精确地，重心 $G$ 位于垂心 $H$ 和外心 $O$ 之间，且 $HG : GO = 2 : 1$。

## 直观解释

欧拉线定理揭示了一个令人惊叹的事实：在任何三角形中，三个最重要的几何中心点——垂心（高的汇聚点）、重心（质量的平衡点）和外心（外接圆的圆心）——总是惊人地排列在一条直线上。这就像一个精心设计的宇宙秩序：无论三角形是锐角、钝角还是直角，这三个点从不各自为政。特别地，对于等边三角形，这三个点重合为一点；而对于直角三角形，垂心恰好是直角顶点，外心则在斜边中点。

## 形式化表述

设 $ABC$ 是一个非退化三角形，$H$ 为垂心，$G$ 为重心，$O$ 为外心，则：

1. $H, G, O$ 三点共线（这条直线称为欧拉线）
2. $G$ 在线段 $HO$ 上，且满足 $\vec{HG} = 2 \vec{GO}$，即 $HG : GO = 2 : 1$

用向量表示（以外心 $O$ 为原点）：

$$\vec{OH} = \vec{OA} + \vec{OB} + \vec{OC}$$
$$\vec{OG} = \frac{1}{3}(\vec{OA} + \vec{OB} + \vec{OC})$$

因此 $\vec{OH} = 3 \vec{OG}$，即 $O, G, H$ 共线且 $OG : GH = 1 : 2$。

其中：

- 垂心 $H$：三条高的交点
- 重心 $G$：三条中线的交点，也是三角形的质量中心
- 外心 $O$：外接圆的圆心，三边垂直平分线的交点

## 证明思路

1. **向量法**：设 $O$ 为外心（原点），利用 $\vec{OH} = \vec{OA} + \vec{OB} + \vec{OC}$（垂心的向量公式），以及 $\vec{OG} = \frac{1}{3}(\vec{OA} + \vec{OB} + \vec{OC})$，直接得 $\vec{OH} = 3\vec{OG}$
2. **坐标法**：将三角形放在坐标系中，分别计算三点的坐标，验证它们满足同一直线方程
3. **相似三角形法**：连接中点构成中位三角形，利用外心是中位三角形的垂心这一性质，结合位似变换证明共线
4. **重心坐标法**：在重心坐标系中，$O, G, H$ 的坐标分别为 $(a^2(b^2+c^2-a^2), \dots)$, $(1:1:1)$, $(\tan A : \tan B : \tan C)$，验证行列式为零

核心洞察在于外心、重心、垂心之间存在以重心为中心、比例为 $-1/2$ 的位似关系。

## 示例

### 示例 1：直角三角形

在直角三角形中，垂心 $H$ 是直角顶点，外心 $O$ 是斜边中点，重心 $G$ 位于连接两者的线段上且 $HG : GO = 2 : 1$。

### 示例 2：等边三角形

在等边三角形中，$H = G = O$，欧拉线退化为一个点。这是欧拉线定理的退化情形。

### 示例 3：九点圆心

三角形的九点圆心 $N$ 也在欧拉线上，且是 $OH$ 的中点。即 $ON = NH$ 且 $GN = \frac{1}{4}OH$。九点圆是连接三边中点、三垂足和顶点到垂心线段中点的圆。

## 应用

- **计算机图形学**：三角形网格的质心和外接圆计算
- **结构力学**：三角形框架的应力分析和稳定性研究
- **几何画板与数学教育**：动态几何软件中的经典演示定理
- **天体测量学**：三角测量中的中心点计算
- **凸几何**：多面体和单纯形的重心与对偶结构研究

## 相关概念

- 垂心 (Orthocenter)：三角形三条高的交点
- 重心 (Centroid)：三角形三条中线的交点，质量中心
- 外心 (Circumcenter)：三角形外接圆的圆心
- 九点圆 (Nine-Point Circle)：通过九个特殊点的圆
- 位似变换 (Homothety)：以固定点为中心的比例缩放

## 参考

### 教材

- [H. S. M. Coxeter. Introduction to Geometry. Wiley, 2nd edition, 1969. Section 1.7]
- [R. Honsberger. Episodes in Nineteenth and Twentieth Century Euclidean Geometry. MAA, 1995. Chapter 1]

### 在线资源

- [Mathlib4 - Euclidean Triangle](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Euclidean/Triangle.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*