---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: 九点圆定理 (Nine-Point Circle Theorem)
---
# 九点圆定理 (Nine-Point Circle Theorem)

## Mathlib4 引用

```lean
import Mathlib.Geometry.Euclidean.Triangle

namespace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- 九点圆定理：三角形三边中点、三垂足、顶点到垂心线段中点共圆 -/
theorem nine_point_circle (A B C : P) (hnondegenerate : ¬ Collinear ℝ {A, B, C}) :
    Concyclic
      {midpoint ℝ A B, midpoint ℝ B C, midpoint ℝ C A,
       foot A B C, foot B A C, foot C A B,
       midpoint ℝ A (orthocenter A B C), midpoint ℝ B (orthocenter A B C),
       midpoint ℝ C (orthocenter A B C)} := by
      -- 利用中位三角形的外接圆和垂心的位似关系证明
      sorry

end EuclideanGeometry
```

## 数学背景

九点圆定理是欧几里得几何中最优雅、最令人惊奇的定理之一，由卡尔·威廉·费尔巴哈（Karl Wilhelm Feuerbach）于1822年系统证明并发表。该定理断言：在任何三角形中，九个特殊点——三边的中点、三个垂足（高线与对边的交点）、以及顶点到垂心线段的中点——必定共圆，这个圆被称为九点圆（或费尔巴哈圆）。九点圆的圆心恰好在欧拉线上，是外心与垂心的中点；其半径是外接圆半径的一半。

## 直观解释

九点圆定理揭示了一个令人难以置信的几何巧合：在任何三角形中，九个看似毫无关联的点竟然都躺在同一个圆上。这九个点分别是：三条边的中点（像三角形的腰部）、三个垂足（像从顶点垂直落下的脚印）、以及连接每个顶点与垂心的线段中点（像顶点与高原之间的半山点）。更令人惊叹的是，这个九点圆的圆心恰好位于欧拉线上，半径恰好是外接圆的一半。就像三角形内部隐藏着一个完美的小宇宙，所有的关键构造都以一种和谐的方式相互关联。

## 形式化表述

设 $ABC$ 是一个非退化三角形，则以下九点共圆：

1. **三边中点**：$D$（$BC$ 中点）、$E$（$AC$ 中点）、$F$（$AB$ 中点）
2. **三垂足**：$D'$（从 $A$ 到 $BC$ 的垂足）、$E'$（从 $B$ 到 $AC$ 的垂足）、$F'$（从 $C$ 到 $AB$ 的垂足）
3. **顶点到垂心的中点**：$D''$（$AH$ 中点）、$E''$（$BH$ 中点）、$F''$（$CH$ 中点）

九点圆的性质：

- **圆心** $N$：欧拉线上外心 $O$ 与垂心 $H$ 的中点
- **半径** $R_9 = R/2$，其中 $R$ 是外接圆半径
- **费尔巴哈定理**：九点圆与三角形的内切圆和三个旁切圆都相切

其中 $H$ 是三角形的垂心。

## 证明思路

1. **中位三角形法**：三角形 $DEF$（由三边中点构成）的外接圆就是九点圆。因为 $DEF$ 与 $ABC$ 位似，位似中心为重心 $G$，比例为 $-1/2$
2. **垂足共圆**：证明垂足 $D', E', F'$ 也在中位三角形的外接圆上，利用圆内接四边形的对角互补性质
3. **顶垂中点共圆**：证明 $D'', E'', F''$ 也在同一个圆上，利用欧拉线和中点性质
4. **统一证明**：以欧拉线中点 $N$ 为圆心，$R/2$ 为半径，直接验证这九点到 $N$ 的距离相等

核心洞察在于九点圆是中位三角形的外接圆在垂心位似下的像。

## 示例

### 示例 1：直角三角形

在直角三角形 $ABC$（$C = 90^\circ$）中，垂心 $H = C$。九点圆的九个点包括：斜边中点、两直角边中点、直角顶点 $C$（垂足）、以及另外两条高的垂足（即直角顶点）、$AC$ 和 $BC$ 的中点等。此时九点圆退化为以斜边中点为圆心、斜边一半为半径的圆。

### 示例 2：等边三角形

在等边三角形中，九点圆与外接圆、内切圆同心（因为 $O = G = H$），半径为外接圆半径的一半。九个点中有许多重合。

### 示例 3：费尔巴哈点

九点圆与内切圆的切点称为费尔巴哈点。在一般三角形中，这个点是唯一的且具有重要的射影几何意义。

## 应用

- **几何教育**：动态几何软件（如 GeoGebra）中的经典教学案例
- **计算机图形学**：三角形细分和网格光滑中的圆约束
- **结构工程**：三角形框架对称性分析和优化设计
- **射影几何**：圆锥曲线和极点极线理论的入门实例
- **数学奥林匹克**：平面几何竞赛题中的常用结构和技巧

## 相关概念

- 垂心 (Orthocenter)：三角形三条高的交点
- 外心 (Circumcenter)：三角形外接圆的圆心
- 欧拉线 (Euler Line)：通过垂心、重心、外心的直线
- 中位三角形 (Medial Triangle)：由原三角形三边中点构成的三角形
- 费尔巴哈定理 (Feuerbach's Theorem)：九点圆与内切圆、旁切圆相切

## 参考

### 教材

- [H. S. M. Coxeter. Introduction to Geometry. Wiley, 2nd edition, 1969. Section 1.8]
- [R. Honsberger. Episodes in Nineteenth and Twentieth Century Euclidean Geometry. MAA, 1995. Chapter 2]

### 在线资源

- [Mathlib4 - Euclidean Triangle](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Euclidean/Triangle.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*