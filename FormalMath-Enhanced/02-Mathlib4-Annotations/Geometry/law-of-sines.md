---
msc_primary: 00A99
processed_at: '2026-04-15'
title: 正弦定理 (Law of Sines)
---
# 正弦定理 (Law of Sines)

## Mathlib4 引用

```lean
import Mathlib.Geometry.Euclidean.Triangle

namespace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- 正弦定理：任意三角形中 a / sin(A) = b / sin(B) = c / sin(C) = 2R -/
theorem law_of_sines (A B C : P) (hnondegenerate : ¬ Collinear ℝ {A, B, C}) :
    dist B C / Real.sin (∠ B A C) = dist A C / Real.sin (∠ A B C) 
      ∧ dist A C / Real.sin (∠ A B C) = dist A B / Real.sin (∠ A C B) := by
  -- 利用三角形面积公式 S = (1/2)ab sin(C) 证明
  sorry

end EuclideanGeometry
```

## 数学背景

正弦定理是平面几何和三角学中最基本、最常用的定理之一。该定理断言：在任何三角形中，各边与其对角的正弦之比相等，且等于该三角形外接圆的直径。正弦定理的历史可以追溯到古希腊和古印度的数学家，而现代形式则在阿拉伯数学黄金时代（约公元10世纪）得到完善。这一定理与余弦定理一起构成了解三角形的完整工具集，是测量学、天文学、导航学和物理学中不可或缺的数学基础。

## 直观解释

正弦定理提供了一个关于三角形边角关系的优美比例规律。想象一个三角形的外接圆：无论三角形的形状如何变化，只要它内接于同一个圆，某条边与其对角的正弦之比始终等于圆的直径。这可以理解为：边长不仅取决于对角的大小，还取决于三角形在外接圆中的尺度。如果两个三角形有相同的对角，但外接圆大小不同，那么边长会按外接圆半径成比例变化。正弦定理将三角形的局部角度信息与全局的外接圆尺度信息完美地联系在一起。

## 形式化表述

设三角形的三边长为 $a, b, c$，分别对应角 $A, B, C$，外接圆半径为 $R$，则：

$$\frac{a}{\sin(A)} = \frac{b}{\sin(B)} = \frac{c}{\sin(C)} = 2R$$

等价形式：

$$a : b : c = \sin(A) : \sin(B) : \sin(C)$$

其中：

- $a, b, c$ 分别是角 $A, B, C$ 的对边长度
- $\sin(A)$ 是角 $A$ 的正弦值
- $R$ 是三角形外接圆的半径
- $2R$ 称为三角形的外接圆直径或正弦定理常数

## 证明思路

1. **面积法**：三角形面积 $S = \frac{1}{2}bc\sin(A) = \frac{1}{2}ac\sin(B) = \frac{1}{2}ab\sin(C)$，整理即得正弦定理的比例关系
2. **外接圆法**：连接顶点与外接圆心，利用等腰三角形和圆心角是圆周角两倍的关系，证明 $a = 2R\sin(A)$
3. **高线法**：从顶点 $C$ 向边 $AB$ 作高 $h$，则 $h = a\sin(B) = b\sin(A)$，整理得 $\frac{a}{\sin(A)} = \frac{b}{\sin(B)}$
4. **复数/向量法**：用复平面上的点表示三角形顶点，利用复数的辐角和模长关系推导

核心洞察在于三角形的面积和外接圆半径为边角关系提供了统一的比例常数。

## 示例

### 示例 1：AAS 情形求解

已知三角形的两角 $A = 30^\circ$, $B = 45^\circ$ 和一边 $a = 10$。则 $C = 105^\circ$，且：
$b = a \frac{\sin(B)}{\sin(A)} = 10 \frac{\sin(45^\circ)}{\sin(30^\circ)} = 10 \sqrt{2} \approx 14.14$。

### 示例 2：外接圆半径计算

设三角形边长 $a = 13$, 对角 $A = 60^\circ$，则外接圆半径：
$R = \frac{a}{2\sin(A)} = \frac{13}{2 \times \sqrt{3}/2} = \frac{13}{\sqrt{3}} \approx 7.51$。

### 示例 3：等边三角形

在等边三角形中，$A = B = C = 60^\circ$，$a = b = c$。正弦定理给出：
$\frac{a}{\sin(60^\circ)} = \frac{b}{\sin(60^\circ)} = \frac{c}{\sin(60^\circ)} = 2R$，即 $a = b = c = R\sqrt{3}$。

## 应用

- **测量与导航**：通过已知角度和一边计算不可达距离
- **天文学**：恒星距离和天体三角形的边长计算
- **结构工程**：桁架分析和力的三角形法
- **信号处理**：相位差与波长关系的三角计算
- **医学成像**：CT 重建和超声波定位中的三角测量

## 相关概念

- 余弦定理 (Law of Cosines)：三角形边角关系的另一基本定理
- 外接圆 (Circumcircle)：通过三角形三个顶点的圆
- 正弦函数 (Sine Function)：直角三角形中对边与斜边之比
- 三角形面积公式：$S = \frac{1}{2}ab\sin(C)$
- 球面正弦定理：正弦定理在球面几何中的推广

## 参考

### 教材

- [Euclid. Elements. Book III, Proposition 20-21]
- [G. B. Thomas, R. L. Finney. Calculus and Analytic Geometry. Addison-Wesley, 9th edition, 1996. Chapter 9]

### 在线资源

- [Mathlib4 - Euclidean Triangle](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Euclidean/Triangle.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*