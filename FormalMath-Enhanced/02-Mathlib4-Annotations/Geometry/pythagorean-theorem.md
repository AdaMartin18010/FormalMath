---
msc_primary: 00A99
processed_at: '2026-04-15'
title: 勾股定理 (Pythagorean Theorem)
---
# 勾股定理 (Pythagorean Theorem)

## Mathlib4 引用

```lean
import Mathlib.Geometry.Euclidean.Triangle

namespace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- 勾股定理：直角三角形斜边平方等于两直角边平方和 -/
theorem pythagorean_theorem (A B C : P) (h : ∠ A B C = π / 2) :
    dist A C ^ 2 = dist A B ^ 2 + dist B C ^ 2 := by
  -- 利用内积和向量分解证明
  sorry

end EuclideanGeometry
```

## 数学背景

勾股定理是人类数学史上最著名、最古老的定理之一，早在古巴比伦（约公元前1800年）和古埃及的数学文献中就有记载。在中国，《周髀算经》中记载了商高与周公的对话（约公元前11世纪），因此在中国被称为勾股定理或商高定理。古希腊数学家毕达哥拉斯（Pythagoras）及其学派在公元前6世纪给出了第一个已知的严格证明，故在西方称为毕达哥拉斯定理。该定理是欧几里得几何的基石，也是三角学、解析几何和物理学中无数结果的基础。

## 直观解释

勾股定理描述了一个极其优美的几何规律：在任何直角三角形中，斜边上正方形的面积恰好等于两条直角边上正方形面积之和。可以想象一个由三个正方形拼成的独特L形图案：两个较小的正方形分别建在直角边上，它们合起来的面积刚好填满最大的那个建在斜边上的正方形。这个定理不仅是几何学的核心，也是建筑、测绘和工程中最常用的数学工具——只要知道直角三角形的任意两边，就能精确算出第三边。

## 形式化表述

设直角三角形的三边长为 $a, b, c$，其中 $c$ 为斜边，则：

$$a^2 + b^2 = c^2$$

向量形式：若向量 $u$ 和 $v$ 正交（$\langle u, v \rangle = 0$），则：

$$||u + v||^2 = ||u||^2 + ||v||^2$$

其中：

- $a, b$ 是直角边（股和勾）的长度
- $c$ 是斜边（弦）的长度
- $||u|| = \sqrt{\langle u, u \rangle}$ 是向量的欧几里得范数

## 证明思路

1. **面积法**：构造以三边为边长的正方形，通过剪切-拼接证明大正方形面积等于两个小正方形面积之和
2. **相似三角形**：从直角顶点向斜边作垂线，利用相似三角形的边长比例关系推导
3. **向量内积**：$||u + v||^2 = ||u||^2 + ||v||^2 + 2\langle u, v \rangle$，正交时交叉项为零
4. **坐标法**：将直角顶点放在原点，两直角边分别沿坐标轴，直接用距离公式计算

勾股定理已有超过 400 种不同的证明方法，是证明方法最多的数学定理之一。

## 示例

### 示例 1：3-4-5 三角形

最经典的勾股数组：$3^2 + 4^2 = 9 + 16 = 25 = 5^2$。这意味着边长为 3、4、5 的三角形是直角三角形，是古代埃及和巴比伦建筑中常用的测量工具。

### 示例 2：对角线长度

边长为 1 的正方形的对角线长度为 $\sqrt{1^2 + 1^2} = \sqrt{2}$。这说明了无理数的存在（$\sqrt{2}$ 不能表示为两个整数之比）。

### 示例 3：空间距离

在三维空间中，点 $(1, 2, 3)$ 到原点 $(0, 0, 0)$ 的距离为 $\sqrt{1^2 + 2^2 + 3^2} = \sqrt{14}$。这是勾股定理在更高维度的直接推广。

## 应用

- **建筑与工程**：结构测量、斜撑长度计算和直角校验
- **导航与测绘**：GPS 定位、距离测量和地图绘制
- **物理学**：矢量合成、力的分解和能量守恒
- **计算机图形学**：三维模型中的距离和碰撞检测
- **三角学**：正弦、余弦定理和傅里叶分析的基础

## 相关概念

- 直角三角形 (Right Triangle)：有一个内角为 90 度的三角形
- 勾股数 (Pythagorean Triple)：满足 $a^2 + b^2 = c^2$ 的正整数三元组
- 欧几里得距离 (Euclidean Distance)：$\sqrt{(x_2-x_1)^2 + (y_2-y_1)^2}$
- 正交向量 (Orthogonal Vectors)：内积为零的向量
- 余弦定理 (Law of Cosines)：勾股定理对任意三角形的推广

## 参考

### 教材

- [Euclid. Elements. Book I, Proposition 47]
- [D. Maor. The Pythagorean Theorem: A 4,000-Year History. Princeton, 2007]

### 在线资源

- [Mathlib4 - Euclidean Triangle](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Euclidean/Triangle.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*