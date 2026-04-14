---
msc_primary: 00A99
processed_at: '2026-04-15'
title: 余弦定理 (Law of Cosines)
---
# 余弦定理 (Law of Cosines)

## Mathlib4 引用

```lean
import Mathlib.Geometry.Euclidean.Triangle

namespace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- 余弦定理：任意三角形中 c² = a² + b² - 2ab cos(C) -/
theorem law_of_cosines (A B C : P) :
    dist A B ^ 2 = dist A C ^ 2 + dist B C ^ 2 - 2 * dist A C * dist B C * Real.cos (∠ A C B) := by
  -- 利用向量分解和内积定义证明
  sorry

end EuclideanGeometry
```

## 数学背景

余弦定理是平面几何和三角学中的核心结果，它将勾股定理从直角三角形推广到任意三角形。该定理最早出现在欧几里得的《几何原本》第二卷（命题12和13）中，但现代形式的余弦定理是由波斯数学家阿尔·卡西（al-Kashi）在15世纪系统发展的，因此在中东地区常被称为 al-Kashi 定理。余弦定理是测量学、航海学、天文学和物理学中计算未知边长和角度的基本工具。

## 直观解释

余弦定理可以理解为勾股定理的修正版。勾股定理说：在直角三角形中，$c^2 = a^2 + b^2$。但当三角形的角 $C$ 不是直角时，这个等式就不成立了。余弦定理告诉我们需要减去（或加上）一个修正项 $2ab \cos(C)$：当角 $C$ 是锐角时，$\cos(C) > 0$，所以 $c^2 < a^2 + b^2$；当角 $C$ 是钝角时，$\cos(C) < 0$，所以 $c^2 > a^2 + b^2$；当角 $C$ 恰好是直角时，$\cos(C) = 0$，余弦定理就退化回勾股定理。这个公式完美地统一了所有三角形的情形。

## 形式化表述

设三角形的三边长为 $a, b, c$，分别对应角 $A, B, C$，则：

$$c^2 = a^2 + b^2 - 2ab \cos(C)$$

对称地：

$$a^2 = b^2 + c^2 - 2bc \cos(A)$$
$$b^2 = a^2 + c^2 - 2ac \cos(B)$$

向量形式：对任意向量 $u, v$：

$$||u - v||^2 = ||u||^2 + ||v||^2 - 2\langle u, v \rangle$$

其中：

- $a, b, c$ 分别是角 $A, B, C$ 的对边长度
- $\cos(C)$ 是角 $C$ 的余弦值
- 当 $C = 90^\circ$ 时，$\cos(C) = 0$，定理退化为勾股定理

## 证明思路

1. **向量法**：设 $\vec{c} = \vec{a} - \vec{b}$，则 $c^2 = ||\vec{a} - \vec{b}||^2 = ||\vec{a}||^2 + ||\vec{b}||^2 - 2\langle \vec{a}, \vec{b} \rangle = a^2 + b^2 - 2ab\cos(C)$
2. **坐标法**：将顶点 $C$ 放在原点，$A$ 放在 $(b, 0)$，$B$ 放在 $(a\cos(C), a\sin(C))$，用距离公式计算 $c^2$
3. **高线法**：从顶点 $B$ 向边 $AC$ 作高线，分两种情况（垂足在 $AC$ 内部或延长线上），分别用勾股定理推导
4. **复数法**：用复数表示三角形的顶点，利用 $|z_1 - z_2|^2 = (z_1 - z_2)(\bar{z}_1 - \bar{z}_2)$ 展开

核心洞察在于内积与夹角余弦的内在联系。

## 示例

### 示例 1：SAS 情形求第三边

已知三角形的两边 $a = 5$, $b = 7$，夹角 $C = 60^\circ$，则：
$c^2 = 25 + 49 - 2 \times 5 \times 7 \times 0.5 = 74 - 35 = 39$，故 $c = \sqrt{39} \approx 6.24$。

### 示例 2：钝角三角形

设 $a = 3$, $b = 4$, $C = 120^\circ$，则：
$c^2 = 9 + 16 - 2 \times 3 \times 4 \times (-0.5) = 25 + 12 = 37$，故 $c = \sqrt{37} > 5$。
这说明钝角三角形中对边大于勾股定理的预测。

### 示例 3：已知三边求角

设三角形三边为 $a = 2$, $b = 3$, $c = 4$，则：
$\cos(C) = (4 + 9 - 16)/(2 \times 2 \times 3) = -3/12 = -0.25$，故 $C \approx 104.5^\circ$。

## 应用

- **测量与测绘**：不可直接测量的距离和角度的间接计算
- **航海与天文学**：球面三角学中边长关系的计算基础
- **物理学**：力的合成与分解、功的计算（$W = Fd\cos\theta$）
- **机器学习**：向量相似度计算（余弦相似度）的几何基础
- **计算机图形学**：三维变换中角度和距离的精确计算

## 相关概念

- 勾股定理 (Pythagorean Theorem)：余弦定理在直角时的特例
- 正弦定理 (Law of Sines)：三角形边角关系的另一基本定理
- 内积 (Inner Product)：$\langle u, v \rangle = ||u|| ||v|| \cos\theta$
- 余弦相似度 (Cosine Similarity)：机器学习中的角度度量
- 海伦公式 (Heron's Formula)：由三边计算三角形面积

## 参考

### 教材

- [Euclid. Elements. Book II, Propositions 12-13]
- [G. B. Thomas, R. L. Finney. Calculus and Analytic Geometry. Addison-Wesley, 9th edition, 1996. Chapter 9]

### 在线资源

- [Mathlib4 - Euclidean Triangle](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Euclidean/Triangle.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*