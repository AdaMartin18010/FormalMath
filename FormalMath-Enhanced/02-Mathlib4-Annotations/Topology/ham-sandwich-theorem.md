---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: 火腿三明治定理 (Ham Sandwich Theorem)
---
# 火腿三明治定理 (Ham Sandwich Theorem)

## Mathlib4 引用

```lean
import Mathlib.MeasureTheory.Measure.Haar

namespace MeasureTheory

variable {n : ℕ} {μ : Fin n → Measure (ℝ^n)}

/-- Ham Sandwich 定理：R^n 中 n 个有限测度集可被同一个超平面平分 -/
theorem ham_sandwich (hμ : ∀ i, (μ i).IsFiniteMeasure)
    (hopen : ∀ i, (μ i).IsOpenPosMeasure) :
    ∃ (v : ℝ^n) (c : ℝ), ‖v‖ = 1 ∧
      ∀ i, (μ i) {x | ⟪v, x⟫_ℝ > c} = (μ i) {x | ⟪v, x⟫_ℝ < c} := by
  -- 利用 Borsuk-Ulam 定理证明存在性
  sorry

end MeasureTheory
```

## 数学背景

火腿三明治定理是测度论和组合几何中的一个著名结果，通常归功于数学家亚瑟·斯通（Arthur Stone）和约翰·图基（John Tukey）于1942年。该定理断言：在 n 维欧氏空间中，给定 n 个具有有限测度的物体，总存在一个 (n-1) 维超平面能够同时将这 n 个物体的体积平分。定理的名字来源于一个直观的二维情形：给定两片面包和一块火腿（三个二维物体），总存在一条直线可以同时将三者切成面积相等的两半。

## 直观解释

火腿三明治定理是生活中公平分割问题的数学保证。想象你要把一份由面包、火腿和奶酪组成的三明治公平地切成两半，使每一半都含有相同量的面包、火腿和奶酪。定理告诉我们：无论你如何随意地堆放这些食材，总存在一种切割方式可以完美地实现这一点。在更高维度中，如果你有 n 种不同的食材散落在 n 维空间中，总存在一个 (n-1) 维的刀面可以将它们同时平分。

## 形式化表述

设 μ_1, μ_2, \dots, μ_n 是 R^n 上的 n 个有限 Borel 测度，则存在一个单位向量 v \in R^n 和一个实数 c \in R，使得超平面：

$$H = \{x \in R^n : \langle v, x \rangle = c\}$$

同时平分所有 n 个测度，即对每个 i = 1, 2, \dots, n：

$$μ_i(\{x : \langle v, x \rangle > c\}) = μ_i(\{x : \langle v, x \rangle < c\})$$

其中：

- v 是超平面的法向量，||v|| = 1
- c 决定超平面的位置
- \langle v, x \rangle = c 是超平面的方程
- 测度集中在超平面上的部分不影响等式（通常假设为零测度）

## 证明思路

1. **构型空间**：考虑所有可能的定向超平面，其参数空间可以等同于 S^n（通过齐次坐标或法向量-截距对）
2. ** signed 测度映射**：定义映射 f: S^n → R^n，其中 f_i(v, c) 表示第 i 个测度在超平面某一侧的净超出量
3. **连续性**：在适当条件下，f 是连续映射
4. **应用 Borsuk-Ulam**：由 Borsuk-Ulam 定理，存在 (v, c) 和 (-v, -c)（即同一个超平面的两侧参数化）使得 f(v, c) = f(-v, -c)，这意味着超平面平分了所有测度

核心洞察在于超平面的对径参数化与 Borsuk-Ulam 定理的完美契合。

## 示例

### 示例 1：二维火腿三明治

在平面上给定两块面包片和一块火腿（三个区域）。定理保证存在一条直线同时将它们三者的面积平分。这就是定理名称的由来。

### 示例 2：三维鸡蛋

在三维空间中给定一个鸡蛋（蛋黄和蛋白两部分）。存在一个平面同时将蛋黄和蛋白的体积平分。这是 n=2 时定理的应用。

### 示例 3：点集的公平分割

平面上有红、蓝两种颜色的点各 2n 个。Ham Sandwich 定理保证存在一条直线使得直线两侧的红点数和蓝点数都恰好为 n。这在计算几何和组合学中有重要应用。

## 应用

- **公平分割理论**：经济学中的蛋糕分割和社会选择问题
- **计算几何**：超平面分割和平衡分区的算法设计
- **统计学**：中位数和高维数据的分割方法
- **政治地理学**：选区划分中的公平性分析
- **机器人学**：多目标路径规划和资源分配

## 相关概念

- Borsuk-Ulam 定理 (Borsuk-Ulam Theorem)：Ham Sandwich 定理的拓扑基础
- 超平面 (Hyperplane)：n 维空间中的 (n-1) 维仿射子空间
- 测度 (Measure)：数学上推广长度、面积、体积的概念
- 公平分割 (Fair Division)：将资源分配给多个参与者的理论
- 计算几何 (Computational Geometry)：研究几何对象算法的学科

## 参考

### 教材

- [J. Matoušek. Using the Borsuk-Ulam Theorem. Springer, 2003. Chapter 3]
- [H. Edelsbrunner. Algorithms in Combinatorial Geometry. Springer, 1987. Chapter 7]

### 在线资源

- [Mathlib4 - Haar Measure](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Haar.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*