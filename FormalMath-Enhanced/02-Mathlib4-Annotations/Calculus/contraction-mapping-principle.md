---
msc_primary: 00A99
processed_at: '2026-04-03'
title: 压缩映射原理 (Contraction Mapping Principle)
---
# 压缩映射原理 (Contraction Mapping Principle)

## Mathlib4 引用

```lean
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.SpecificLimits.Basic

namespace ContractionMapping

variable {X : Type*} [MetricSpace X] [CompleteSpace X]

/-- 压缩映射原理（Banach不动点定理的等价表述） -/
theorem contraction_mapping_principle (f : X → X) (q : ℝ) (hq : 0 ≤ q ∧ q < 1)
    (hf : LipschitzWith q f) :
    ∃! x, f x = x := by
  -- 构造迭代序列并证明收敛
  sorry

/-- 误差估计 -/
theorem contraction_error_estimate (f : X → X) (q : ℝ) (hq : 0 ≤ q ∧ q < 1)
    (hf : LipschitzWith q f) (x* : X) (hx* : f x* = x*) (n : ℕ) (x₀ : X) :
    dist (f^[n] x₀) x* ≤ q^n / (1 - q) * dist x₀ (f x₀) := by
  -- 几何级数估计
  sorry

/-- 先验误差估计 -/
theorem contraction_a_priori_estimate (f : X → X) (q : ℝ) (hq : 0 ≤ q ∧ q < 1)
    (hf : LipschitzWith q f) (x* : X) (hx* : f x* = x*) (n : ℕ) (x₀ : X) :
    dist (f^[n] x₀) x* ≤ q^n * dist x₀ x* := by
  -- 直接利用Lipschitz条件
  sorry

end ContractionMapping
```

## 数学背景

压缩映射原理（即Banach不动点定理）是现代分析学中最重要的不动点定理之一。它由波兰数学家Stefan Banach于1922年在其博士论文中提出，为度量空间中迭代方法的收敛性提供了完整的理论保证。这一定理在微分方程、数值分析、经济学和优化理论中具有核心地位。

## 直观解释

压缩映射原理告诉我们：**在完备空间中，任何"收缩"变换都必然将空间中的点逐步"挤压"到一个唯一的不动点**。想象一张橡胶膜上画着一个城市地图，如果你将地图不断向中心压缩（每个点都向中心移动，且移动距离按比例缩小），最终所有点都会汇聚到地图上的一个特定点——这就是不动点。

## 形式化表述

设 $(X, d)$ 是完备度量空间，映射 $f: X \to X$ 是**压缩映射**，即存在常数 $q \in [0, 1)$ 使得：

$$d(f(x), f(y)) \leq q \cdot d(x, y), \quad \forall x, y \in X$$

则：

1. **存在性**：$f$ 存在不动点 $x^* \in X$（即 $f(x^*) = x^*$）
2. **唯一性**：不动点是唯一的
3. **收敛性**：对任意初始点 $x_0 \in X$，迭代序列 $x_{n+1} = f(x_n)$ 收敛到 $x^*$
4. **误差估计**：$d(x_n, x^*) \leq \frac{q^n}{1-q} d(x_0, x_1)$

## 证明思路

1. **构造迭代序列**：任取 $x_0 \in X$，定义 $x_{n+1} = f(x_n)$
2. **证明Cauchy性**：
   - 利用压缩条件：$d(x_{n+1}, x_n) \leq q^n d(x_1, x_0)$
   - 几何级数估计：$d(x_m, x_n) \leq \frac{q^n}{1-q} d(x_1, x_0) \to 0$
3. **完备性保证收敛**：$x_n \to x^*$
4. **验证不动点**：由连续性 $f(x^*) = \lim f(x_n) = \lim x_{n+1} = x^*$
5. **唯一性证明**：假设 $x, y$ 都是不动点，则 $d(x,y) = d(f(x), f(y)) \leq q \cdot d(x,y)$，故 $d(x,y) = 0$

## 示例

### 示例 1：Newton迭代法

求解 $g(x) = 0$，迭代格式：$x_{n+1} = x_n - \frac{g(x_n)}{g'(x_n)}$

在根 $x^*$ 附近，若 $g'(x^*) \neq 0$，则迭代函数是局部压缩映射。

### 示例 2：Picard迭代（微分方程）

初值问题：$y' = F(t, y)$, $y(t_0) = y_0$

定义积分算子：$(Ty)(t) = y_0 + \int_{t_0}^t F(s, y(s)) ds$

在适当条件下，$T$ 是压缩映射，保证解的存在唯一性。

### 示例 3：隐函数求解

求解 $F(x, y) = 0$ 得到 $y = g(x)$。

固定 $x$，定义 $T_x(y) = y - c \cdot F(x, y)$，适当选择 $c$ 使 $T_x$ 成为压缩映射。

## 应用

- **常微分方程**：Picard-Lindelöf存在唯一性定理
- **偏微分方程**：变分问题的迭代求解
- **数值分析**：线性/非线性方程组的迭代法
- **经济学**：均衡价格的计算
- **机器学习**：某些优化算法的收敛性分析
- **图像处理**：分形压缩算法

## 相关概念

- [Banach不动点定理](./banach-fixed-point.md)：同一定理的不同命名
- Lipschitz连续性：压缩映射的条件
- 完备度量空间：定理成立的空间条件
- 迭代法收敛性：数值分析应用

## 参考

### 教材

- [Kreyszig. Introductory Functional Analysis with Applications. Wiley, 1978. Chapter 5]
- [Zeidler. Nonlinear Functional Analysis and Its Applications, Vol I. Springer, 1986]

### 历史文献

- [Banach. Sur les opérations dans les ensembles abstraits et leur application aux équations intégrales. Fundamenta Mathematicae, 3:133-181, 1922]

### 在线资源

- [Mathlib4 文档 - Contracting][https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/MetricSpace/Contracting.html](需更新)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
