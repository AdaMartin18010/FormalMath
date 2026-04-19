---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: Banach不动点定理 (Banach Fixed-Point Theorem)
---
# Banach不动点定理 (Banach Fixed-Point Theorem)

## Mathlib4 引用

```lean
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.SpecificLimits.Basic

namespace BanachFixedPoint

variable {X : Type*} [MetricSpace X] [CompleteSpace X]

/-- Banach不动点定理（压缩映射原理） -/
theorem banach_fixed_point (f : X → X) (q : ℝ) (hq : 0 ≤ q ∧ q < 1)
    (hf : ∀ x y, dist (f x) (f y) ≤ q * dist x y) :
    ∃! x, f x = x := by
  -- 构造迭代序列并证明收敛到不动点
  sorry

/-- 迭代收敛速度估计 -/
theorem fixed_point_iteration_rate (f : X → X) (q : ℝ) (hq : 0 ≤ q ∧ q < 1)
    (hf : ∀ x y, dist (f x) (f y) ≤ q * dist x y)
    (x₀ : X) (x* : X) (hx* : f x* = x*) (n : ℕ) :
    dist (f^[n] x₀) x* ≤ q^n / (1 - q) * dist (f x₀) x₀ := by
  -- 几何级数估计
  sorry

end BanachFixedPoint
```

## 数学背景

Banach不动点定理由波兰数学家斯特凡·巴拿赫（Stefan Banach）于1922年提出，也被称为压缩映射原理。这是完备度量空间理论中最基本的结果之一，为迭代方法的收敛性提供了理论基础，在微分方程、数值分析和经济学中有广泛应用。

## 直观解释

Banach定理告诉我们：**将一个空间"压缩"到自身的映射必有唯一不动点**。想象用地图定位：如果每次查看地图都让你更接近目标（压缩），那么最终会到达一个点，地图上的位置与实际位置重合（不动点）。

## 形式化表述

设 $(X, d)$ 是完备度量空间，$f: X \to X$ 是压缩映射，即存在 $q \in [0, 1)$ 使得：

$$d(f(x), f(y)) \leq q \cdot d(x, y), \quad \forall x, y \in X$$

则：

1. $f$ 有唯一不动点 $x^* \in X$（即 $f(x^*) = x^*$）
2. 对任意 $x_0 \in X$，迭代序列 $x_{n+1} = f(x_n)$ 收敛到 $x^*$
3. 误差估计：$d(x_n, x^*) \leq \frac{q^n}{1-q} d(x_1, x_0)$

## 证明思路

1. **构造迭代序列**：任取 $x_0$，定义 $x_{n+1} = f(x_n)$
2. **证明Cauchy列**：利用压缩条件证明 $d(x_n, x_m) \to 0$
3. **完备性保证收敛**：$x_n \to x^*$
4. **验证不动点**：$f(x^*) = x^*$（由连续性）
5. **唯一性**：假设两个不动点，导出矛盾

## 示例

### 示例 1：Newton法

求 $g(x) = 0$ 的根，迭代 $f(x) = x - g(x)/g'(x)$。

在根附近，$f$ 是压缩映射。

### 示例 2：Picard迭代

解初值问题 $y' = F(t, y)$，$y(t_0) = y_0$。

定义 $f(y)(t) = y_0 + \int_{t_0}^t F(s, y(s)) ds$。

在适当条件下是压缩映射。

## 应用

- **微分方程**：Picard存在唯一性定理
- **数值分析**：迭代法的收敛性
- **经济学**：均衡存在性
- **图像处理**：分形压缩
- **机器学习**：某些优化算法的收敛性

## 相关概念

- [完备度量空间](./complete-metric-space.md)：定理成立的空间条件
- 压缩映射：Lipschitz常数小于1的映射
- Lipschitz连续性：更强的连续性条件
- [Brouwer不动点定理](../Topology/brouwer-fixed-point.md)：拓扑学版本

## 参考

### 教材

- [Kreyszig. Introductory Functional Analysis with Applications. Wiley, 1978. Chapter 5]
- [Conway. A Course in Functional Analysis. Springer, 1990. Chapter 1]

### 历史文献

- [Banach. Sur les opérations dans les ensembles abstraits et leur application aux équations intégrales. 1922]

### 在线资源

- [Mathlib4 文档 - Contracting][https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/MetricSpace/Contracting.html](需更新)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
