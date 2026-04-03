---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# Brouwer不动点定理（单位球版本）

## Mathlib4 引用

```lean
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Homotopy.Contractible

namespace BrouwerFixedPointBall

variable (n : ℕ)

/-- Brouwer不动点定理：单位球版本 -/
theorem brouwer_fixed_point_ball (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : Continuous f) (hfs : ∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ 1) :
    ∃ x, ‖x‖ ≤ 1 ∧ f x = x := by
  -- 单位闭球到自身的连续映射必有不动点
  sorry

/-- 单纯形版本 -/
theorem brouwer_fixed_point_simplex (f : StandardSimplex n → StandardSimplex n)
    (hf : Continuous f) :
    ∃ x ∈ StandardSimplex n, f x = x := by
  -- 标准单纯形同胚于球
  sorry

/-- 同胚不变性 -/
theorem brouwer_fixed_point_homeo {X : Type*} [TopologicalSpace X]
    (hX : Nonempty (Homeomorph (EuclideanSpace ℝ (Fin n)) X))
    (K : Set X) (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (f : X → X) (hf : ContinuousOn f K) (hfs : MapsTo f K K) :
    ∃ x ∈ K, f x = x := by
  -- 不动点性质在同胚下不变
  sorry

end BrouwerFixedPointBall
```

## 数学背景

Brouwer不动点定理是拓扑学中最著名和最基本的定理之一，由荷兰数学家L. E. J. Brouwer于1910年证明。单位球版本是该定理最经典的形式，它断言：任何将n维闭单位球连续映射到自身的函数必有不动点。这一定理在数学的多个分支以及经济学、博弈论等领域有广泛应用。

## 直观解释

想象一杯咖啡：无论你如何连续地搅拌（不泼出杯子，不撕裂液体），总有一点咖啡最终会回到原来的位置。这就是Brouwer不动点定理的直观含义——连续变换无法"打散"所有点。这一结果深刻揭示了拓扑空间的连续性约束。

## 形式化表述

设 $B^n = \{x \in \mathbb{R}^n : \|x\| \leq 1\}$ 是n维闭单位球，$f: B^n \to B^n$ 是连续映射，则：

$$\exists x \in B^n : f(x) = x$$

**等价形式**：任何紧致凸集到自身的连续映射都有不动点（Schauder推广）。

## 证明思路

### 代数拓扑证明：

1. **反证法**：假设 $f$ 无不动点
2. **构造收缩**：定义 $r: B^n \to S^{n-1}$ 为 $r(x) = x + t(x - f(x))$（射线投影到边界）
3. **同调矛盾**：导出 $H_{n-1}(S^{n-1}) \to H_{n-1}(B^n)$ 非零的矛盾
4. **结论**：假设不成立，存在不动点

### 组合证明（Sperner引理）：

1. **三角剖分**：对单纯形进行细三角剖分
2. **Sperner标记**：构造特殊顶点标记
3. **完全单形**：证明存在完全标记的单形
4. **极限论证**：通过极限过程得到不动点

## 示例

### 示例 1：一维情形

$f: [0, 1] \to [0, 1]$ 连续。

若 $f(0) > 0$ 且 $f(1) < 1$，设 $g(x) = f(x) - x$，则 $g(0) > 0$, $g(1) < 0$。

由介值定理，存在不动点。

### 示例 2：经济均衡

Arrow-Debreu一般均衡存在性证明使用Brouwer定理：

价格单纯形上，超额需求函数的"标准化"版本有不动点，对应均衡价格。

### 示例 3：博弈论（Nash均衡）

有限博弈中，最佳反应映射是连续的，策略单纯形到自身的映射。

由Brouwer定理，Nash均衡存在。

## 应用

- **经济学**：一般均衡存在性、博弈论
- **微分方程**：Peano存在性定理
- **动力系统**：周期轨道存在性
- **图论**：流网络、染色问题
- **泛函分析**：算子理论

## 相关概念

- [Brouwer不动点定理（一般形式）](../Topology/brouwer-fixed-point.md)：拓扑版本
- [紧致性 (Compactness)](./compactness.md)：定理的关键条件
- [凸集 (Convex Set)](./convex-set.md)：等价表述中的条件
- [Schauder不动点定理](./schauder-fixed-point.md)：无限维推广

## 参考

### 教材

- [Hatcher. Algebraic Topology. Cambridge, 2002. Chapter 2]
- [Border. Fixed Point Theorems with Applications to Economics. Cambridge, 1985]

### 历史文献

- [Brouwer. Über eineindeutige, stetige Transformationen von Flächen in sich. 1910]

### 在线资源

- [Mathlib4 文档 - Fixed Point](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/FixedPoint.html)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
