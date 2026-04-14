---
msc_primary: 00A99
processed_at: '2026-04-03'
title: Erdős–Szekeres定理 (Erdős–Szekeres Theorem)
---
# Erdős–Szekeres定理 (Erdős–Szekeres Theorem)

## Mathlib4 引用

```lean
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Sort

namespace ErdosSzekeres

/-- Erdős–Szekeres定理：单调子序列 -/
theorem erdos_szekeres_monotone {α : Type*} [LinearOrder α] (n : ℕ)
    (s : List α) (hs : s.length ≥ n^2 + 1) :
    ∃ t : List α, t <+ s ∧ (t.StrictMonotone ∨ t.StrictAntiMonotone) ∧ t.length = n + 1 := by
  -- 利用鸽巢原理和对称构造
  sorry

/-- Erdős–Szekeres定理：凸多边形 -/
theorem erdos_szekeres_convex (n : ℕ) :
    ∃ N : ℕ, ∀ (S : Finset (ℝ × ℝ)),
      S.card ≥ N → InGeneralPosition S →
      ∃ T : Finset (ℝ × ℝ), T ⊆ S ∧ T.card = n ∧ ConvexPosition T := by
  -- 点集中必存在凸n边形
  sorry

/-- 具体上界 -/
theorem erdos_szekeres_bound (n : ℕ) :
    erdosSzekeresNumber n ≤ Nat.choose (2*n - 4) (n - 2) + 1 := by
  -- 组合上界
  sorry

end ErdosSzekeres
```

## 数学背景

Erdős–Szekeres定理由匈牙利数学家Paul Erdős和George Szekeres于1935年证明，是Ramsey理论在几何和序列问题中的早期重要结果。该定理有两个经典形式：（1）任何足够长的实数序列必含长单调子序列；（2）平面上任何足够大的处于一般位置的点集必含大凸多边形。这一定理开创了组合几何的研究。

## 直观解释

Erdős–Szekeres定理告诉我们：**混沌中必然存在秩序**。想象随机放置一堆点，只要数量足够多，就一定能从中挑出若干点形成一个凸多边形。同样，任意混乱的数字序列中，必有长递增或长递减的子序列。这是"完全无序不可能"的又一体现。

## 形式化表述

**单调子序列版本**：

任何 $n^2 + 1$ 个不同实数的序列必含长度为 $n+1$ 的递增子序列或长度为 $n+1$ 的递减子序列。

即 $ES(n) \leq n^2 + 1$。

**凸多边形版本**：

对任意 $n \geq 3$，存在最小整数 $N(n)$ 使得：平面上任何 $N(n)$ 个处于一般位置（无三点共线）的点中，必有 $n$ 个点构成凸 $n$ 边形的顶点。

## 证明思路

### 单调子序列证明：

1. **序列配对**：对每个元素，记录以它结尾的最长递增子序列长度 $a_i$ 和最长递减子序列长度 $b_i$
2. **映射单射**：$(a_i, b_i)$ 对互不相同
3. **鸽巢原理**：若所有 $a_i, b_i \leq n$，则最多 $n^2$ 个不同对
4. **矛盾**：$n^2 + 1$ 个元素必有一个对超出范围

### 凸多边形证明：

利用Ramsey理论和组合几何论证。

## 示例

### 示例 1：序列 3, 1, 4, 1, 5, 9, 2, 6

长度为8（$> 2^2 + 1 = 5$），必含长度为3的单调子序列。

递增：1, 4, 5 或 1, 5, 6 或 1, 2, 6

递减：3, 1, 1（非严格）或 5, 2（不足）

### 示例 2：凸位置点集

平面上5个一般位置的点，必有4个构成凸四边形。

## 应用

- **计算几何**：凸包算法、点集分析
- **序理论**：偏序集的链和反链
- **随机序列**：随机排列的性质
- **极值组合**：极值问题的界限
- **图论**：路径和圈的存在性

## 相关概念

- [Ramsey定理](./ramsey-theorem.md)：理论基础
- Dilworth定理：偏序集分解
- [鸽巢原理](./pigeonhole-principle.md)：证明工具
- 凸包：计算几何概念

## 参考

### 教材

- [Matoušek. Lectures on Discrete Geometry. Springer, 2002. Chapter 3]
- [Steele. Probability Theory and Combinatorial Optimization. SIAM, 1997]

### 历史文献

- [Erdős & Szekeres. A combinatorial problem in geometry. 1935]

### 在线资源

- [Mathlib4 文档 - List][https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/List/Basic.html](需更新)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
