---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: 鸽巢原理 (Pigeonhole Principle)
---
# 鸽巢原理 (Pigeonhole Principle)

## Mathlib4 引用

```lean
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Basic

namespace PigeonholePrinciple

/-- 基本鸽巢原理 -/
theorem pigeonhole_principle {α β : Type*} [Finite β] (f : α → β)
    (h : Fintype.card α > Fintype.card β) :
    ∃ y : β, 2 ≤ Fintype.card (f ⁻¹' {y}) := by
  -- 若元素多于容器，必有容器含至少两个元素
  sorry

/-- 推广的鸽巢原理 -/
theorem generalized_pigeonhole {α β : Type*} [Finite β] (f : α → β) (k : ℕ)
    (h : Fintype.card α > k * Fintype.card β) :
    ∃ y : β, k + 1 ≤ Fintype.card (f ⁻¹' {y}) := by
  -- 必有容器含至少k+1个元素
  sorry

/-- 无限版本 -/
theorem infinite_pigeonhole {α β : Type*} [Infinite α] [Finite β] (f : α → β) :
    ∃ y : β, Infinite (f ⁻¹' {y}) := by
  -- 无限集映射到有限集，某原像无限
  sorry

end PigeonholePrinciple
```

## 数学背景

鸽巢原理（Dirichlet原理或抽屉原理）是组合数学中最简单却最强大的原理之一。它以德国数学家Peter Gustav Lejeune Dirichlet命名，他在1834年明确表述了这一原理。尽管形式简单（若鸽子多于鸽巢，则必有鸽巢含有多只鸽子），但它蕴含了丰富的数学内容，在数论、图论和计算机科学中有广泛应用。

## 直观解释

鸽巢原理告诉我们：**如果你有更多的物品要放入较少的容器中，那么至少有一个容器必须包含多个物品**。这就像把10封信投入9个信箱，无论如何投递，至少有一个信箱会收到至少两封信。这一"显然"的事实却有深刻而有力的推论。

## 形式化表述

**基本形式**：若将 $n$ 个物体放入 $m$ 个盒子，且 $n > m$，则至少有一个盒子包含至少两个物体。

**推广形式**：若将 $n$ 个物体放入 $m$ 个盒子，且 $n > k \cdot m$，则至少有一个盒子包含至少 $k+1$ 个物体。

**平均值形式**：若 $n$ 个物体放入 $m$ 个盒子，则某个盒子至少含有 $\lceil n/m \rceil$ 个物体。

## 证明思路

1. **反证法**：假设每个盒子最多有1个（或k个）物体
2. **计数**：则总物体数不超过 $m$（或 $k \cdot m$）
3. **矛盾**：与条件 $n > m$（或 $n > k \cdot m$）矛盾
4. **结论**：假设不成立

## 示例

### 示例 1：生日问题

366个人中，必有至少两人同一天生日。

（盒子=365天，鸽子=366人）

### 示例 2：Ramsey型结果

6个人中，必有3人互相认识或3人互不认识。

（将完全图 $K_6$ 的边2-染色，必有单色三角形）

### 示例 3：数论应用

从 $\{1, 2, ..., 2n\}$ 中选取 $n+1$ 个数，必有两数满足一个整除另一个。

（利用2-adic赋值，映射到奇数）

## 应用

- **数论**：Diophantine逼近、同余方程
- **图论**：Ramsey理论、染色问题
- **计算机科学**：哈希冲突、负载均衡
- **几何**：格点问题、覆盖问题
- **组合优化**：存在性证明

## 相关概念

- [Ramsey定理](./ramsey-theorem.md)：鸽巢原理的图论推广
- [Erdős–Szekeres定理](./erdos-szekeres-theorem.md)：单调子序列存在性
- Dirichlet逼近定理：数论应用
- Erdős–Ginzburg–Ziv定理：零和子序列

## 参考

### 教材

- [van Lint & Wilson. A Course in Combinatorics. Cambridge, 2nd edition, 2001. Chapter 1]
- [Brualdi. Introductory Combinatorics. Pearson, 5th edition, 2009. Chapter 3]

### 在线资源

- [Mathlib4 文档 - Pigeonhole][https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Pigeonhole.html](需更新)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
