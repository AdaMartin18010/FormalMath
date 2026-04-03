---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# 容斥原理 (Inclusion-Exclusion Principle)

## Mathlib4 引用

```lean
import Mathlib.Combinatorics.SetFamily.InclusionExclusion
import Mathlib.Data.Finset.Basic

namespace InclusionExclusion

/-- 容斥原理 - finite set版本 -/
theorem inclusion_exclusion {α : Type*} [Fintype α] (s : Finset (Finset α)) :
    Fintype.card (⋃ t ∈ s, t) = ∑ t ∈ s.powerset, (-1 : ℤ)^(Fintype.card t + 1) *
      Fintype.card (⋂ u ∈ t, u) := by
  -- 通过Möbius反演证明
  sorry

/-- 两个集合的容斥 -/
theorem inclusion_exclusion_two (A B : Set α) [Finite A] [Finite B] :
    Nat.card (A ∪ B) = Nat.card A + Nat.card B - Nat.card (A ∩ B) := by
  -- 直接计数
  sorry

/-- 概率版本 -/
theorem inclusion_exclusion_probability {Ω : Type*} [MeasureSpace Ω] (A : Finset (Set Ω))
    (hA : ∀ a ∈ A, MeasurableSet a) :
    measureOf (⋃ a ∈ A, a) = ∑ t ∈ A.powerset, (-1 : ℝ)^(Fintype.card t + 1) *
      measureOf (⋂ a ∈ t, a) := by
  -- 测度论版本
  sorry

end InclusionExclusion
```

## 数学背景

容斥原理是组合计数中的基本工具，其思想可以追溯到18世纪的数学家。它系统地纠正了直接计数并集时产生的重复计算问题。这一原理与Möbius反演、生成函数等技术密切相关，在组合数学、概率论和数论中都有重要应用。

## 直观解释

容斥原理告诉我们：**要计算多个集合的并集大小，先简单相加各集合大小，然后减去两两交集（因为重复计算了），再加回三重交集（因为减多了），如此交替进行**。这就像画维恩图时，要确保每个区域恰好被计数一次。

## 形式化表述

对于有限集合 $A_1, A_2, ..., A_n$：

$$\left|\bigcup_{i=1}^n A_i\right| = \sum_{k=1}^n (-1)^{k+1} \sum_{1 \leq i_1 < ... < i_k \leq n} |A_{i_1} \cap ... \cap A_{i_k}|$$

**展开形式**：
$$|A \cup B| = |A| + |B| - |A \cap B|$$

$$|A \cup B \cup C| = |A| + |B| + |C| - |A \cap B| - |B \cap C| - |C \cap A| + |A \cap B \cap C|$$

## 证明思路

1. **元素贡献法**：证明每个元素对右边的贡献恰好为1（若在并集中）或0（若不在）
2. **Möbius反演**：在子集格上应用Möbius反演公式
3. **指示函数**：利用 $\mathbf{1}_{A \cup B} = 1 - (1-\mathbf{1}_A)(1-\mathbf{1}_B)$ 展开
4. **归纳法**：对集合个数进行归纳

## 示例

### 示例 1：错位排列（derangement）

n个元素的排列中，没有不动点的排列数：

$$D_n = n! \sum_{k=0}^n \frac{(-1)^k}{k!} \approx \frac{n!}{e}$$

### 示例 2：Euler's Totient函数

$$\varphi(n) = n \prod_{p|n} \left(1 - \frac{1}{p}\right)$$

通过容斥计算与 $n$ 互素的数的个数。

### 示例 3：命中概率

将 $n$ 个球随机投入 $n$ 个盒子，每个盒子至少一个球的概率：

$$P = \sum_{k=0}^n (-1)^k \binom{n}{k} \left(1 - \frac{k}{n}\right)^n$$

## 应用

- **计数问题**：错位排列、受限位置排列
- **数论**：Euler's totient函数、素数计数
- **概率论**：并集概率、命中问题
- **图论**：染色计数、匹配计数
- **算法分析**：冲突解决、负载均衡

## 相关概念

- [Möbius反演](./mobius-inversion.md)：偏序集上的反演技术
- [生成函数](./generating-function.md)：计数的代数方法
- [错位排列](./derangement.md)：无不动点排列
- [Euler's totient函数](./euler-totient.md)：数论函数

## 参考

### 教材

- [Stanley. Enumerative Combinatorics, Vol 1. Cambridge, 2nd edition, 2012. Chapter 2]
- [van Lint & Wilson. A Course in Combinatorics. Cambridge, 2001. Chapter 10]

### 在线资源

- [Mathlib4 文档 - Inclusion Exclusion](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SetFamily/InclusionExclusion.html)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
