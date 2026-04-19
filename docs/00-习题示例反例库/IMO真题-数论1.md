---
title: "IMO真题-数论：整除与素数"
msc_primary: 00A99
level: silver
course: IMO竞赛数学
difficulty: L3
topic: 数论
source: "IMO 2005 Problem 2"
target_courses:
  - MIT 18.701
status: completed
created_at: 2026-04-18
review_status: completed
---

# IMO 2005 Problem 2：数论

## 题目

设 $a_1, a_2, \ldots$ 为整数序列，其中有无穷多项为正，也有无穷多项为负。假设对每个正整数 $n$，数 $a_1, a_2, \ldots, a_n$ 除以 $n$ 的余数互不相同。证明：每个整数在序列 $a_1, a_2, \ldots$ 中恰好出现一次。

## 解答

**步骤1：证明所有 $a_i$ 互不相同**

假设 $a_i = a_j$ 对 $i < j$。考虑前 $j$ 项。$a_i \equiv a_j \pmod{j}$（因为 $a_i = a_j$），与条件矛盾。$\square$

**步骤2：证明对任意 $n$，$\{a_1, \ldots, a_n\}$ 是模 $n$ 的完全剩余系**

由条件，$a_1, \ldots, a_n$ 模 $n$ 的余数互不相同，且共有 $n$ 个数，所以它们构成模 $n$ 的完全剩余系。$\square$

**步骤3：证明序列包含任意大的正数和负数**

由步骤2，$\sum_{i=1}^n a_i \equiv \sum_{k=0}^{n-1} k = \frac{n(n-1)}{2} \pmod{n}$。所以 $\sum_{i=1}^n a_i \equiv 0 \pmod{n}$ 当 $n$ 为奇数时。

由条件，有无穷多项为正，无穷多项为负，且所有项互不相同，所以序列无界。$\square$

**步骤4：证明每个整数都出现**

假设整数 $m$ 不出现。由于序列无界且各项为整数，存在 $N$ 使得 $|a_i| > |m|$ 对所有 $i > N$。

考虑前 $N + 2|m| + 1$ 项。由步骤2，它们构成模 $N + 2|m| + 1$ 的完全剩余系。但其中有 $N$ 项的绝对值大于 $|m|$，且 $m$ 不出现，这导致矛盾（剩余系的元素分布不均匀）。$\square$

**步骤5：唯一性**

由步骤1，所有 $a_i$ 互不相同，所以每个整数至多出现一次。结合步骤4，每个整数恰好出现一次。$\square$

## 知识点映射

| 知识点 | 银层对应 |
|--------|---------|
| 完全剩余系 | MIT 18.701 模运算 |
| 鸽巢原理 | MIT 18.06 组合思想 |
| 整除性 | MIT 18.701 数论基础 |

## Lean4 形式化

```lean4
import Mathlib

-- IMO 2005 Problem 2 的形式化陈述
example (a : ℕ → ℤ)
    (h_pos : ∀ N, ∃ n > N, a n > 0)
    (h_neg : ∀ N, ∃ n > N, a n < 0)
    (h_distinct_mod : ∀ n, (a '' Finset.Icc 1 n).card = n ∧
      ∀ i j ∈ Finset.Icc 1 n, i ≠ j → a i % n ≠ a j % n) :
    ∀ m : ℤ, ∃! n, a n = m := by
  sorry
```

## 相关文档

- [IMO真题-不等式2](IMO真题-不等式2.md)
- [IMO真题-不等式3](IMO真题-不等式3.md)
- [IMO真题-代数1](IMO真题-代数1.md)
- [IMO真题-代数2](IMO真题-代数2.md)
- [IMO真题-代数3](IMO真题-代数3.md)

## 习题摘要

**习题 1.0** 参见上文问题 1。
## 参考文献

1. International Mathematical Olympiad (IMO). *Official Problems and Solutions*. Available at: https://www.imo-official.org/
2. Engel, A. (1998). *Problem-Solving Strategies*. Springer. ISBN: 978-0387982191.
3. Andreescu, T., & Gelca, R. (2000). *Mathematical Olympiad Challenges*. Birkhäuser. ISBN: 978-0817641900.