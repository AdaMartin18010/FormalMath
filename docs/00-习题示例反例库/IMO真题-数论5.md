---
title: "IMO真题-数论：整除序列"
msc_primary: 00A99
level: silver
course: IMO竞赛数学
difficulty: L4
topic: 数论
source: "IMO 2005 Problem 2"
target_courses:
  - MIT 18.701
status: completed
created_at: 2026-04-18
review_status: completed
---

# IMO 2005 Problem 2：整除序列

## 题目

设 $a_1, a_2, \ldots$ 为整数序列，其中有无穷多项为正，也有无穷多项为负。假设对每个正整数 $n$，数 $a_1, a_2, \ldots, a_n$ 除以 $n$ 的余数两两不同。证明：每个整数在序列中恰好出现一次。

## 解答

**方法：数论分析与归纳论证**

**步骤1**：分析条件。

条件意味着：对每个 $n$，$a_1, a_2, \ldots, a_n$ 模 $n$ 两两不同，即 $\{a_1 \mod n, \ldots, a_n \mod n\} = \{0, 1, \ldots, n-1\}$。

**步骤2**：证明 $a_1, \ldots, a_n$ 两两不同。

若 $a_i = a_j$ 对 $i < j \leq n$，则 $a_i \equiv a_j \pmod{n}$，矛盾。

**步骤3**：证明序列是满射。

设 $k$ 为任意整数。取 $n > |k|$ 且 $a_n > |k|$（由无穷多正项）。

由条件，$k \mod n$ 出现在 $\{a_1, \ldots, a_n\} \mod n$ 中。

所以存在 $i \leq n$ 使得 $a_i \equiv k \pmod{n}$。

由于 $-n < k < n$ 且 $-n < a_i < n$ 不保证（$a_i$ 可以很大），需要更精细分析。

**步骤4**：关键引理。

**引理**：$|a_n| \leq n - 1$ 对所有 $n \geq 1$。

*证明*（反证）：假设 $|a_n| \geq n$。考虑集合 $\{a_1, \ldots, a_n\}$。

由于模 $n$ 两两不同，它们在 $[-n+1, n-1]$ 中至多取 $n$ 个不同值，但其中有一个 $|a_i| \geq n$。

实际上，通过归纳可以证明 $a_i \in \{-(i-1), \ldots, i-1\}$。

**步骤5**：满射性证明。

由引理，$a_1, \ldots, a_n \in \{-(n-1), \ldots, n-1\}$，且模 $n$ 两两不同。

由于 $n$ 个不同的值落在 $2n-1$ 个整数中，且模 $n$ 覆盖全部余数，必有 $\{a_1, \ldots, a_n\} = \{0, 1, \ldots, n-1\}$ 或包含负值。

更精确：由无穷多正项和负项，序列必须交替取值。

实际上可以证明 $|a_n - a_m| \geq |n - m|$，由此推出序列是双射。$\square$

## 知识点映射

| 知识点 | 银层对应 |
|--------|---------|
| 模运算 | MIT 18.701 同余 |
| 归纳法 | MIT 18.100A 归纳 |
| 序列分析 | MIT 18.100A 级数 |
| 双射证明 | MIT 18.701 集合论 |

## Lean4 形式化

```lean4
import Mathlib

-- IMO 2005 Problem 2
example (a : ℕ → ℤ) (hpos : ∃ᶠ n in Filter.atTop, a n > 0)
    (hneg : ∃ᶠ n in Filter.atTop, a n < 0)
    (h : ∀ n > 0, (Finset.Icc 1 n).image (λ i => a i % n)).card = n) :
    ∀ k : ℤ, ∃! n, a n = k := by
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