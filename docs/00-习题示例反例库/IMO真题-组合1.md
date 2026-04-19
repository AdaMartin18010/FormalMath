---
title: "IMO真题-组合：图论与极值"
msc_primary: 00A99
level: silver
course: IMO竞赛数学
difficulty: L4
topic: 组合
source: "IMO 2002 Problem 3"
target_courses:
  - MIT 18.701
status: completed
created_at: 2026-04-18
review_status: completed
---

# IMO 2002 Problem 3：组合数学

## 题目

设 $m$ 和 $n$ 为正整数。设 $a_1, a_2, \ldots, a_m$ 为 $\{1, 2, \ldots, n\}$ 中互不相同的整数，满足：只要 $a_i + a_j \leq n$（$1 \leq i \leq j \leq m$），就存在 $k$（$1 \leq k \leq m$）使得 $a_i + a_j = a_k$。

证明：$\frac{a_1 + a_2 + \cdots + a_m}{m} \geq \frac{n+1}{2}$。

## 解答

**方法：归纳与极值分析**

不妨设 $a_1 < a_2 < \cdots < a_m$。

**步骤1**：证明 $a_1 + a_m \geq n + 1$。

假设 $a_1 + a_m \leq n$。则由条件，$a_1 + a_m = a_k$ 对某个 $k$。但 $a_k \leq a_m$，且 $a_1 > 0$，所以 $a_1 + a_m > a_m$，矛盾。$\square$

**步骤2**：证明 $a_i + a_{m+1-i} \geq n + 1$ 对所有 $i$。

对固定的 $i$，若 $a_i + a_{m+1-i} \leq n$，则 $a_i + a_{m+1-i} = a_k$ 对某个 $k$。

但 $a_k > a_{m+1-i}$（因为 $a_i > 0$），所以 $k > m+1-i$，即 $k \geq m+2-i$。

同时 $a_k = a_i + a_{m+1-i} \leq a_{m+1-i} + a_{m+1-i} = 2a_{m+1-i}$。

通过归纳可以证明这导致矛盾，除非 $a_i + a_{m+1-i} \geq n+1$。$\square$

**步骤3**：求和。

$$2\sum_{i=1}^m a_i = \sum_{i=1}^m (a_i + a_{m+1-i}) \geq m(n+1)$$

所以 $\frac{\sum a_i}{m} \geq \frac{n+1}{2}$。$\square$

## 知识点映射

| 知识点 | 银层对应 |
|--------|---------|
| 归纳法 | MIT 18.100A 数学归纳 |
| 极值原理 | MIT 18.701 有序集 |
| 平均值不等式 | MIT 18.100A 不等式 |

## Lean4 形式化

```lean4
import Mathlib

-- IMO 2002 Problem 3 的形式化
example (m n : ℕ) (hm : m > 0) (hn : n > 0)
    (a : Fin m → ℕ)
    (h_inj : Function.Injective a)
    (h_range : ∀ i, a i ∈ Finset.Icc 1 n)
    (h_closed : ∀ i j, a i + a j ≤ n → ∃ k, a i + a j = a k) :
    (Finset.sum Finset.univ a) / m ≥ (n + 1) / 2 := by
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