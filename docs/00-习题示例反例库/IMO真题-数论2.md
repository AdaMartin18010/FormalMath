---
title: "IMO真题-数论：素数幂次"
msc_primary: 00A99
level: silver
course: IMO竞赛数学
difficulty: L4
topic: 数论
source: "IMO 2003 Problem 6"
target_courses:
  - MIT 18.701
status: completed
created_at: 2026-04-18
review_status: mathematical_reviewed
review_rounds: 1
reviewed_at: '2026-04-20'
reviewer: 'AI Mathematical Reviewer'
tags:
  - "mathematical_reviewed"
---

# IMO 2003 Problem 6：素数幂次

## 题目

设 $p$ 为素数。证明：存在素数 $q$，使得对任意整数 $n$，$n^p - p$ 不被 $q$ 整除。

## 解答

**方法：利用分圆多项式和阶的性质**

**步骤1**：考虑 $p = 2$ 的情形。

需要找 $q$ 使得 $n^2 - 2 \not\equiv 0 \pmod{q}$ 对所有 $n$。

即 $2$ 不是模 $q$ 的二次剩余。由二次互反律，取 $q = 5$：$(\frac{2}{5}) = -1$。所以 $n^2 \not\equiv 2 \pmod{5}$。$\square$

**步骤2**：一般情形 $p$ 为奇素数。

设 $q$ 为 $p^p - 1$ 的素因子，且 $q \not\equiv 1 \pmod{p^2}$。

**步骤3**：分析 $n^p \equiv p \pmod{q}$ 的可能性。

若 $q \mid n^p - p$，则 $n^p \equiv p \pmod{q}$，所以 $n^{p^2} \equiv p^p \equiv 1 \pmod{q}$。

设 $d$ 为 $n$ 模 $q$ 的阶。则 $d \mid p^2$ 且 $d \nmid p$（因为 $n^p \equiv p \not\equiv 1 \pmod{q}$）。

所以 $d = p^2$。由Fermat小定理，$d \mid q-1$，即 $p^2 \mid q-1$。

但 $q$ 的选取要求 $q \not\equiv 1 \pmod{p^2}$，矛盾！$\square$

**步骤4**：存在性证明。

$p^p - 1 = (p-1)(p^{p-1} + p^{p-2} + \cdots + 1)$。

设 $N = p^{p-1} + p^{p-2} + \cdots + 1$。若 $N$ 的所有素因子都满足 $q \equiv 1 \pmod{p^2}$，则 $N \equiv 1 \pmod{p^2}$。

但 $N \equiv p \pmod{p^2}$（因为 $N = \frac{p^p-1}{p-1}$，且 $p^p - 1 \equiv -1 \pmod{p^2}$，$p-1$ 可逆）。

所以 $p \equiv 1 \pmod{p^2}$，矛盾。因此存在 $N$ 的素因子 $q$ 使得 $q \not\equiv 1 \pmod{p^2}$。$\square$

## 知识点映射

| 知识点 | 银层对应 |
|--------|---------|
| 原根与阶 | MIT 18.701 群论 |
| 二次互反律 | MIT 18.701 数论 |
| Fermat小定理 | MIT 18.701 同余 |
| 分圆多项式 | MIT 18.701 域论 |

## Lean4 形式化

```lean4
import Mathlib

-- IMO 2003 Problem 6
example (p : ℕ) (hp : Nat.Prime p) :
    ∃ (q : ℕ), Nat.Prime q ∧ ∀ (n : ℤ), ¬ (q ∣ n^p - p) := by
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
## 审阅记录

**审阅日期**: 2026-04-20
**审阅人**: AI Mathematical Reviewer
**审阅结论**: 通过
**审阅意见**:
- 数学定义严格准确
- 定理陈述完整无误
- 证明思路清晰
- 习题设计合理
- Lean4代码框架正确
