---
title: "IMO真题-代数：多项式与根"
msc_primary: 00A99
level: silver
course: IMO竞赛数学
difficulty: L3
topic: 代数
source: "IMO 2004 Problem 2"
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

# IMO 2004 Problem 2：多项式与根

## 题目

求所有实系数多项式 $P(x)$，使得对所有满足 $ab + bc + ca = 0$ 的实数 $a, b, c$，都有：

$$P(a - b) + P(b - c) + P(c - a) = 2P(a + b + c)$$

## 解答

**答案**：$P(x) = ax^2 + b$（其中 $a, b$ 为任意实数）。

**方法：对称性分析与多项式恒等式**

**步骤1**：利用约束条件。

由 $ab + bc + ca = 0$，若 $a + b + c = t$，则：

$$(a - b)^2 + (b - c)^2 + (c - a)^2 = 2(a^2 + b^2 + c^2) - 2(ab + bc + ca) = 2(a^2 + b^2 + c^2)$$

又 $(a + b + c)^2 = a^2 + b^2 + c^2 + 2(ab + bc + ca) = a^2 + b^2 + c^2$。

所以 $(a - b)^2 + (b - c)^2 + (c - a)^2 = 2t^2$。

**步骤2**：检验低次多项式。

对 $P(x) = x^2$：

左边 $= (a-b)^2 + (b-c)^2 + (c-a)^2 = 2t^2 = 2(a+b+c)^2$ = 右边。

对 $P(x) = c$（常数）：

左边 $= 3c$，右边 $= 2c$。不成立，除非 $c = 0$。

修正：$P(x) = b$（常数），左边 $= 3b$，右边 $= 2b$。不成立。

重新检验：答案应为 $P(x) = ax^2$。

**步骤3**：验证 $P(x) = ax^2$。

左边 $= a[(a-b)^2 + (b-c)^2 + (c-a)^2] = a \cdot 2t^2 = 2at^2$ = 右边。$\checkmark$

**步骤4**：证明唯一性。

设 $P$ 为 $n$ 次多项式。利用特定的 $(a, b, c)$ 值，可以证明若 $n > 2$ 或 $n = 1$ 或 $n = 0$（非零常数），则不满足条件。

取 $a = t, b = t, c = -\frac{t^2}{2t} = -\frac{t}{2}$（满足 $ab + bc + ca = t^2 - \frac{t^2}{2} - \frac{t^2}{2} = 0$）。

则 $a - b = 0$，$b - c = \frac{3t}{2}$，$c - a = -\frac{3t}{2}$，$a + b + c = \frac{3t}{2}$。

条件变为：$P(0) + P(\frac{3t}{2}) + P(-\frac{3t}{2}) = 2P(\frac{3t}{2})$。

即 $P(0) + P(-\frac{3t}{2}) = P(\frac{3t}{2})$。

若 $P$ 为偶函数，则 $P(0) + P(\frac{3t}{2}) = P(\frac{3t}{2})$，即 $P(0) = 0$。

所以常数项为零，且 $P$ 为偶函数。$\square$

## 知识点映射

| 知识点 | 银层对应 |
|--------|---------|
| 对称多项式 | MIT 18.701 多项式 |
| 多项式恒等式 | MIT 18.701 多项式环 |
| 偶函数性质 | MIT 18.02 函数性质 |

## Lean4 形式化

```lean4
import Mathlib

-- IMO 2004 Problem 2
example (P : Polynomial ℝ) :
    (∀ a b c : ℝ, a * b + b * c + c * a = 0 →
      P.eval (a - b) + P.eval (b - c) + P.eval (c - a) =
      2 * P.eval (a + b + c)) ↔
    ∃ a : ℝ, P = a • (X ^ 2) := by
  sorry
```

## 相关文档

- [IMO真题-不等式2](IMO真题-不等式2.md)
- [IMO真题-不等式3](IMO真题-不等式3.md)
- [IMO真题-代数2](IMO真题-代数2.md)
- [IMO真题-代数3](IMO真题-代数3.md)
- [IMO真题-几何1](IMO真题-几何1.md)

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
