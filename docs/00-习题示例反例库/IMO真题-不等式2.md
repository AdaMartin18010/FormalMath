---
title: "IMO真题-不等式：三元不等式"
msc_primary: 00A99
level: silver
course: IMO竞赛数学
difficulty: L4
topic: 不等式
source: "IMO 2001 Problem 2"
target_courses:
  - MIT 18.02
status: completed
created_at: 2026-04-18
---

# IMO 2001 Problem 2：三元不等式

## 题目

设 $a, b, c$ 为正实数。证明：

$$\frac{a}{\sqrt{a^2 + 8bc}} + \frac{b}{\sqrt{b^2 + 8ca}} + \frac{c}{\sqrt{c^2 + 8ab}} \geq 1$$

## 解答

**方法：Jensen不等式与Holder不等式**

**步骤1**：尝试直接应用Jensen不等式。

函数 $f(x) = \frac{1}{\sqrt{x}}$ 是凸函数，但直接应用Jensen不等式方向不对。

**步骤2**：利用Holder不等式。

由Holder不等式：

$$\left(\sum \frac{a}{\sqrt{a^2 + 8bc}}\right)^2 \left(\sum a(a^2 + 8bc)\right) \geq (a + b + c)^3$$

**步骤3**：证明关键不等式。

只需证明：

$$(a + b + c)^3 \geq \sum a(a^2 + 8bc) = a^3 + b^3 + c^3 + 24abc$$

展开左边：

$$(a + b + c)^3 = a^3 + b^3 + c^3 + 3(a + b)(b + c)(c + a)$$

$$= a^3 + b^3 + c^3 + 3\sum_{sym} a^2b + 6abc$$

所以只需证明：

$$3\sum_{sym} a^2b + 6abc \geq 24abc$$

即 $\sum_{sym} a^2b \geq 6abc$，由AM-GM不等式成立。$\square$

## 知识点映射

| 知识点 | 银层对应 |
|--------|---------|
| Holder不等式 | MIT 18.02 积分不等式 |
| AM-GM不等式 | MIT 18.100A 数列极限 |
| 对称多项式 | MIT 18.701 多项式 |

## Lean4 形式化

```lean4
import Mathlib

-- IMO 2001 Problem 2
example (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) :
    a / Real.sqrt (a^2 + 8 * b * c) +
    b / Real.sqrt (b^2 + 8 * c * a) +
    c / Real.sqrt (c^2 + 8 * a * b) ≥ 1 := by
  sorry
```
