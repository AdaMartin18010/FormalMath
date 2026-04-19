---
title: "IMO真题-代数：不等式与最值"
msc_primary: 00A99
level: silver
course: IMO竞赛数学
difficulty: L3
topic: 代数
source: "IMO 2001 Problem 2"
target_courses:
  - MIT 18.100A
status: completed
created_at: 2026-04-18
review_status: completed
---

# IMO 2001 Problem 2：不等式

## 题目

设 $a, b, c$ 为正实数。证明：

$$\frac{a}{\sqrt{a^2 + 8bc}} + \frac{b}{\sqrt{b^2 + 8ca}} + \frac{c}{\sqrt{c^2 + 8ab}} \geq 1$$

## 解答

**方法：Holder不等式或 Jensen 不等式**

**步骤1**：试探等号成立条件。

当 $a = b = c$ 时，每项 = $\frac{1}{3}$，和 = 1。

**步骤2**：利用Holder不等式。

由Holder不等式：

$$\left(\sum \frac{a}{\sqrt{a^2+8bc}}\right)^2 \left(\sum a(a^2+8bc)\right) \geq (a+b+c)^3$$

**步骤3**：证明 $\sum a(a^2+8bc) \leq (a+b+c)^3$。

$\sum a(a^2+8bc) = \sum a^3 + 8\sum abc = \sum a^3 + 24abc$

$(a+b+c)^3 = \sum a^3 + 3\sum_{sym} a^2b + 6abc$

需要证明：$3\sum_{sym} a^2b + 6abc \geq 24abc$，即 $\sum_{sym} a^2b \geq 6abc$。

由AM-GM：$a^2b + b^2c + c^2a + ab^2 + bc^2 + ca^2 \geq 6\sqrt[6]{a^6b^6c^6} = 6abc$。$\square$

**步骤4**：综合。

$$\left(\sum \frac{a}{\sqrt{a^2+8bc}}\right)^2 \geq \frac{(a+b+c)^3}{\sum a(a^2+8bc)} \geq 1$$

所以 $\sum \frac{a}{\sqrt{a^2+8bc}} \geq 1$。$\square$

## 知识点映射

| 知识点 | 银层对应 |
|--------|---------|
| Holder不等式 | MIT 18.100A 不等式 |
| AM-GM不等式 | MIT 18.100A 均值不等式 |
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

## 相关文档

- [IMO真题-不等式2](IMO真题-不等式2.md)
- [IMO真题-不等式3](IMO真题-不等式3.md)
- [IMO真题-代数1](IMO真题-代数1.md)
- [IMO真题-代数2](IMO真题-代数2.md)
- [IMO真题-几何1](IMO真题-几何1.md)

## 习题摘要

**习题 1.0** 参见上文问题 1。
## 参考文献

1. International Mathematical Olympiad (IMO). *Official Problems and Solutions*. Available at: https://www.imo-official.org/
2. Engel, A. (1998). *Problem-Solving Strategies*. Springer. ISBN: 978-0387982191.
3. Andreescu, T., & Gelca, R. (2000). *Mathematical Olympiad Challenges*. Birkhäuser. ISBN: 978-0817641900.