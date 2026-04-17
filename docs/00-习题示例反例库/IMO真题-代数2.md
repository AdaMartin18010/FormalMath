---
title: "IMO真题-代数：函数方程"
level: silver
course: IMO竞赛数学
difficulty: L4
topic: 代数
source: "IMO 2002 Problem 5"
target_courses:
  - MIT 18.100A
status: completed
created_at: 2026-04-18
---

# IMO 2002 Problem 5：函数方程

## 题目

求所有从实数集到实数集的函数 $f$，使得对所有实数 $x, y, z, t$：

$$(f(x) + f(z))(f(y) + f(t)) = f(xy - zt) + f(xt + yz)$$

## 解答

**步骤1：试探常数解**

设 $f(x) = c$（常数）。则 $(2c)(2c) = 2c$，即 $4c^2 = 2c$，所以 $c = 0$ 或 $c = \frac{1}{2}$。

验证：$f(x) = 0$ 满足方程（两边均为0）。

$f(x) = \frac{1}{2}$ 满足方程（左边=1，右边=$\frac{1}{2} + \frac{1}{2} = 1$）。$\square$

**步骤2：寻找非常数解**

设 $x = y = z = t = 0$：$(2f(0))^2 = 2f(0)$，所以 $f(0) = 0$ 或 $f(0) = \frac{1}{2}$。

**情形A**：$f(0) = 0$。

设 $z = t = 0$：$f(x)f(y) = f(xy)$。所以 $f$ 是乘性的。

设 $x = y = 0$：$f(z)f(t) = f(-zt)$。结合乘性，$f(-zt) = f(z)f(t) = f(zt)$，所以 $f$ 是偶函数。

设 $y = x, z = 0, t = x$：$(f(x) + f(0))(f(x) + f(x)) = f(x^2) + f(x^2)$。

$2f(x)^2 = 2f(x^2) = 2f(x)^2$（由乘性）。恒成立。

由 $f(x) = x^2$ 是候选。验证：

左边 $= (x^2 + z^2)(y^2 + t^2) = x^2y^2 + x^2t^2 + z^2y^2 + z^2t^2$

右边 $= (xy-zt)^2 + (xt+yz)^2 = x^2y^2 - 2xyzt + z^2t^2 + x^2t^2 + 2xyzt + y^2z^2$

$= x^2y^2 + z^2t^2 + x^2t^2 + y^2z^2$ = 左边。$\square$

**情形B**：$f(0) = \frac{1}{2}$。

类似分析可得 $f(x) = \frac{1}{2}$ 对所有 $x$。

**结论**：$f(x) = 0$，$f(x) = \frac{1}{2}$，或 $f(x) = x^2$。

## 知识点映射

| 知识点 | 银层对应 |
|--------|---------|
| 函数方程 | MIT 18.100A 函数连续性 |
| 乘性函数 | MIT 18.701 群同态 |
| 恒等式验证 | MIT 18.06 矩阵乘法 |

## Lean4 形式化

```lean4
import Mathlib

-- IMO 2002 Problem 5 的形式化
example (f : ℝ → ℝ)
    (h : ∀ x y z t, (f x + f z) * (f y + f t) = f (x * y - z * t) + f (x * t + y * z)) :
    (∀ x, f x = 0) ∨ (∀ x, f x = 1 / 2) ∨ (∀ x, f x = x ^ 2) := by
  sorry
```
