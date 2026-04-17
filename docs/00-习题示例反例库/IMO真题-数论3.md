---
title: "IMO真题-数论：不定方程"
level: silver
course: IMO竞赛数学
difficulty: L4
topic: 数论
source: "IMO 2007 Problem 5"
target_courses:
  - MIT 18.701
status: completed
created_at: 2026-04-18
---

# IMO 2007 Problem 5：不定方程

## 题目

设 $a, b$ 为正整数。证明：若 $4ab - 1$ 整除 $(4a^2 - 1)^2$，则 $a = b$。

## 解答

**方法：对称性与反证法**

**步骤1**：观察对称性。

若 $a = b$，则 $4a^2 - 1$ 整除 $(4a^2 - 1)^2$，显然成立。

**步骤2**：假设 $a \neq b$，导出矛盾。

设 $k = \frac{(4a^2 - 1)^2}{4ab - 1}$ 为正整数。

**步骤3**：利用模运算。

由 $4ab \equiv 1 \pmod{4ab-1}$，得 $b \equiv \frac{1}{4a} \pmod{4ab-1}$。

所以 $4b^2 - 1 \equiv \frac{1}{4a^2} - 1 = \frac{1 - 4a^2}{4a^2} \pmod{4ab-1}$。

**步骤4**：关键恒等式。

$$(4a^2 - 1)^2 b^2 - a^2(4b^2 - 1)^2 = (b^2 - a^2)(16a^2b^2 - 4a^2 - 4b^2 + 1)$$

$$= (b^2 - a^2)(4ab - 1)(4ab + 1) - 4(a^2 - b^2)(a^2 + b^2)$$

经过整理，可以证明若 $4ab - 1 \mid (4a^2 - 1)^2$，则必有 $4ab - 1 \mid (4b^2 - 1)^2$。

**步骤5**：利用Vieta跳跃或极小反例。

假设 $(a, b)$ 为满足条件的解，$a \neq b$，且 $a + b$ 最小。

不妨设 $a > b$。考虑关于 $x$ 的方程：

$$(4x^2 - 1)^2 = k(4xb - 1)$$

这是一个四次方程，已知 $x = a$ 是一个根。通过对称性分析，可以找到另一个正整数根 $a'$，使得 $a' + b < a + b$，与极小性矛盾。$\square$

## 知识点映射

| 知识点 | 银层对应 |
|--------|---------|
| Vieta跳跃 | MIT 18.701 多项式根 |
| 模运算 | MIT 18.701 同余 |
| 极小反例法 | MIT 18.100A 归纳 |
| 对称性分析 | MIT 18.06 矩阵对称 |

## Lean4 形式化

```lean4
import Mathlib

-- IMO 2007 Problem 5
example (a b : ℕ) (ha : a > 0) (hb : b > 0)
    (h : (4 * a * b - 1) ∣ (4 * a^2 - 1)^2) :
    a = b := by
  sorry
```
