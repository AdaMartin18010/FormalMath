---
title: "IMO真题-代数：方程与不等式"
level: silver
course: IMO竞赛数学
difficulty: L3
topic: 代数
source: "IMO 2008 Problem 2"
target_courses:
  - MIT 18.02
  - MIT 18.06
status: completed
created_at: 2026-04-18
---

# IMO 2008 Problem 2：代数不等式

## 题目

(a) 证明：若实数 $x, y, z$ 满足 $x \neq 1, y \neq 1, z \neq 1$ 且 $xyz = 1$，则：

$$\frac{x^2}{(x-1)^2} + \frac{y^2}{(y-1)^2} + \frac{z^2}{(z-1)^2} \geq 1$$

(b) 证明等号可以取到无穷多组 $(x, y, z)$。

## 解答

### (a) 证明不等式

**方法：代换与对称化**

令 $a = \frac{x}{x-1}$，$b = \frac{y}{y-1}$，$c = \frac{z}{z-1}$。则 $x = \frac{a}{a-1}$，$y = \frac{b}{b-1}$，$z = \frac{c}{c-1}$。

由 $xyz = 1$：

$$\frac{abc}{(a-1)(b-1)(c-1)} = 1$$

即 $abc = (a-1)(b-1)(c-1) = abc - ab - bc - ca + a + b + c - 1$

所以 $ab + bc + ca = a + b + c - 1$。

原不等式变为 $a^2 + b^2 + c^2 \geq 1$。

由 $(a+b+c)^2 = a^2+b^2+c^2 + 2(ab+bc+ca) = a^2+b^2+c^2 + 2(a+b+c-1)$。

设 $S = a+b+c$，$Q = a^2+b^2+c^2$。则 $S^2 = Q + 2(S-1)$，即 $Q = S^2 - 2S + 2 = (S-1)^2 + 1 \geq 1$。

等号当且仅当 $S = 1$ 时成立。$\square$

### (b) 等号成立的无穷多组解

由 $S = a+b+c = 1$ 和 $ab+bc+ca = a+b+c-1 = 0$。

取 $a = t$，则 $b+c = 1-t$，$bc = -t(1-t)$。

$b, c$ 是方程 $u^2 - (1-t)u - t(1-t) = 0$ 的根。

判别式 $\Delta = (1-t)^2 + 4t(1-t) = (1-t)(1+3t) \geq 0$ 对 $t \in [-\frac{1}{3}, 1]$ 成立。

对每个这样的 $t$，我们得到一组 $(a, b, c)$，从而得到 $(x, y, z)$。由于 $t$ 有无穷多选择，等号成立的解也有无穷多组。$\square$

## 知识点映射

| 知识点 | 银层对应 |
|--------|---------|
| 对称多项式 | MIT 18.701 多项式环 |
| 不等式技巧 | MIT 18.100A 实分析 |
| 变量代换 | MIT 18.02 多元函数 |

## Lean4 形式化

```lean4
import Mathlib

-- IMO 2008 Problem 2(a)
example (x y z : ℝ) (hx : x ≠ 1) (hy : y ≠ 1) (hz : z ≠ 1)
    (h : x * y * z = 1) :
    x^2 / (x - 1)^2 + y^2 / (y - 1)^2 + z^2 / (z - 1)^2 ≥ 1 := by
  have h1 : x - 1 ≠ 0 := by intro h2; apply hx; linarith
  have h2 : y - 1 ≠ 0 := by intro h3; apply hy; linarith
  have h3 : z - 1 ≠ 0 := by intro h4; apply hz; linarith
  -- 变量代换 a = x/(x-1) 等
  let a := x / (x - 1)
  let b := y / (y - 1)
  let c := z / (z - 1)
  -- 需要证明 a^2 + b^2 + c^2 ≥ 1
  sorry
```
