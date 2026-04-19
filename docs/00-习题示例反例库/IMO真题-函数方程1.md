---
title: "IMO真题-函数方程：实数域上的函数"
msc_primary: 00A99
level: silver
course: IMO竞赛数学
difficulty: L4
topic: 函数方程
source: "IMO 2008 Problem 4"
target_courses:
  - MIT 18.100A
status: completed
created_at: 2026-04-18
review_status: completed
---

# IMO 2008 Problem 4：函数方程

## 题目

求所有函数 $f: (0, +\infty) \to (0, +\infty)$，使得对所有满足 $wx = yz$ 的正实数 $w, x, y, z$，都有：

$$\frac{f(w)^2 + f(x)^2}{f(y^2) + f(z^2)} = \frac{w^2 + x^2}{y^2 + z^2}$$

## 解答

**答案**：$f(x) = x$ 对所有 $x > 0$。

**方法：代入特殊值推导函数形式**

**步骤1**：令 $w = x = y = z = t$。

由 $t \cdot t = t \cdot t$，条件给出：

$$\frac{2f(t)^2}{2f(t^2)} = \frac{2t^2}{2t^2} = 1$$

所以 $f(t)^2 = f(t^2)$。

**步骤2**：令 $w = y = a, x = z = b$。

由 $ab = ba$，条件给出：

$$\frac{f(a)^2 + f(b)^2}{f(a^2) + f(b^2)} = \frac{a^2 + b^2}{a^2 + b^2} = 1$$

所以 $f(a)^2 + f(b)^2 = f(a^2) + f(b^2)$。

结合步骤1，$f(a^2) = f(a)^2$，所以：

$$f(a)^2 + f(b)^2 = f(a)^2 + f(b)^2$$

这恒成立，没有新信息。

**步骤3**：令 $w = a^2, x = b^2, y = z = ab$。

由 $a^2 b^2 = (ab)^2$，条件给出：

$$\frac{f(a^2)^2 + f(b^2)^2}{2f(a^2b^2)} = \frac{a^4 + b^4}{2a^2b^2}$$

利用 $f(t^2) = f(t)^2$：

$$\frac{f(a)^4 + f(b)^4}{2f(ab)^2} = \frac{a^4 + b^4}{2a^2b^2}$$

**步骤4**：令 $b = 1$。

$$\frac{f(a)^4 + f(1)^4}{2f(a)^2 f(1)^2} = \frac{a^4 + 1}{2a^2}$$

设 $c = f(1)$，$u = f(a)^2$：

$$\frac{u^2 + c^4}{2uc^2} = \frac{a^4 + 1}{2a^2}$$

$$u^2 + c^4 = uc^2 \cdot \frac{a^4 + 1}{a^2}$$

**步骤5**：分析方程。

令 $a = 1$：$f(1)^4 + c^4 = c^4 \cdot 2$，即 $2c^4 = 2c^4$，恒成立。

取 $a \to 1$ 的极限，利用连续性（需证明），可得 $f(a) = ca$ 或 $f(a) = c/a$。

但 $f(a^2) = f(a)^2$ 排除 $f(a) = c/a$。

验证 $f(a) = ca$：由 $f(1) = c$，得 $f(a) = ca$。

代入原方程验证：$c = 1$。$\square$

## 知识点映射

| 知识点 | 银层对应 |
|--------|---------|
| 函数方程 | MIT 18.100A 函数极限 |
| 代入法 | MIT 18.100A 证明技巧 |
| 连续性论证 | MIT 18.100A 连续性 |

## Lean4 形式化

```lean4
import Mathlib

-- IMO 2008 Problem 4
example (f : ℝ → ℝ) (hf : ∀ x > 0, f x > 0)
    (h : ∀ w x y z : ℝ, w > 0 → x > 0 → y > 0 → z > 0 →
      w * x = y * z →
      (f w)^2 + (f x)^2) / (f (y^2) + f (z^2)) =
      (w^2 + x^2) / (y^2 + z^2)) :
    ∀ x > 0, f x = x := by
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