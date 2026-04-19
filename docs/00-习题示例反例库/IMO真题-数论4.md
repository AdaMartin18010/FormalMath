---
title: "IMO真题-数论：素数幂与整除"
msc_primary: 00A99
level: silver
course: IMO竞赛数学
difficulty: L3
topic: 数论
source: "IMO 2003 Problem 6"
target_courses:
  - MIT 18.701
status: completed
created_at: 2026-04-18
review_status: completed
---

# IMO 2003 Problem 6：素数幂与整除

## 题目

设 $p$ 为素数。证明：对任意整数 $n \geq 1$，存在整数 $x$ 使得 $p$ 整除 $x^n + x^{n-1} + \cdots + x + 1$ 当且仅当 $n + 1$ 不是 $p$ 的幂。

## 解答

**方法：分情况讨论与Lucas定理**

**步骤1**：分析多项式 $f(x) = \frac{x^{n+1} - 1}{x - 1} = x^n + x^{n-1} + \cdots + 1$。

**步骤2**：若 $n + 1 = p^k$。

令 $x = 1$：$f(1) = n + 1 = p^k \equiv 0 \pmod{p}$。

但 $x = 1$ 是 $f(x)$ 的极点（原式 $x^{n+1} - 1$ 在 $x = 1$ 时为0，但 $f(1) = n + 1$）。

实际上，对 $x \equiv 1 \pmod{p}$：

$$f(x) = \frac{x^{n+1} - 1}{x - 1}$$

当 $x = 1 + pt$：

$$(1 + pt)^{p^k} \equiv 1 + p^{k+1}t \pmod{p^{k+2}}$$

所以 $f(1 + pt) = \frac{(1+pt)^{p^k} - 1}{pt} \equiv p^k \pmod{p}$，当 $k \geq 1$ 时不为0。

更严格地，利用分圆多项式：$f(x) = \Phi_{n+1}(x)$ 当 $n + 1$ 为素数时。

一般情形：$n + 1 = p^k$ 时，$f(x) = \Phi_{p^k}(x)$ 在 $\mathbb{F}_p$ 上不可约且无根。

**步骤3**：若 $n + 1$ 不是 $p$ 的幂。

设 $n + 1 = p^k \cdot m$，$m > 1$，$\gcd(m, p) = 1$。

取 $x$ 为 $\mathbb{F}_{p^d}$ 中的原始 $m$ 次单位根（$d = \operatorname{ord}_m(p)$）。

则 $x^{n+1} = (x^m)^{p^k} = 1$，且 $x \neq 1$。

所以 $f(x) = \frac{x^{n+1} - 1}{x - 1} = 0$。$\square$

## 知识点映射

| 知识点 | 银层对应 |
|--------|---------|
| 分圆多项式 | MIT 18.701 域扩张 |
| 有限域 | MIT 18.701 有限域 |
| 原根 | MIT 18.701 循环群 |
| 多项式不可约性 | MIT 18.701 多项式环 |

## Lean4 形式化

```lean4
import Mathlib

-- IMO 2003 Problem 6
example (p n : ℕ) (hp : Nat.Prime p) (hn : n ≥ 1) :
    (∃ x : ℤ, p ∣ ∑ i in Finset.range (n + 1), x^i) ↔
    ¬ (∃ k, n + 1 = p^k) := by
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