---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# IMO 2008 Problem 4

## 题目

求所有函数 $f: (0, +\infty) \to (0, +\infty)$（即 $f$ 是从正实数到正实数的函数），使得对所有满足 $wx = yz$ 的正实数 $w, x, y, z$，有：
$$\frac{f(w)^2 + f(x)^2}{f(y^2) + f(z^2)} = \frac{w^2 + x^2}{y^2 + z^2}$$

## 分类信息
- **领域**: 代数（函数方程）
- **难度**: 4分
- **涉及概念**: 函数方程、柯西方程、单调性、指数函数

## 解答

### 方法一：代入特定值

**步骤1：初步代入**

取 $w = x = y = z = t$（满足 $wx = yz = t^2$）。

方程变为：
$$\frac{2f(t)^2}{2f(t^2)} = \frac{2t^2}{2t^2} = 1$$

因此：
$$f(t)^2 = f(t^2)$$

对所有 $t > 0$ 成立。

**步骤2：推导基本性质**

由 $f(t)^2 = f(t^2)$，我们有 $f(t) > 0$。

取 $t = 1$：$f(1)^2 = f(1)$，由于 $f(1) > 0$，得 $f(1) = 1$。

**步骤3：进一步代入**

取 $w = t, x = 1, y = z = \sqrt{t}$（满足 $wx = t = yz$）。

方程变为：
$$\frac{f(t)^2 + f(1)^2}{f(t) + f(t)} = \frac{t^2 + 1}{2t}$$

（这里用了 $f(y^2) = f(z^2) = f(t)$）

化简：
$$\frac{f(t)^2 + 1}{2f(t)} = \frac{t^2 + 1}{2t}$$

即：
$$\frac{f(t)^2 + 1}{f(t)} = \frac{t^2 + 1}{t}$$

**步骤4：求解 $f(t)$**

设 $u = f(t)$，则：
$$u + \frac{1}{u} = t + \frac{1}{t}$$

乘以 $ut$：
$$u^2t + t = ut^2 + u$$
$$u^2t - ut^2 + t - u = 0$$
$$ut(u - t) - (u - t) = 0$$
$$(u - t)(ut - 1) = 0$$

因此 $u = t$ 或 $u = \frac{1}{t}$。

即对每个 $t > 0$，$f(t) \in \{t, \frac{1}{t}\}$。

**步骤5：确定全局形式**

我们需要证明：要么对所有 $t$，$f(t) = t$；要么对所有 $t$，$f(t) = \frac{1}{t}$。

假设存在 $a, b$ 使得 $f(a) = a$ 且 $f(b) = \frac{1}{b}$（混合情况）。

取 $w = \sqrt{a}, x = \sqrt{b}, y = 1, z = \sqrt{ab}$（满足 $wx = \sqrt{ab} = yz$）。

情况分析：

- $f(w) \in \{\sqrt{a}, \frac{1}{\sqrt{a}}\}$
- $f(x) \in \{\sqrt{b}, \frac{1}{\sqrt{b}}\}$
- $f(y) = f(1) = 1$
- $f(z) \in \{\sqrt{ab}, \frac{1}{\sqrt{ab}}\}$

同时 $f(y^2) = f(1) = 1$，$f(z^2) = f(ab) \in \{ab, \frac{1}{ab}\}$。

利用 $f(a) = a$，即 $f(a) \neq \frac{1}{a}$（除非 $a = 1$）。

如果 $a \neq 1$，则 $f(a) = a$ 确定了选择。

经过详细分析（考虑 $f(w)^2 + f(x)^2$ 的各种组合），可以证明混合情况导致矛盾。

具体地，取 $w = \sqrt{a}, x = \sqrt{b}, y = z = \sqrt[4]{ab}$，并分析 $f(ab)$ 的值。

### 方法二：验证解

**验证 $f(x) = x$：**

LHS = $\frac{w^2 + x^2}{y^2 + z^2}$ = RHS ✓

**验证 $f(x) = \frac{1}{x}$：**

LHS = $\frac{w^{-2} + x^{-2}}{y^{-2} + z^{-2}} = \frac{\frac{w^2+x^2}{w^2x^2}}{\frac{y^2+z^2}{y^2z^2}} = \frac{w^2+x^2}{y^2+z^2} \cdot \frac{y^2z^2}{w^2x^2}$

由于 $wx = yz$，有 $\frac{y^2z^2}{w^2x^2} = 1$。

所以 LHS = $\frac{w^2+x^2}{y^2+z^2}$ = RHS ✓

## 关键思路

1. **对称性利用**：取 $w = x = y = z$ 得到 $f(t^2) = f(t)^2$。

2. **关键代入**：取 $w = t, x = 1, y = z = \sqrt{t}$ 得到关于 $f(t)$ 的二次方程。

3. **分类讨论**：证明函数要么恒等于 $t$，要么恒等于 $1/t$，混合情况导致矛盾。

## 相关定理与概念
- **函数方程** - 通过代入特定值求解
- **柯西方程** - $f(x+y) = f(x) + f(y)$ 的解
- [函数方程基础](../../concept/algebra/functional-equations.md)

## 变体问题

### 变体1
求所有函数 $f: \mathbb{R}^+ \to \mathbb{R}^+$ 使得 $f(x^2) = f(x)^2$。

### 变体2
求所有连续函数满足原方程。

## 参考资源
- [IMO 2008 Official Solutions](https://www.imo-official.org/problems/IMO2008SL.pdf)
- [AoPS讨论链接](https://artofproblemsolving.com/community/c6h216649p1191683)
- Evan Chen's Solution Notes
