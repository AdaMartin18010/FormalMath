---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: IMO 2010 Problem 01
---

# IMO 2010 Problem 01

## 题目

求所有函数 $f: \mathbb{R} \to \mathbb{R}$，使得对所有实数 $x, y$：
$$f(\lfloor x \rfloor y) = f(x) \lfloor f(y) \rfloor$$
其中 $\lfloor t \rfloor$ 表示不超过 $t$ 的最大整数。

## 分类信息
- **领域**: 代数（函数方程）
- **难度**: 4分
- **涉及概念**: 取整函数、函数方程

## 解答

### 方法一：分类讨论法

**答案**：$f(x) \equiv c$，其中 $c = 0$ 或 $1 \leq c < 2$。

**步骤1：代入 $x = 0$**

令 $x = 0$，则对任意 $y \in \mathbb{R}$：
$$f(0) = f(0) \cdot \lfloor f(y) \rfloor$$

这给出两种可能：
- **情况A**：$\lfloor f(y) \rfloor = 1$ 对所有 $y$ 成立，即 $1 \leq f(y) < 2$ 对所有 $y$。
- **情况B**：$f(0) = 0$。

**步骤2：分析情况A**

若 $1 \leq f(y) < 2$ 对所有 $y$，则原方程变为：
$$f(\lfloor x \rfloor y) = f(x) \cdot 1 = f(x)$$

令 $y = 0$，得 $f(0) = f(x)$ 对所有 $x$。故 $f$ 是常数函数 $f(x) \equiv c$。
由情况A的条件，$1 \leq c < 2$。验证：$\lfloor c \rfloor = 1$，方程变为 $c = c \cdot 1$，成立。

**步骤3：分析情况B（$f(0) = 0$）**

**子情况B1**：存在 $\alpha \in (0,1)$ 使得 $f(\alpha) \neq 0$。

令 $x = \alpha$，则对任意 $y$：
$$f(0) = f(\alpha) \cdot \lfloor f(y) \rfloor$$
由于 $f(0) = 0$ 且 $f(\alpha) \neq 0$，得 $\lfloor f(y) \rfloor = 0$ 对所有 $y$。

现在令 $x = 1$，原方程给出：
$$f(y) = f(1) \cdot \lfloor f(y) \rfloor = f(1) \cdot 0 = 0$$
故 $f(y) = 0$ 对所有 $y$。但这与 $f(\alpha) \neq 0$ 矛盾！

因此子情况B1不可能发生。

**子情况B2**：$f(\alpha) = 0$ 对所有 $\alpha \in [0,1)$。

对任意实数 $z$，取整数 $N$ 使得 $\alpha = z/N \in [0,1)$（例如 $N = \lfloor z \rfloor + 1$ 若 $z \geq 0$，否则 $N = \lfloor z \rfloor - 1$）。

由 $f(\alpha) = 0$ 和原方程（取 $x = N$，注意 $\lfloor N \rfloor = N$）：
$$f(z) = f(N \cdot \alpha) = f(N) \cdot \lfloor f(\alpha) \rfloor = f(N) \cdot 0 = 0$$

故 $f(z) = 0$ 对所有 $z \in \mathbb{R}$。验证：$f(x) \equiv 0$ 满足原方程。

**结论**：所有解为 $f(x) \equiv 0$ 或 $f(x) \equiv c$（$1 \leq c < 2$）。$\square$

### 方法二：利用取整函数性质

**关键观察**：令 $y = 1$，则 $f(\lfloor x \rfloor) = f(x) \lfloor f(1) \rfloor$。

若 $\lfloor f(1) \rfloor = 0$，则 $f(\lfloor x \rfloor) = 0$ 对所有 $x$。由于 $\lfloor x \rfloor$ 取遍所有整数，$f(n) = 0$ 对所有 $n \in \mathbb{Z}$。再利用原方程对整数 $x$ 可推出 $f \equiv 0$。

若 $\lfloor f(1) \rfloor \neq 0$，则 $f(x) = f(\lfloor x \rfloor) / \lfloor f(1) \rfloor$，说明 $f$ 在每个区间 $[n, n+1)$ 上为常数。进一步分析可推出 $f$ 为全局常数。

## 关键思路

1. **从特殊值入手**：$x = 0$ 和 $y = 0$ 的代入是破解函数方程的经典策略
2. **利用取整函数的分段常数性质**：$\lfloor x \rfloor$ 在 $[n, n+1)$ 上恒为 $n$，这使得函数在区间上的行为高度受限
3. **分类讨论**：对 $f(0)$ 是否为零进行分类，覆盖了所有可能性

## 相关定理与概念
- **取整函数（Floor function）**：$\lfloor x \rfloor = \max\{n \in \mathbb{Z} : n \leq x\}$
- **函数方程**：寻找满足特定代数关系的函数
- **Cauchy型函数方程**：$f(x+y) = f(x) + f(y)$ 等经典方程

## 变体问题

### 变体1
求所有函数 $f: \mathbb{R} \to \mathbb{R}$ 使得 $f(\lceil x \rceil y) = f(x) \lceil f(y) \rceil$。

### 变体2
求所有函数 $f: \mathbb{Z} \to \mathbb{Z}$ 使得 $f(mn) = f(m) f(n)$（乘法函数方程）。

## 参考资源
- [IMO 2010 Official Solutions](https://www.imo-official.org/problems/IMO2010SL.pdf)
- [AoPS讨论链接](https://artofproblemsolving.com/community/c6h1935849)

---

*解答整理：FormalMath项目团队*
