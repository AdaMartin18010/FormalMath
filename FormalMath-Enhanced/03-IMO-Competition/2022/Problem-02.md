---
msc_primary: 00A99
processed_at: 2026-04-15
title: IMO 2022 Problem 2
---
# IMO 2022 Problem 2

## 题目
求所有函数 $f:\mathbb{R}^+\to\mathbb{R}^+$，使得对每个 $x\in\mathbb{R}^+$，存在唯一的 $y\in\mathbb{R}^+$ 满足
$$xf(y)+yf(x)\le2.$$

## 分类信息
- **领域**: 代数/函数方程
- **难度**: 5分
- **涉及概念**: 函数方程、不等式、唯一性、连续性

## 解答

### 答案
唯一解为 $f(x)=\frac{1}{x}$（对所有 $x>0$）。

### 证明
显然 $f(x)=1/x$ 满足条件（此时唯一 $y=x$）。

下设 $f$ 满足条件。对每个 $x$，称满足不等式的唯一 $y$ 为 $x$ 的"朋友"。由对称性，若 $y$ 是 $x$ 的朋友，则 $x$ 也是 $y$ 的朋友。

**引理**：每个数都是自己的朋友。
*证明*：假设 $a\neq b$ 互为朋友。则由唯一性，$af(a)+af(a)>2$，即 $f(a)>1/a$；同理 $f(b)>1/b$。但
$$2\ge af(b)+bf(a)>\frac{a}{b}+\frac{b}{a}\stackrel{\text{AM-GM}}{\ge}2,$$
矛盾。*

因此 $xf(x)\le2$ 对所有 $x$ 成立，且对 $x\neq y$ 有 $xf(y)+yf(x)>2$。

固定 $x>0$，对任意 $\varepsilon>0$，取 $y=x+\varepsilon$。则
$$2<xf(x+\varepsilon)+(x+\varepsilon)f(x)\le\frac{x}{x+\varepsilon}+(x+\varepsilon)f(x).$$
整理得
$$f(x)>\frac{1}{x+\varepsilon}\cdot\frac{x+2\varepsilon}{x+\varepsilon}=\frac{1}{x}+\frac{\varepsilon^2}{x(x+\varepsilon)^2}>\frac{1}{x}.$$
令 $\varepsilon\to0^+$，得 $f(x)\ge1/x$。结合 $xf(x)\le2$？不对，引理只给出 $xf(x)\le2$，不是 $xf(x)\le1$。重新整理：

由 $2<xf(x+\varepsilon)+(x+\varepsilon)f(x)$ 及 $f(x+\varepsilon)\le1/(x+\varepsilon)$（待证），需要更严谨的推导。

**修正推导**：已知对任意 $x,y>0$ 且 $x\neq y$，有 $xf(y)+yf(x)>2$。固定 $x$，令 $y\to x^+$，若 $f$ 在某点有极限，则 $2xf(x)\ge2$，即 $f(x)\ge1/x$。结合引理中 $xf(x)\le2$？不，引理说的是 $xf(x)+xf(x)>2$，即 $f(x)>1/x$ 当 $x$ 有朋友时。由于 $x$ 是自己的朋友，$xf(x)\le2$ 不是直接结论；直接结论是不等式 $xf(y)+yf(x)\le2$ 在 $y=x$ 时成立，即 $2xf(x)\le2$，所以 $f(x)\le1/x$。

但前面又推出 $f(x)\ge1/x$（通过连续性或取极限）。因此 $f(x)=1/x$。

严格地，对任意 $x>0$ 和 $\varepsilon>0$：
$$2<xf(x+\varepsilon)+(x+\varepsilon)f(x).$$
假设已知 $f(x+\varepsilon)\le1/(x+\varepsilon)$（由自己是自己的朋友），则
$$2<\frac{x}{x+\varepsilon}+(x+\varepsilon)f(x)\implies f(x)>\frac{x+2\varepsilon}{(x+\varepsilon)^2}.$$
令 $\varepsilon\to0$ 得 $f(x)\ge1/x$。结合 $f(x)\le1/x$，得 $f(x)=1/x$。

## 关键思路与技巧
1. **朋友对称性**：定义朋友关系并利用对称性
2. **自友引理**：证明每个数必是自己的朋友，从而得到上界 $f(x)\le1/x$
3. **邻域不等式**：用 $y=x+\varepsilon$ 导出下界 $f(x)\ge1/x$
4. **夹逼定理**：上下界重合得到唯一解

## 参考
- IMO 2022 Official Solutions
- AoPS Community
- Evan Chen''s Solution Notes
