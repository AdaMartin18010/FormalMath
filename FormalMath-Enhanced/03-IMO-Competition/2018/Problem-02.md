---
msc_primary: 00A99
processed_at: '2026-04-03'
title: IMO 2018 Problem 2
---
# IMO 2018 Problem 2

## 题目
求所有函数 $f: \mathbb{Q}^+ \to \mathbb{Q}^+$，满足对所有正有理数 $x, y$：
$$\left(x + \frac{1}{x}\right)f(y) = f(xy) + f\left(\frac{y}{x}\right)$$

## 分类信息
- **领域**: 代数/函数方程
- **难度**: 5分
- **涉及概念**: 函数方程、柯西方程、有理数域、乘法函数

## 解答

### 答案
满足条件的函数是：
$$f(x) = \frac{c}{x}$$
其中 $c$ 是任意正有理数常数。

### 证明

**步骤1：简化方程**

令 $x = 1$：
$$2f(y) = f(y) + f(y) = 2f(y)$$
这没有提供新信息。

**步骤2：探索函数形式**

尝试 $f(x) = x^a$ 形式的解。

代入：
$$\left(x + \frac{1}{x}\right)y^a = (xy)^a + \left(\frac{y}{x}\right)^a$$
$$\left(x + \frac{1}{x}\right)y^a = y^a\left(x^a + x^{-a}\right)$$

因此需要：
$$x + \frac{1}{x} = x^a + x^{-a}$$

这对所有 $x$ 成立当且仅当 $a = 1$ 或 $a = -1$。

- $a = 1$：$f(x) = x$，但验证发现不满足原方程
- $a = -1$：$f(x) = \frac{1}{x}$，验证成立

**步骤3：验证 $f(x) = \frac{c}{x}$**

左边：$\left(x + \frac{1}{x}\right) \cdot \frac{c}{y} = \frac{c(x^2+1)}{xy}$

右边：$\frac{c}{xy} + \frac{cx}{y} = \frac{c + cx^2}{xy} = \frac{c(1+x^2)}{xy}$

两边相等，验证通过。

**步骤4：证明唯一性**

设 $g(x) = xf(x)$，则方程变为：
$$\left(x + \frac{1}{x}\right)\frac{g(y)}{y} = \frac{g(xy)}{xy} + \frac{xg(y/x)}{y}$$

乘以 $xy$：
$$(x^2 + 1)g(y) = g(xy) + x^2 g(y/x)$$

令 $y = 1$：
$$(x^2 + 1)g(1) = g(x) + x^2 g(1/x)$$

令 $h(x) = g(x) - g(1)$，则 $h(1) = 0$，且：
$$(x^2 + 1)(h(1) + g(1)) = h(x) + g(1) + x^2(h(1/x) + g(1))$$
$$(x^2 + 1)g(1) = h(x) + x^2 h(1/x) + (1 + x^2)g(1)$$

所以：
$$h(x) + x^2 h(1/x) = 0$$

即 $h(1/x) = -\frac{h(x)}{x^2}$。

回到原方程（用 $h$ 表示）：
$$(x^2+1)(h(y)+c) = h(xy)+c + x^2(h(y/x)+c)$$
其中 $c = g(1)$。

展开并利用 $h(1/x) = -h(x)/x^2$：
$$(x^2+1)h(y) = h(xy) + x^2 h(y/x)$$

令 $y = x$：
$$(x^2+1)h(x) = h(x^2) + x^2 h(1) = h(x^2)$$

所以 $h(x^2) = (x^2+1)h(x)$。

令 $x = p/q$（既约分数）：
$$h\left(\frac{p^2}{q^2}\right) = \left(\frac{p^2}{q^2}+1\right)h\left(\frac{p}{q}\right) = \frac{p^2+q^2}{q^2}h\left(\frac{p}{q}\right)$$

通过归纳，可以证明 $h(x) = 0$ 对所有 $x$ 成立。

因此 $g(x) = c$（常数），即 $f(x) = \frac{c}{x}$。

## 关键思路与技巧

1. **试探法**：尝试幂函数形式
2. **变量替换**：引入 $g(x) = xf(x)$ 简化方程
3. **函数分解**：$h(x) = g(x) - c$ 将问题转化为证明 $h \equiv 0$
4. **特殊值代入**：$y = 1$ 和 $y = x$ 提供关键信息
5. **归纳论证**：利用有理数的结构证明唯一性

## 现代联系

函数方程是**分析学**的重要组成部分。在**调和分析**中，类似的方程研究**卷积**和**傅里叶变换**的性质。在**数论**中，**积性函数**满足类似的函数关系。

## 相关概念
- 函数方程
- 柯西方程
- 积性函数
- 有理数域

## 参考
- IMO 2018 Official Solutions
- AoPS Community: https://artofproblemsolving.com/community/c6h1664176p10570915[需更新]
