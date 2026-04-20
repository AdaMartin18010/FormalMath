---
msc_primary: 00A07
msc_secondary:
  - 00A99
  - 28A35
---

# 常见错误: 误用Fubini定理

## 所属领域

分析

## 错误描述

Fubini定理是重积分计算中最重要的工具之一，它允许我们将二重积分化为累次积分。然而，初学者常常忽略其前提条件——**函数绝对可积**，直接对非绝对可积的函数交换积分顺序，从而得到荒谬的结论（如 $\int_0^1 \int_0^1 f \neq \int_0^1 \int_0^1 f$ 或甚至得到 $0 = 1$ 的"证明"）。

### 正确陈述

**Fubini定理**：设 $(X, \mathcal{A}, \mu)$ 和 $(Y, \mathcal{B}, \nu)$ 是 $\sigma$-有限测度空间，$f: X \times Y \to \mathbb{R}$ 是 $\mathcal{A} \otimes \mathcal{B}$-可测函数。若
$$\int_{X \times Y} |f(x,y)|\, d(\mu \times \nu) < \infty$$
则 $f \in L^1(X \times Y)$，且
$$\int_{X \times Y} f\, d(\mu \times \nu) = \int_X \left(\int_Y f(x,y)\, d\nu(y)\right) d\mu(x) = \int_Y \left(\int_X f(x,y)\, d\mu(x)\right) d\nu(y)$$

**Tonelli定理**：若 $f \geq 0$ 可测（不必可积），则上述等式恒成立（可能为 $+\infty$）。

## 正确理解

### 为什么需要绝对可积？

直观上，Fubini定理要求"累次积分的绝对值之和有限"，即
$$\int_X \int_Y |f(x,y)|\, d\nu(y)\, d\mu(x) < \infty$$

这保证了函数在乘积空间上的"总质量"有限，积分顺序的交换才不会改变结果。如果 $f$ 变号剧烈且正负部分都发散，交换积分顺序可能分别"收敛"到不同的值。

### 实用判断流程

```
需要交换积分顺序?
├─ f ≥ 0 ? → 用Tonelli定理，自由交换
└─ f 变号 ?
   ├─ 先验证 ∫∫|f| < ∞ ? → 用Fubini定理
   └─ ∫∫|f| = ∞ ? → Fubini不适用！可能得到不同结果
```

### 与累次极限的关系

Fubini定理失败的本质与累次极限不可交换类似：
$$\lim_{m \to \infty} \lim_{n \to \infty} a_{m,n} \neq \lim_{n \to \infty} \lim_{m \to \infty} a_{m,n}$$
积分是极限过程，二重积分的两个积分顺序对应两种不同的累次极限。

## 反例

### 反例1：经典Sierpiński型反例

定义 $f: [0,1] \times [0,1] \to \mathbb{R}$：
$$f(x,y) = \frac{x^2 - y^2}{(x^2 + y^2)^2}$$

**计算第一个累次积分**：
$$\int_0^1 \left(\int_0^1 \frac{x^2 - y^2}{(x^2 + y^2)^2}\, dy\right) dx$$

内层积分：令 $y = x \tan \theta$，$dy = x \sec^2 \theta\, d\theta$
$$\int_0^1 \frac{x^2 - y^2}{(x^2 + y^2)^2}\, dy = \left[\frac{y}{x^2 + y^2}\right]_0^1 = \frac{1}{1 + x^2}$$

于是
$$\int_0^1 \frac{1}{1+x^2}\, dx = \arctan(1) = \frac{\pi}{4}$$

**计算第二个累次积分**：
由对称性（或直接计算），
$$\int_0^1 \left(\int_0^1 \frac{x^2 - y^2}{(x^2 + y^2)^2}\, dx\right) dy = -\frac{\pi}{4}$$

**结论**：
$$\int_0^1 \int_0^1 f(x,y)\, dy\, dx = \frac{\pi}{4} \neq -\frac{\pi}{4} = \int_0^1 \int_0^1 f(x,y)\, dx\, dy$$

**验证绝对不可积**：
$$\int_0^1 \int_0^1 \left|\frac{x^2 - y^2}{(x^2 + y^2)^2}\right| dx\, dy = +\infty$$

因为在原点附近，$|x^2 - y^2| \approx r^2 |\cos^2\theta - \sin^2\theta| = r^2 |\cos 2\theta|$，而 $(x^2 + y^2)^2 = r^4$，被积函数 $\sim \frac{1}{r^2}$，在极坐标下
$$\int_0^{\pi/2} \int_0^\varepsilon \frac{|\cos 2\theta|}{r^2} \cdot r\, dr\, d\theta = \int_0^{\pi/2} |\cos 2\theta|\, d\theta \cdot \int_0^\varepsilon \frac{dr}{r} = +\infty$$

### 反例2：离散化版本

考虑数列 $a_{m,n}$ 满足：

- $a_{m,n} = 1$ 若 $m = n$
- $a_{m,n} = -1$ 若 $m = n + 1$
- $a_{m,n} = 0$ 其他

则
$$\sum_{m=1}^\infty \sum_{n=1}^\infty a_{m,n} = \sum_{m=1}^\infty 0 = 0$$
$$\sum_{n=1}^\infty \sum_{m=1}^\infty a_{m,n} = 1 + \sum_{n=1}^\infty 0 = 1$$

这个离散版本清楚地展示了：当 $\sum_{m,n} |a_{m,n}| = \infty$ 时，求和顺序至关重要。

### 反例3：条件收敛的反常积分

$$\int_0^\infty \frac{\sin x}{x}\, dx = \frac{\pi}{2}$$

但若试图用Fubini定理于
$$\frac{\sin x}{x} = \int_0^1 \cos(xt)\, dt$$

得到
$$\int_0^\infty \frac{\sin x}{x}\, dx = \int_0^\infty \int_0^1 \cos(xt)\, dt\, dx \stackrel{?}{=} \int_0^1 \int_0^\infty \cos(xt)\, dx\, dt$$

右侧内层积分 $\int_0^\infty \cos(xt)\, dx$ 不绝对收敛，Fubini定理不适用。事实上右侧表达式无良好定义。

## 避免方法

1. **永远先验证绝对可积性**：在交换积分顺序前，先计算或估计 $\int \int |f|$。

2. **非负函数用Tonelli**：若 $f \geq 0$，放心使用Tonelli定理——即使结果为 $+\infty$，等式仍成立。

3. **条件收敛时格外谨慎**：对于条件收敛的积分（如 $\int \frac{\sin x}{x}\, dx$），任何积分顺序的交换都需要额外论证。

4. **使用控制收敛定理**：若找不到绝对可积性，但能找到控制函数 $g \in L^1$ 使得 $|f| \leq g$，则可用控制收敛定理配合截断论证。

5. **记住口诀**："Tonelli管非负，Fubini要绝对，条件交换须谨慎，否则结果会错位。"


## 相关定理与概念
- **Fubini定理**：$\sigma$-有限测度空间上的可测函数，若绝对可积，则重积分与累次积分相等
- **Tonelli定理**：非负可测函数的重积分与累次积分相等（允许 $+\infty$）
- **控制收敛定理（DCT）**： \to f$ a.e.，$|f_n| \leq g \in L^1$，则 $\int f_n \to \int f$
- **单调收敛定理（MCT）**： \leq f_n \nearrow f$，则 $\int f_n \nearrow \int f$

## 变体问题

### 变体1
设 (x,y) = \frac{x-y}{(x^2+y^2)^2}$ 在 $[0,1]\times[0,1]$ 上，验证两个累次积分不相等。

### 变体2
证明：若  \geq 0$ 可测，则 $\int_X \int_Y f \,dy\,dx = \int_Y \int_X f \,dx\,dy = \int_{X\times Y} f$（Tonelli定理）。
