---
number: "ANA-053"
category: 实分析
topic: 函数序列与级数
difficulty: ⭐⭐
title: Weierstrass M-判别法的应用
keywords: [Weierstrass判别法, 函数级数, 一致收敛, 优级数]
prerequisites: [ANA-018, ANA-052]
source: 经典分析习题
---

## 题目

**(a)** 用Weierstrass M-判别法证明 $\sum_{n=1}^{\infty} \frac{\sin(nx)}{n^2}$ 在 $\mathbb{R}$ 上一致收敛。

**(b)** 证明 $\sum_{n=1}^{\infty} \frac{x}{n(1+nx^2)}$ 在 $\mathbb{R}$ 上一致收敛。

**(c)** 证明 $\sum_{n=1}^{\infty} \frac{(-1)^n}{n+x^2}$ 在 $\mathbb{R}$ 上一致收敛（注意：不能用M-判别法的直接形式）。

## 详细解答

### (a) 正弦级数的一致收敛

**证明：**

对于所有 $x \in \mathbb{R}$：
$$\left|\frac{\sin(nx)}{n^2}\right| \leq \frac{1}{n^2}$$

取 $M_n = \frac{1}{n^2}$，则 $\sum M_n = \sum \frac{1}{n^2} < \infty$（p-级数，p=2>1）。

由Weierstrass M-判别法，原级数在 $\mathbb{R}$ 上一致收敛。

**证毕。**

### (b) 有理函数级数

**证明：**

需要找到与 $x$ 无关的上界。

对于 $f_n(x) = \frac{x}{n(1+nx^2)}$，求其在 $\mathbb{R}$ 上的最大值。

求导（对固定的 $n$）：
$$f_n'(x) = \frac{1}{n} \cdot \frac{(1+nx^2) - x \cdot 2nx}{(1+nx^2)^2} = \frac{1-nx^2}{n(1+nx^2)^2}$$

令 $f_n'(x) = 0$，得 $x = \pm \frac{1}{\sqrt{n}}$。

最大值为：
$$f_n\left(\frac{1}{\sqrt{n}}\right) = \frac{1/\sqrt{n}}{n(1+n \cdot \frac{1}{n})} = \frac{1/\sqrt{n}}{2n} = \frac{1}{2n^{3/2}}$$

因此：
$$|f_n(x)| \leq \frac{1}{2n^{3/2}}$$

取 $M_n = \frac{1}{2n^{3/2}}$，则 $\sum M_n$ 收敛（p=3/2 > 1）。

由M-判别法，一致收敛。

**证毕。**

### (c) 交错级数的一致收敛

**分析：** 直接用M-判别法需要 $\sum \frac{1}{n}$ 收敛，这不成立。改用**交错级数判别法+余项估计**。

**证明：**

对于固定 $x$，这是Leibniz型交错级数：
- $a_n(x) = \frac{1}{n+x^2}$ 关于 $n$ 单调递减
- $\lim_{n \to \infty} a_n(x) = 0$

由Leibniz判别法，级数收敛。且余项估计：
$$\left|\sum_{k=n+1}^{\infty} \frac{(-1)^k}{k+x^2}\right| \leq \frac{1}{(n+1)+x^2} \leq \frac{1}{n+1}$$

由于 $\frac{1}{n+1} \to 0$ 与 $x$ 无关，故一致收敛。

**证毕。**

## 证明技巧

1. **求函数最值：** 对含参函数求上界，常用求导法
2. **M-判别法失效时的替代方案：**
   - Abel判别法、Dirichlet判别法
   - 交错级数的余项估计
3. **一致收敛的传递：** 一致收敛级数的和函数继承连续性

## 常见错误

| 错误 | 说明 |
|------|------|
| 在(b)中直接取 $M_n = \frac{1}{n}$ | 忽略 $x$ 的影响，上界不紧 |
| 在(c)中强行用M-判别法 | $\sum \frac{1}{n}$ 发散，不适用 |
| 余项估计时忽略"与$x$无关" | 一致收敛要求上界不依赖于$x$ |

## 变式练习

**变式1：** 证明 $\sum_{n=1}^{\infty} \frac{x^n}{n^2}$ 在 $[-1,1]$ 上一致收敛。

**变式2：** 研究 $\sum_{n=1}^{\infty} \frac{(-1)^n x^n}{n}$ 在 $[0,1]$ 上的一致收敛性。

**变式3：** 证明 $\sum_{n=1}^{\infty} \frac{\cos(nx)}{n^p}$ 对 $p > 1$ 在 $\mathbb{R}$ 上一致收敛。
