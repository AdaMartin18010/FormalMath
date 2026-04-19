---
msc_primary: 00A99
习题编号: ANA-133
学科: 实分析
知识点: Fourier分析-Poisson求和公式
难度: ⭐⭐⭐⭐
预计时间: 35分钟
---

# Poisson求和公式

## 题目

**(a)** 证明Poisson求和公式：对 $f \in \mathcal{S}(\mathbb{R})$，
$$\sum_{n=-\infty}^{\infty} f(n) = \sum_{k=-\infty}^{\infty} \hat{f}(k)$$

**(b)** 用Poisson求和公式证明 $\sum_{n=1}^{\infty} \frac{1}{n^2} = \frac{\pi^2}{6}$。

**(c)** 证明Jacobi theta函数的函数方程：
$$\sum_{n=-\infty}^{\infty} e^{-\pi n^2 t} = \frac{1}{\sqrt{t}} \sum_{n=-\infty}^{\infty} e^{-\pi n^2/t}, \quad t > 0$$

## 解答

### (a) Poisson求和公式

**证明：**

设 $F(x) = \sum_{n \in \mathbb{Z}} f(x+n)$，是1-周期函数。

Fourier系数：
$$\hat{F}(k) = \int_0^1 F(x) e^{-2\pi i k x} dx = \sum_n \int_0^1 f(x+n) e^{-2\pi i k x} dx$$

$$= \sum_n \int_n^{n+1} f(y) e^{-2\pi i k(y-n)} dy = \int_{-\infty}^{\infty} f(y) e^{-2\pi i k y} dy = \hat{f}(k)$$

Fourier级数：$F(x) = \sum_k \hat{f}(k) e^{2\pi i k x}$。

取 $x = 0$：$\sum_n f(n) = \sum_k \hat{f}(k)$。$\square$

### (b) 计算 $\zeta(2)$

**证明：**

取 $f(x) = e^{-2\pi t|x|}$，$t > 0$。

Fourier变换：
$$\hat{f}(\xi) = \frac{1}{\pi} \frac{t}{t^2 + \xi^2}$$

Poisson求和：
$$1 + 2\sum_{n=1}^{\infty} e^{-2\pi t n} = \frac{1}{\pi t} + \frac{2}{\pi} \sum_{k=1}^{\infty} \frac{t}{t^2 + k^2}$$

左边：$1 + \frac{2e^{-2\pi t}}{1 - e^{-2\pi t}} = \coth(\pi t)$。

展开右边为 $t$ 的级数，比较 $t$ 的一次项：
$$\frac{\pi^2}{3} - 8\pi^2 \sum_{k=1}^{\infty} \int_0^{\infty} e^{-2\pi t k} t dt = \frac{\pi^2}{3} - 2\sum_{k=1}^{\infty} \frac{1}{k^2}$$

由此得 $\sum_{n=1}^{\infty} \frac{1}{n^2} = \frac{\pi^2}{6}$。$\square$

### (c) Theta函数方程

**证明：**

取 $f(x) = e^{-\pi t x^2}$。

Fourier变换：$\hat{f}(\xi) = t^{-1/2} e^{-\pi \xi^2/t}$。

Poisson求和：
$$\sum_n e^{-\pi t n^2} = \sum_k t^{-1/2} e^{-\pi k^2/t} = t^{-1/2} \sum_k e^{-\pi k^2/t}$$
$\square$
