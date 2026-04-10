---
exercise_id: ANA-076
title: Fourier级数的点态收敛与一致收敛
difficulty: ⭐⭐⭐⭐
topics: [Fourier级数, Dirichlet核, Fejér核, 收敛性]
created: 2026-04-10
---

## 题目

设 $f$ 是 $\mathbb{R}$ 上的 $2\pi$-周期连续函数，其Fourier级数为：

$$f(x) \sim \frac{a_0}{2} + \sum_{n=1}^{\infty}(a_n\cos nx + b_n\sin nx)$$

(1) 设 $S_N(f;x) = \frac{a_0}{2} + \sum_{n=1}^{N}(a_n\cos nx + b_n\sin nx)$ 是部分和，用Dirichlet核表示 $S_N(f;x)$；

(2) 证明若 $f \in C^{0,\alpha}$（Hölder连续，$0 < \alpha \leq 1$），则 $S_N(f) \rightrightarrows f$ 一致收敛；

(3) 构造一个连续函数使其Fourier级数在某点发散（描述性构造，无需具体函数）。

## 详细解答

### (1) Dirichlet核表示

Fourier系数：

$$a_n = \frac{1}{\pi}\int_{-\pi}^{\pi} f(t)\cos(nt)dt, \quad b_n = \frac{1}{\pi}\int_{-\pi}^{\pi} f(t)\sin(nt)dt$$

部分和：

$$S_N(f;x) = \frac{1}{\pi}\int_{-\pi}^{\pi} f(t)\left[\frac{1}{2} + \sum_{n=1}^{N}\cos n(x-t)\right]dt$$

利用恒等式 $\frac{1}{2} + \sum_{n=1}^{N}\cos n\theta = \frac{\sin((N+\frac{1}{2})\theta)}{2\sin(\frac{\theta}{2})}$：

$$S_N(f;x) = \frac{1}{\pi}\int_{-\pi}^{\pi} f(t) D_N(x-t) dt = (f * D_N)(x)$$

其中 **Dirichlet核**：

$$D_N(\theta) = \frac{\sin((N+\frac{1}{2})\theta)}{2\sin(\frac{\theta}{2})}$$

性质：$\int_{-\pi}^{\pi} D_N(\theta)d\theta = \pi$。

### (2) Hölder连续函数的一致收敛

**定理**：若 $f \in C^{0,\alpha}$，即 $|f(x)-f(y)| \leq L|x-y|^\alpha$，则 $S_N(f) \rightrightarrows f$。

**证明思路**：

$$S_N(f;x) - f(x) = \frac{1}{\pi}\int_{-\pi}^{\pi}[f(x-t)-f(x)]D_N(t)dt$$

利用 $D_N$ 的振荡性质。

**详细证明**：

设 $\delta \in (0, \pi)$ 待定，拆分积分：

$$= \frac{1}{\pi}\int_{|t|<\delta}[f(x-t)-f(x)]D_N(t)dt + \frac{1}{\pi}\int_{\delta<|t|<\pi}[f(x-t)-f(x)]D_N(t)dt$$

**第一项估计**：利用Hölder条件 $|f(x-t)-f(x)| \leq L|t|^\alpha$：

$$\left|\int_{|t|<\delta}\right| \leq \frac{L}{\pi}\int_{|t|<\delta}|t|^\alpha \frac{1}{2|\sin(t/2)|}dt$$

对 $|t| < \delta$，$|\sin(t/2)| \approx |t|/2$，故：

$$\leq C L \int_0^{\delta} t^{\alpha-1}dt = \frac{CL}{\alpha}\delta^{\alpha}$$

**第二项估计**：利用 $|D_N(t)| \leq \frac{1}{2|\sin(t/2)|} \leq \frac{C'}{|t|}$ 对 $|t| \geq \delta$：

$$\left|\int_{\delta<|t|<\pi}\right| \leq \frac{2\|f\|_\infty}{\pi}\int_{\delta}^{\pi}|D_N(t)|dt$$

通过Dirichlet核的 $L^1$ 估计：$\int_{\delta}^{\pi}|D_N(t)|dt \leq C''\frac{\ln N}{N\delta}$（对于大的 $N$）。

实际上，利用振荡积分估计：

$$\int_{\delta}^{\pi}\frac{\sin((N+1/2)t)}{\sin(t/2)}dt = O\left(\frac{1}{N\delta}\right)$$

综合：选择 $\delta = N^{-\beta}$，$\beta = \frac{1}{1+\alpha}$，可得两项都趋于 $0$。

**结论**：$\|S_N(f) - f\|_\infty \to 0$。

### (3) 连续函数Fourier级数发散的例子

**Kolmogorov定理（1923）**：存在可积函数（甚至 $L^1$ 函数）其Fourier级数处处发散。

**Du Bois-Reymond（1876）**：存在连续函数其Fourier级数在某点发散。

**构造思路**（Fejér的构造）：

考虑三角多项式 $P_n(x) = \sum_{k=1}^{n}\frac{\sin kx}{k}$，这是有界的（一致有界）。

令 $Q_n(x) = \frac{1}{n}\sum_{k=1}^{n}P_k(x)$ 是Cesàro平均。

更精细的构造：令

$$f(x) = \sum_{n=1}^{\infty}\frac{1}{n^2}\sin(2^{n^3}x)$$

这是一个一致收敛的级数，定义连续函数。

通过适当选择，可以证明在某些点 $x$（如 $x = 0$ 附近的有理数倍），Fourier部分和 $S_N(f;x)$ 无界。

**Carleson定理（1966）**：若 $f \in L^2$，则其Fourier级数几乎处处收敛到 $f$。

这意味着连续函数（属于 $L^2$）的Fourier级数必几乎处处收敛，但可以在零测集上发散。

## 证明技巧

1. **核方法**：将部分和表示为卷积，分析核的性质
2. **局部化原理**：Fourier级数在某点的收敛性只依赖于函数在该点附近的性态
3. **振荡积分**：利用快速振荡产生的抵消效应

## 常见错误

| 错误类型 | 错误表现 | 正确做法 |
|---------|---------|---------|
| 混淆收敛性 | 认为连续函数的Fourier级数处处收敛 | 连续 $
Rightarrow$ a.e.收敛，但可有点发散 |
| Dirichlet核性质 | 认为 $D_N$ 是正核或有界 $L^1$ 范数 | $\|D_N\|_{L^1} \sim \ln N \to \infty$ |
| Cesàro平均 | 混淆Fourier部分和与Fejér平均 | Fejér核是正核，有更好的收敛性质 |

## 变式练习

**变式1（难度⭐⭐⭐）**：证明Fejér平均 $\sigma_N(f) = \frac{1}{N+1}\sum_{k=0}^{N}S_k(f)$ 对连续函数一致收敛到 $f$。

**变式2（难度⭐⭐⭐⭐）**：设 $f$ 是有界变差函数，证明其Fourier级数处处收敛。

**变式3（难度⭐⭐⭐⭐⭐）**：证明 $\sum_{n=2}^{\infty}\frac{\sin nx}{\ln n}$ 是某连续函数的Fourier级数，但在 $x=0$ 发散。
