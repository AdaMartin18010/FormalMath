---
number: "ANA-068"
category: 实分析
topic: 综合练习
difficulty: ⭐⭐⭐⭐
title: Fourier级数的收敛与发散
msc_primary: 00A99
keywords: [Fourier级数, Dirichlet核, Fejér核, 逐点收敛, Cesàro和]
prerequisites: [ANA-067, ANA-053]
source: 经典分析习题
---

## 题目

设 $f \in L^1[-\pi, \pi]$，Fourier系数 $\hat{f}(n) = \frac{1}{2\pi} \int_{-\pi}^{\pi} f(x) e^{-inx} dx$。

Fourier级数：$S_N f(x) = \sum_{n=-N}^{N} \hat{f}(n) e^{inx}$。

**(a)** 证明 $S_N f(x) = (f * D_N)(x)$，其中 $D_N(x) = \sum_{n=-N}^{N} e^{inx} = \frac{\sin((N+\frac{1}{2})x)}{\sin(x/2)}$（Dirichlet核）。

**(b)** 证明 $\{S_N f\}$ 不必在 $L^1$ 中收敛，即存在 $f \in L^1$ 使 $\|S_N f\|_{L^1} \to \infty$。

**(c)** 定义Cesàro和 $\sigma_N f = \frac{1}{N+1} \sum_{n=0}^{N} S_n f$。证明 $\sigma_N f = f * F_N$，其中 $F_N$ 是Fejér核，且 $\sigma_N f \to f$ 在 $L^1$ 中。

**(d)** 证明：若 $f$ 在 $x_0$ 可微，则 $S_N f(x_0) \to f(x_0)$。

## 详细解答

### (a) Dirichlet核与卷积

**证明：**

$$S_N f(x) = \sum_{n=-N}^{N} \hat{f}(n) e^{inx} = \sum_{n=-N}^{N} \left(\frac{1}{2\pi} \int_{-\pi}^{\pi} f(t) e^{-int} dt\right) e^{inx}$$

$$= \frac{1}{2\pi} \int_{-\pi}^{\pi} f(t) \sum_{n=-N}^{N} e^{in(x-t)} dt = (f * D_N)(x)$$

其中 $D_N(x-t) = \sum_{n=-N}^{N} e^{in(x-t)}$。

**计算Dirichlet核的闭式：**

$$D_N(x) = e^{-iNx} \sum_{n=0}^{2N} e^{inx} = e^{-iNx} \cdot \frac{1 - e^{i(2N+1)x}}{1 - e^{ix}}$$

$$= \frac{e^{-iNx} - e^{i(N+1)x}}{1 - e^{ix}} = \frac{e^{i(N+\frac{1}{2})x} - e^{-i(N+\frac{1}{2})x}}{e^{ix/2} - e^{-ix/2}} = \frac{\sin((N+\frac{1}{2})x)}{\sin(x/2)}$$

**证毕。**

### (b) $L^1$ 中的发散性

**证明思路：**

**步骤1：** 估计 $\|D_N\|_{L^1}$

$$\|D_N\|_{L^1} = \frac{1}{2\pi} \int_{-\pi}^{\pi} \left|\frac{\sin((N+\frac{1}{2})x)}{\sin(x/2)}\right| dx$$

对小的 $x$，$\sin(x/2) \approx x/2$，故：

$$\|D_N\|_{L^1} \approx \frac{2}{\pi} \int_{0}^{\pi} \frac{|\sin((N+\frac{1}{2})x)|}{x} dx = \frac{2}{\pi} \int_{0}^{(N+\frac{1}{2})\pi} \frac{|\sin u|}{u} du$$

$$\sim \frac{2}{\pi} \cdot \frac{2}{\pi} \ln N = \frac{4}{\pi^2} \ln N \to \infty$$

（更精确地，$\|D_N\|_{L^1} \sim \frac{4}{\pi^2} \ln N$）

**步骤2：** 一致有界原理

算子 $T_N: L^1 \to L^1$，$T_N f = S_N f = f * D_N$。

若 $\sup_N \|T_N\| < \infty$，则Fourier级数在 $L^1$ 中收敛。

但 $\|T_N\| = \|D_N\|_{L^1} \to \infty$。

由共鸣定理，存在 $f \in L^1$ 使 $\|S_N f\|_{L^1} \to \infty$。

**证毕。**

### (c) Fejér核与Cesàro收敛

**证明：**

**步骤1：** Fejér核的定义

$$\sigma_N f = \frac{1}{N+1} \sum_{n=0}^{N} S_n f = f * \left(\frac{1}{N+1} \sum_{n=0}^{N} D_n\right) = f * F_N$$

其中 $F_N = \frac{1}{N+1} \sum_{n=0}^{N} D_n$。

**步骤2：** Fejér核的闭式

$$F_N(x) = \frac{1}{N+1} \cdot \frac{\sin^2((N+1)x/2)}{\sin^2(x/2)} \geq 0$$

（非负性是成功的关键）

**步骤3：** Fejér核的性质

- $\frac{1}{2\pi} \int_{-\pi}^{\pi} F_N(x) dx = 1$
- 对任意 $\delta > 0$，$\int_{\delta \leq |x| \leq \pi} F_N(x) dx \to 0$（$N \to \infty$）

**步骤4：** $\sigma_N f \to f$ 在 $L^1$

这是标准的逼近恒等论证，类似于Weierstrass逼近定理。

对连续函数 $g$：
$$\|\sigma_N g - g\|_{L^1} \leq \int_{-\pi}^{\pi} |g(x-t) - g(x)| F_N(t) dt dx$$

交换积分，利用 $g$ 的一致连续性得收敛。

对一般 $f \in L^1$，用连续函数逼近。

**证毕。**

### (d) 可微点的收敛

**证明：**

设 $f$ 在 $x_0$ 可微。考虑：

$$S_N f(x_0) - f(x_0) = \frac{1}{2\pi} \int_{-\pi}^{\pi} (f(x_0-t) - f(x_0)) D_N(t) dt$$

令 $g(t) = \frac{f(x_0-t) - f(x_0)}{\sin(t/2)}$，在 $t=0$ 处补充定义 $g(0) = -2f'(x_0)$（利用可微性）。

可微性保证 $g$ 在 $t=0$ 附近可积（实际上是连续的）。

则：
$$S_N f(x_0) - f(x_0) = \frac{1}{2\pi} \int_{-\pi}^{\pi} g(t) \sin((N+\frac{1}{2})t) dt$$

这是 $g$ 的Fourier正弦系数，由Riemann-Lebesgue引理趋于0。

**证毕。**

## 证明技巧

1. **核函数方法：** 将部分和表示为卷积，分析核函数性质
2. **逼近恒等：** 良好核（非负、积分1、集中）保证收敛
3. **Riemann-Lebesgue引理：** $L^1$ 函数的Fourier系数趋于0

## 常见错误

| 错误 | 说明 |
|------|------|
| 认为$L^1$函数Fourier级数处处收敛 | 需要额外条件（如可微、有界变差） |
| 混淆Dirichlet核与Fejér核 | Dirichlet核变号，$L^1$范数无界；Fejér核非负 |
| 忘记验证Fejér核的积分条件 | 需要验证逼近恒等的三个条件 |

## 变式练习

**变式1：** 证明Dirichlet关于Fourier级数收敛的定理：有界变差函数Fourier级数处处收敛。

**变式2：** 构造连续函数使其Fourier级数在某点发散。

**变式3：** 证明Carleson定理：$L^2$函数的Fourier级数几乎处处收敛。
