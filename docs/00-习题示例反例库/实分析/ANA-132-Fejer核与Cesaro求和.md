---
习题编号: ANA-132
学科: 实分析
知识点: Fourier分析-Fejer核
难度: ⭐⭐⭐
预计时间: 25分钟
---

# Fejér核与Cesàro求和

## 题目

Fourier级数的部分和 $S_N f(x) = \sum_{n=-N}^{N} \hat{f}(n) e^{inx}$。

定义Cesàro平均：$\sigma_N f(x) = \frac{1}{N+1} \sum_{k=0}^{N} S_k f(x)$

**(a)** 证明Fejér核表示：
$$\sigma_N f(x) = (f * F_N)(x) = \frac{1}{2\pi} \int_{-\pi}^{\pi} f(x-y) F_N(y) dy$$
其中 $F_N(x) = \frac{1}{N+1} \frac{\sin^2((N+1)x/2)}{\sin^2(x/2)}$。

**(b)** 证明Fejér核性质：
- $F_N(x) \geq 0$
- $\frac{1}{2\pi} \int_{-\pi}^{\pi} F_N(x) dx = 1$
- 对所有 $\delta > 0$，$\int_{\delta \leq |x| \leq \pi} F_N(x) dx \to 0$（$N \to \infty$）

**(c)** 证明Fejér定理：若 $f \in C([-\pi, \pi])$ 且 $f(-\pi) = f(\pi)$，则 $\sigma_N f \to f$ 一致收敛。

## 解答

### (a) Fejér核公式

**证明：**

$$\sigma_N f = \frac{1}{N+1} \sum_{k=0}^N \sum_{n=-k}^k \hat{f}(n) e^{inx} = \sum_{n=-N}^N \left(1 - \frac{|n|}{N+1}\right) \hat{f}(n) e^{inx}$$

定义 $F_N$ 使 $\hat{F}_N(n) = 1 - \frac{|n|}{N+1}$（$|n| \leq N$），0（其他）。

$$F_N(x) = \sum_{n=-N}^N \left(1 - \frac{|n|}{N+1}\right) e^{inx}$$

计算：
$$F_N(x) = \frac{1}{N+1} \left|\sum_{n=0}^N e^{inx}\right|^2 = \frac{1}{N+1} \left|\frac{e^{i(N+1)x} - 1}{e^{ix} - 1}\right|^2$$

$$= \frac{1}{N+1} \frac{\sin^2((N+1)x/2)}{\sin^2(x/2)}$$
$\square$

### (b) 核性质

**证明：**

**非负性**：由公式显然。

**积分归一**：
$$\frac{1}{2\pi} \int F_N = \hat{F}_N(0) = 1$$

**集中性**：对 $|x| \geq \delta$，$\sin^2(x/2) \geq \sin^2(\delta/2) > 0$。

$$0 \leq F_N(x) \leq \frac{1}{(N+1)\sin^2(\delta/2)} \to 0$$

因此 $\int_{\delta \leq |x| \leq \pi} F_N \leq 2\pi \cdot \frac{C}{N+1} \to 0$。$\square$

### (c) Fejér定理

**证明：**

$$(f * F_N)(x) - f(x) = \frac{1}{2\pi} \int_{-\pi}^{\pi} [f(x-y) - f(x)] F_N(y) dy$$

由 $f$ 在紧集一致连续：给定 $\varepsilon > 0$，存在 $\delta > 0$ 使 $|y| < \delta \Rightarrow |f(x-y) - f(x)| < \varepsilon$。

分裂积分：
$$\leq \frac{1}{2\pi} \int_{|y|<\delta} \varepsilon F_N(y) dy + \frac{2\|f\|_\infty}{2\pi} \int_{\delta \leq |y| \leq \pi} F_N(y) dy$$

$$\leq \varepsilon + \frac{\|f\|_\infty}{\pi} \cdot o(1) < 2\varepsilon$$

对足够大的$N$，一致于$x$。$\square$
