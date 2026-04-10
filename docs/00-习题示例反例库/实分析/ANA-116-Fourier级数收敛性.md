---
习题编号: ANA-116
学科: 实分析
知识点: Fourier分析-级数收敛性
难度: ⭐⭐⭐
预计时间: 25分钟
---

# Fourier级数收敛性

## 题目

设 $f \in L^1([-\pi, \pi])$ 是 $2\pi$-周期函数，其Fourier系数定义为：
$$\hat{f}(n) = \frac{1}{2\pi} \int_{-\pi}^{\pi} f(x) e^{-inx} dx, \quad n \in \mathbb{Z}$$

**(a)** 证明：若 $f \in C^1([-\pi, \pi])$ 且 $f(-\pi) = f(\pi)$，则 $\hat{f}(n) = O(1/|n|)$ 当 $|n| \to \infty$。

**(b)** 设 $f(x) = |x|$ 于 $[-\pi, \pi]$，计算其Fourier级数，并讨论逐点收敛性。

**(c)** 证明Dirichlet核 $D_N(x) = \sum_{n=-N}^{N} e^{inx}$ 满足：
$$D_N(x) = \frac{\sin((N+\frac{1}{2})x)}{\sin(x/2)}$$

## 解答

### (a) 光滑函数的Fourier系数衰减

**证明：**

对 $n \neq 0$，分部积分：
$$\hat{f}(n) = \frac{1}{2\pi} \int_{-\pi}^{\pi} f(x) e^{-inx} dx$$

$$= \frac{1}{2\pi} \left[ f(x) \frac{e^{-inx}}{-in} \right]_{-\pi}^{\pi} + \frac{1}{2\pi in} \int_{-\pi}^{\pi} f'(x) e^{-inx} dx$$

由周期性条件 $f(-\pi) = f(\pi)$ 和 $e^{-in\pi} = e^{in\pi} = (-1)^n$：
$$\left[ f(x) \frac{e^{-inx}}{-in} \right]_{-\pi}^{\pi} = \frac{f(\pi)(-1)^n - f(-\pi)(-1)^n}{-in} = 0$$

因此：
$$\hat{f}(n) = \frac{1}{in} \widehat{f'}(n)$$

由Riemann-Lebesgue引理，$\widehat{f'}(n) \to 0$，且：
$$|\hat{f}(n)| \leq \frac{1}{|n|} \cdot \frac{1}{2\pi} \int_{-\pi}^{\pi} |f'(x)| dx = \frac{\|f'\|_{L^1}}{2\pi |n|}$$

故 $\hat{f}(n) = O(1/|n|)$。$\square$

### (b) 绝对值函数的Fourier级数

**解答：**

$f(x) = |x|$ 是偶函数，故 $\hat{f}(n) = \hat{f}(-n)$ 为实数。

**常数项：**
$$\hat{f}(0) = \frac{1}{2\pi} \int_{-\pi}^{\pi} |x| dx = \frac{1}{\pi} \int_0^{\pi} x dx = \frac{\pi}{2}$$

**余弦系数**（$n \geq 1$）：
$$\hat{f}(n) = \frac{1}{\pi} \int_0^{\pi} x \cos(nx) dx$$

分部积分：
$$= \frac{1}{\pi} \left[ \frac{x \sin(nx)}{n} \right]_0^{\pi} - \frac{1}{\pi} \int_0^{\pi} \frac{\sin(nx)}{n} dx$$

$$= 0 + \frac{1}{\pi n} \left[ \frac{\cos(nx)}{n} \right]_0^{\pi} = \frac{(-1)^n - 1}{\pi n^2}$$

因此：
$$\hat{f}(n) = \begin{cases} 0 & n \text{ 偶数}, n \neq 0 \\ -\frac{2}{\pi n^2} & n \text{ 奇数} \end{cases}$$

**Fourier级数：**
$$|x| = \frac{\pi}{2} - \frac{4}{\pi} \sum_{k=0}^{\infty} \frac{\cos((2k+1)x)}{(2k+1)^2}$$

**收敛性**：由Weierstrass M-判别法，级数一致收敛。$\square$

### (c) Dirichlet核公式

**证明：**

$$D_N(x) = \sum_{n=-N}^{N} e^{inx} = e^{-iNx} \sum_{n=0}^{2N} e^{inx} = e^{-iNx} \cdot \frac{1 - e^{i(2N+1)x}}{1 - e^{ix}}$$

（等比级数求和，$x \neq 0$）

$$= \frac{e^{-iNx} - e^{i(N+1)x}}{1 - e^{ix}} = \frac{e^{i(N+\frac{1}{2})x} - e^{-i(N+\frac{1}{2})x}}{e^{ix/2} - e^{-ix/2}} \cdot \frac{e^{-i(N+\frac{1}{2})x}}{e^{-ix/2}}$$

$$= \frac{2i\sin((N+\frac{1}{2})x)}{2i\sin(x/2)} = \frac{\sin((N+\frac{1}{2})x)}{\sin(x/2)}$$

$x = 0$ 时，$D_N(0) = 2N+1$，公式也成立。$\square$

## 证明技巧

1. **分部积分**：光滑性转化为系数衰减
2. **对称性利用**：偶函数/奇函数简化计算
3. **等比级数**：Dirichlet核的闭式表达

## 常见错误

- ❌ 忽略周期边界条件在分部积分中的作用
- ❌ 混淆逐点收敛与一致收敛的条件
- ❌ Dirichlet核的相位计算错误

## 变式练习

**变式1：** 证明 $f \in C^k$ 则 $\hat{f}(n) = O(1/|n|^k)$。

**变式2：** 计算 $f(x) = x$ 于 $(-\pi, \pi)$ 的Fourier级数。
