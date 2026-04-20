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

---

## 解答

### (a) Poisson求和公式

**证明：**

设 $F(x) = \sum_{n \in \mathbb{Z}} f(x+n)$，是1-周期函数。

Fourier系数：
$$\hat{F}(k) = \int_0^1 F(x) e^{-2\pi i k x} dx = \sum_n \int_0^1 f(x+n) e^{-2\pi i k x} dx$$

$$= \sum_n \int_n^{n+1} f(y) e^{-2\pi i k(y-n)} dy = \int_{-\infty}^{\infty} f(y) e^{-2\pi i k y} dy = \hat{f}(k)$$

Fourier级数：$F(x) = \sum_k \hat{f}(k) e^{2\pi i k x}$。

取 $x = 0$：$\sum_n f(n) = \sum_k \hat{f}(k)$。$\square$

**详细解释**：

**步骤1：构造周期化函数**

$F(x) = \sum_{n \in \mathbb{Z}} f(x+n)$ 是以1为周期的函数，因为：
$$F(x+1) = \sum_n f(x+1+n) = \sum_m f(x+m) = F(x)$$

（变量替换 $m = n+1$）

**步骤2：计算Fourier系数**

$F$ 的Fourier系数定义为：
$$\hat{F}(k) = \int_0^1 F(x) e^{-2\pi i k x} dx$$

由于 $f \in \mathcal{S}(\mathbb{R})$（Schwartz函数），求和与积分可交换：
$$\hat{F}(k) = \sum_n \int_0^1 f(x+n) e^{-2\pi i k x} dx$$

令 $y = x + n$，则 $x = y - n$，$dx = dy$：
$$= \sum_n \int_n^{n+1} f(y) e^{-2\pi i k (y-n)} dy$$
$$= \sum_n e^{2\pi i k n} \int_n^{n+1} f(y) e^{-2\pi i k y} dy$$

由于 $e^{2\pi i k n} = 1$（$k, n \in \mathbb{Z}$）：
$$= \sum_n \int_n^{n+1} f(y) e^{-2\pi i k y} dy = \int_{-\infty}^{\infty} f(y) e^{-2\pi i k y} dy = \hat{f}(k)$$

**步骤3：Fourier展开与求值**

$F$ 是光滑周期函数，其Fourier级数逐点收敛：
$$F(x) = \sum_{k \in \mathbb{Z}} \hat{F}(k) e^{2\pi i k x} = \sum_{k \in \mathbb{Z}} \hat{f}(k) e^{2\pi i k x}$$

取 $x = 0$：
$$F(0) = \sum_n f(n) = \sum_k \hat{f}(k)$$

**条件说明**：$f \in \mathcal{S}(\mathbb{R})$ 保证了：
1. 求和 $\sum_n f(x+n)$ 绝对一致收敛
2. Fourier级数收敛到 $F(x)$
3. 积分与求和可交换

实际上，Poisson求和公式在更弱的条件下也成立（如 $f$ 有界变差且 $f, \hat{f}$ 绝对可积）。

---

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

**更清晰的证明**：取 $f(x) = \max(1 - |x|, 0)$（三角脉冲）或直接用 $f(x) = x^2$ 在 $[-1,1]$ 上的展开。

**标准方法**：取 $f(x) = e^{-\pi x^2 t}$，利用 $\hat{f}(\xi) = t^{-1/2} e^{-\pi \xi^2 / t}$（见(c)部分）。

另一种方法：考虑函数 $f(x) = x^2$ 在 $[-\pi, \pi]$ 上的Fourier级数，用Parseval恒等式：

$x^2 = \frac{\pi^2}{3} + 4 \sum_{n=1}^{\infty} \frac{(-1)^n}{n^2} \cos(nx)$

在 $x = \pi$：$\pi^2 = \frac{\pi^2}{3} + 4 \sum \frac{1}{n^2}$

$\sum \frac{1}{n^2} = \frac{\pi^2}{6}$。

---

### (c) Theta函数方程

**证明：**

取 $f(x) = e^{-\pi t x^2}$。

Fourier变换：$\hat{f}(\xi) = t^{-1/2} e^{-\pi \xi^2/t}$。

Poisson求和：
$$\sum_n e^{-\pi t n^2} = \sum_k t^{-1/2} e^{-\pi k^2/t} = t^{-1/2} \sum_k e^{-\pi k^2/t}$$
$\square$

**Fourier变换的计算**：

$$\hat{f}(\xi) = \int_{-\infty}^{\infty} e^{-\pi t x^2} e^{-2\pi i x \xi} dx$$

配方：
$$-\pi t x^2 - 2\pi i x \xi = -\pi t(x + i\xi/t)^2 - \pi \xi^2/t$$

因此：
$$\hat{f}(\xi) = e^{-\pi \xi^2/t} \int_{-\infty}^{\infty} e^{-\pi t(x + i\xi/t)^2} dx$$

由围道积分（将积分路径从实轴平移），得：
$$\int_{-\infty}^{\infty} e^{-\pi t(x + i\xi/t)^2} dx = \int_{-\infty}^{\infty} e^{-\pi t x^2} dx = t^{-1/2}$$

（利用 $\int_{-\infty}^{\infty} e^{-\pi x^2} dx = 1$）

**Theta函数**：
$$\vartheta(t) = \sum_{n=-\infty}^{\infty} e^{-\pi n^2 t}$$

函数方程表明：$\vartheta(t) = t^{-1/2} \vartheta(1/t)$。

**模形式联系**：这一函数方程是 Jacobi theta 函数是权 $1/2$ 模形式的体现。它在解析数论中至关重要，如用于证明 $\zeta$ 函数的函数方程。

---

## 应用与联系

### 在数论中的应用

Poisson求和公式是解析数论的核心工具：

1. **$\zeta$ 函数的函数方程**：通过 theta 函数的模变换推导
2. **圆法（Hardy-Littlewood）**：将加法问题转化为指数和
3. **格点问题**：计算区域内的整数点数目

### 在信号处理中的应用

Poisson求和公式连接了连续与离散：
- 采样定理的数学基础
- 周期延拓的频谱分析
- 混叠效应（aliasing）的数学描述

### 与不确定性原理

Poisson求和公式揭示了函数与其Fourier变换在整数点上的深刻联系。Heisenberg不确定性原理表明，$f$ 和 $\hat{f}$ 不能同时在整数点上"集中"。Poisson求和公式精确量化了这种权衡。
