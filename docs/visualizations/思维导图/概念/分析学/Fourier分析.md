# Fourier分析 (Fourier Analysis)

## 中心概念精确定义

**Fourier分析**是将函数分解为简谐振动（正弦/余弦）叠加的数学理论，是信号处理、偏微分方程和量子力学的核心工具。

> **Fourier级数**：设 $f \in L^1[-\pi, \pi]$ 是 $2\pi$ 周期函数，其Fourier级数为：
> $$f(x) \sim \frac{a_0}{2} + \sum_{n=1}^{\infty} (a_n \cos nx + b_n \sin nx) = \sum_{n=-\infty}^{\infty} c_n e^{inx}$$
> 
> 其中系数：$a_n = \frac{1}{\pi}\int_{-\pi}^{\pi} f(x)\cos nx\,dx$，$b_n = \frac{1}{\pi}\int_{-\pi}^{\pi} f(x)\sin nx\,dx$，$c_n = \frac{1}{2\pi}\int_{-\pi}^{\pi} f(x)e^{-inx}\,dx$

> **Fourier变换**：对 $f \in L^1(\mathbb{R})$，定义：
> $$\hat{f}(\xi) = \int_{-\infty}^{\infty} f(x) e^{-2\pi i x \xi} dx$$

---

## Mermaid 思维导图

```mermaid
mindmap
  root((Fourier分析<br/>Fourier Analysis))
    Fourier级数
      定义
        周期函数展开
        正交基{e^{inx}}
      收敛性
        点态收敛
        一致收敛
        L²收敛
      应用
        热方程
        波动方程
        信号分析
    Fourier变换
      定义
        非周期函数
        频域表示
      性质
        线性
        平移⇔调制
        卷积⇔乘积
      反演
        反变换公式
        L¹+L²理论
    卷积
      定义
        (f∗g)(x)=∫f(y)g(x-y)dy
        平移平均
      性质
        交换律
        结合律
        分配律
      应用
        光滑化
        逼近
        滤波器
    Plancherel定理
      L²等距
        ||f̂||₂=||f||₂
        能量守恒
      内积保持
        ⟨f̂,ĝ⟩=⟨f,g⟩
      应用
        不确定性原理
        信号处理
    分布理论
      广义函数
        Dirac delta
        弱收敛
      变换
        δ̂=1
        1̂=δ
      应用
        微分方程
        物理
    离散Fourier
      DFT
        有限和
        FFT算法
      应用
        数字信号
        图像处理
        多项式乘法
```

---

## 核心要素详解

### 1. Fourier级数收敛理论

**Dirichlet 定理**：若 $f$ 在 $[-\pi, \pi]$ 上分段光滑，则Fourier级数在每点 $x$ 收敛到：
$$\frac{f(x^+) + f(x^-)}{2}$$

在连续点收敛到 $f(x)$。

**Carleson 定理**（1966）：若 $f \in L^2[-\pi, \pi]$，则Fourier级数几乎处处收敛到 $f$。

**L² 收敛（Parseval）**：
$$\|f - S_N f\|_{L^2} \to 0, \quad \text{其中 } S_N f = \sum_{|n| \leq N} c_n e^{inx}$$

### 2. Fourier变换基本性质

| 性质 | 时域 | 频域 |
|------|------|------|
| 线性 | $af + bg$ | $a\hat{f} + b\hat{g}$ |
| 平移 | $f(x-a)$ | $e^{-2\pi i a \xi}\hat{f}(\xi)$ |
| 调制 | $e^{2\pi i a x}f(x)$ | $\hat{f}(\xi - a)$ |
| 伸缩 | $f(ax)$ | $\frac{1}{|a|}\hat{f}(\xi/a)$ |
| 微分 | $f'(x)$ | $2\pi i \xi \hat{f}(\xi)$ |
| 乘 $x$ | $xf(x)$ | $\frac{i}{2\pi}\hat{f}'(\xi)$ |
| 卷积 | $f * g$ | $\hat{f} \cdot \hat{g}$ |
| 乘积 | $f \cdot g$ | $\hat{f} * \hat{g}$ |

### 3. 卷积 (Convolution)

**定义**：$(f * g)(x) = \int_{-\infty}^{\infty} f(y)g(x-y)\,dy$

**关键性质**：
- **交换律**：$f * g = g * f$
- **结合律**：$(f * g) * h = f * (g * h)$
- **卷积定理**：$\widehat{f * g} = \hat{f} \cdot \hat{g}$

**磨光算子**：令 $\phi_\varepsilon(x) = \frac{1}{\varepsilon}\phi(x/\varepsilon)$，则 $f * \phi_\varepsilon \to f$ 当 $\varepsilon \to 0$。

**物理解释**：卷积是加权平均，用于信号滤波和平滑。

### 4. Plancherel 定理

**定理**：Fourier变换是 $L^2(\mathbb{R})$ 上的酉算子（等距同构）：
$$\|\hat{f}\|_{L^2} = \|f\|_{L^2}$$

等价形式（Parseval等式）：
$$\int_{-\infty}^{\infty} f(x)\overline{g(x)}\,dx = \int_{-\infty}^{\infty} \hat{f}(\xi)\overline{\hat{g}(\xi)}\,d\xi$$

**意义**：Fourier变换保持能量（$L^2$范数），是信号处理的理论基础。

### 5. Heisenberg 不确定性原理

**定理**：对 $f \in L^2(\mathbb{R})$，$\|f\|_2 = 1$，有：
$$\left(\int x^2 |f(x)|^2 dx\right)\left(\int \xi^2 |\hat{f}(\xi)|^2 d\xi\right) \geq \frac{1}{16\pi^2}$$

**物理解释**：信号在时域和频域的"展宽"不能同时任意小。位置越精确，动量越不确定（量子力学）。

### 6. Poisson 求和公式

**定理**：对适当光滑的 $f$：
$$\sum_{n=-\infty}^{\infty} f(n) = \sum_{n=-\infty}^{\infty} \hat{f}(n)$$

**应用**：
- $\theta$ 函数的函数方程
- 热核的迹公式
- 数论中的模形式

---

## 关键性质与定理

### 定理1：Fourier反演定理

**定理**：若 $f, \hat{f} \in L^1(\mathbb{R})$，则：
$$f(x) = \int_{-\infty}^{\infty} \hat{f}(\xi) e^{2\pi i x \xi} d\xi \quad \text{a.e.}$$

在连续点精确成立。

### 定理2：Riemann-Lebesgue 引理

**定理**：若 $f \in L^1(\mathbb{R})$，则 $\hat{f} \in C_0(\mathbb{R})$，即：
$$\lim_{|\xi| \to \infty} \hat{f}(\xi) = 0$$

### 定理3：Hausdorff-Young 不等式

**定理**：若 $1 \leq p \leq 2$，$f \in L^p(\mathbb{R})$，则 $\hat{f} \in L^{p'}(\mathbb{R})$，其中 $\frac{1}{p} + \frac{1}{p'} = 1$，且：
$$\|\hat{f}\|_{p'} \leq \|f\|_p$$

### 定理4：采样定理 (Shannon)

**定理**：若 $f$ 是带宽为 $B$ 的信号（即 $\text{supp}(\hat{f}) \subset [-B, B]$），则：
$$f(x) = \sum_{n=-\infty}^{\infty} f\left(\frac{n}{2B}\right) \text{sinc}\left(2B\left(x - \frac{n}{2B}\right)\right)$$

其中 $\text{sinc}(x) = \frac{\sin(\pi x)}{\pi x}$。

**意义**：带限信号可由离散采样完全重建。

---

## 典型例子

### 例子1：方波的Fourier级数

设 $f(x) = \text{sgn}(x)$ 在 $(-\pi, \pi)$，周期延拓。

**计算**：$f$ 是奇函数，$a_n = 0$，
$$b_n = \frac{2}{\pi}\int_0^{\pi} \sin nx\,dx = \frac{2(1-(-1)^n)}{n\pi}$$

故：
$$f(x) \sim \frac{4}{\pi}\sum_{k=0}^{\infty} \frac{\sin(2k+1)x}{2k+1}$$

### 例子2：Gauss函数的Fourier变换

**定理**：若 $f(x) = e^{-\pi x^2}$，则 $\hat{f}(\xi) = e^{-\pi \xi^2}$。

即Gauss函数是Fourier变换的本征函数。

**证明**：利用微分方程 $f' = -2\pi x f$ 和Fourier变换性质。

### 例子3：热方程的求解

**问题**：$\partial_t u = \partial_x^2 u$，$u(x,0) = f(x)$

**解**：Fourier变换得 $\partial_t \hat{u} = -4\pi^2 \xi^2 \hat{u}$

解得 $\hat{u}(\xi, t) = \hat{f}(\xi) e^{-4\pi^2 \xi^2 t}$

反变换：$u(x,t) = (f * K_t)(x)$，其中 $K_t(x) = \frac{1}{\sqrt{4\pi t}}e^{-x^2/(4t)}$ 是热核。

---

## 关联概念网络

### 相似概念

| 概念 | 关系 | 说明 |
|------|------|------|
| **Laplace变换** | 推广 | 适用于非绝对可积函数 |
| **Z变换** | 离散类比 | 离散时间信号处理 |
| **小波变换** | 现代推广 | 时频局部化分析 |
| **Radon变换** | 高维推广 | 医学成像（CT） |

### 对偶概念

| 概念 | 对偶关系 | 说明 |
|------|----------|------|
| **时域 ↔ 频域** | Fourier对偶 | 对偶群上的变换 |
| **周期 ↔ 离散** | Poisson对偶 | 采样与周期化 |
| **紧支 ↔ 解析** | Paley-Wiener | 时频对偶性 |

### 推广概念

```
Fourier级数 → Fourier变换 → 抽象调和分析
      ↓              ↓
   离散FT(DFT)    球面调和
      ↓              ↓
   FFT算法      对称空间
```

---

## 课程对齐

### MIT 18.100
- **Supplementary**: Fourier series basics, convergence
- **Related courses**: 18.311 (PDEs), 18.085 (Computational)

### Princeton MAT 218
- **Topic**: Fourier analysis and applications
- **Text**: Stein & Shakarchi, *Fourier Analysis*
- **Key topics**: Fourier series, transform, Plancherel, applications to PDEs

---

## 总结

Fourier分析是现代数学和工程的核心工具，它将复杂的函数/信号分解为简单的简谐振动。从Fourier级数的周期性展开到Fourier变换的频谱分析，从卷积运算到Plancherel等距性质，Fourier分析揭示了时域与频域之间的深刻对偶性。它在偏微分方程、信号处理、量子力学和数论中都有不可替代的应用。

---

*创建日期：2026年4月*  
*相关概念：[卷积与逼近](卷积与逼近.md)、[Schwartz空间](Schwartz空间.md)、[分布理论](分布理论.md)*
