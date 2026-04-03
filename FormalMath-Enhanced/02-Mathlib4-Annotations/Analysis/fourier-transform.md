# 傅里叶变换 (Fourier Transform)

## Mathlib4 引用

```lean
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Integral.Bochner

namespace Real

/-- 傅里叶变换 -/
noncomputable def fourierTransform (f : ℝ → ℂ) : ℝ → ℂ :=
  fun ξ => ∫ x : ℝ, f x * Complex.exp (-2 * π * Complex.I * x * ξ)

/-- 逆傅里叶变换 -/
noncomputable def fourierInvTransform (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => ∫ ξ : ℝ, f ξ * Complex.exp (2 * π * Complex.I * x * ξ)

end Real
```

## 数学背景

傅里叶分析由法国数学家约瑟夫·傅里叶（Joseph Fourier）于1807年提出，最初用于热传导问题的求解。傅里叶发现任何周期函数都可以表示为正弦和余弦函数的叠加，这一发现 revolutionized 了数学分析和物理学。傅里叶变换将这一思想推广到非周期函数，成为现代信号处理、量子力学和偏微分方程的核心工具。

## 直观解释

傅里叶变换告诉我们：**任何函数都可以分解为不同频率的正弦波的叠加**。想象一个复杂的音乐信号，傅里叶变换就像一台"频谱分析仪"，告诉我们这个音乐包含哪些音符（频率分量）以及每个音符的强度（振幅）。

数学上，变换将时域（或空间域）的函数 $f(x)$ 映射到频域的函数 $\hat{f}(\xi)$，描述了原函数中各频率成分的分布。

## 形式化表述

函数 $f \in L^1(\mathbb{R})$ 的傅里叶变换定义为：

$$\hat{f}(\xi) = \int_{-\infty}^{\infty} f(x) e^{-2\pi i x \xi} dx$$

逆变换为：

$$f(x) = \int_{-\infty}^{\infty} \hat{f}(\xi) e^{2\pi i x \xi} d\xi$$

不同文献中常数因子可能有不同约定（如角频率形式）。

## 证明思路

1. **定义良好性**：证明对 $f \in L^1$，积分绝对收敛
2. **反演公式**：证明 $\mathcal{F}^{-1}\mathcal{F}f = f$
3. **Plancherel 定理**：$\|\hat{f}\|_2 = \|f\|_2$
4. **延拓到 $L^2$**：利用稠密性和连续性

关键在于证明高斯函数 $e^{-\pi x^2}$ 的傅里叶变换等于自身，再通过逼近论证一般情形。

## 示例

### 示例 1：高斯函数

设 $f(x) = e^{-\pi x^2}$，则：

$$\hat{f}(\xi) = \int_{-\infty}^{\infty} e^{-\pi x^2} e^{-2\pi i x \xi} dx = e^{-\pi \xi^2}$$

高斯函数的傅里叶变换仍是高斯函数！这是唯一（在伸缩下）满足此性质的函数。

### 示例 2：矩形函数

设 $f(x) = \mathbf{1}_{[-a, a]}(x)$（区间指示函数）。

$$\hat{f}(\xi) = \int_{-a}^{a} e^{-2\pi i x \xi} dx = \frac{\sin(2\pi a \xi)}{\pi \xi}$$

这是 sinc 函数，在信号处理中极为重要。

### 示例 3：热方程求解

热方程：$\frac{\partial u}{\partial t} = \frac{\partial^2 u}{\partial x^2}$

对空间变量做傅里叶变换：
$$\frac{\partial \hat{u}}{\partial t} = -4\pi^2 \xi^2 \hat{u}$$

解为：$\hat{u}(\xi, t) = \hat{u}(\xi, 0) e^{-4\pi^2 \xi^2 t}$

逆变换给出热核：$u(x, t) = (G_t * u_0)(x)$

## 应用

- **信号处理**：频谱分析、滤波、压缩（MP3、JPEG）
- **量子力学**：位置与动量表象的转换
- **偏微分方程**：线性 PDE 的求解
- **医学成像**：CT、MRI 的重建算法
- **通信理论**：调制解调、信道分析

## 相关概念

- [傅里叶级数 (Fourier Series)](./fourier-series.md)：周期函数的离散频率分解
- [卷积 (Convolution)](./convolution.md)：时域乘积对应频域卷积
- [不确定性原理 (Uncertainty Principle)](./uncertainty-principle.md)：时频局域化的限制
- [快速傅里叶变换 (FFT)](./fast-fourier-transform.md)：离散傅里叶变换的高效算法
- [分布理论 (Distribution Theory)](./distribution-theory.md)：广义函数的傅里叶变换

## 参考

### 教材

- [Stein & Shakarchi. Fourier Analysis. Princeton, 2003]
- [Katznelson. An Introduction to Harmonic Analysis. Dover, 1976]

### 历史文献

- [Fourier. Théorie analytique de la chaleur. 1822]

### 在线资源

- [Mathlib4 文档 - FourierTransform](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/FourierTransform.html)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
