---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: Fourier 反演定理 (Fourier Inversion Theorem)
---
# Fourier 反演定理 (Fourier Inversion Theorem)

## Mathlib4 引用

```lean
import Mathlib.Analysis.Fourier.FourierTransform

namespace FourierTransform

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Fourier 反演定理：Schwartz 函数的 Fourier 变换可反演 -/
theorem fourier_inversion (f : V → ℂ) (hf : SchwartzMap V ℂ) (x : V) :
    f x = ∫ v, 𝓕⁻¹ (𝓕 f) v * fourierChar (-⟪v, x⟫_ℝ) := by
  -- 利用平移不变性和 Fubini 定理交换积分顺序
  sorry

end FourierTransform
```

## 数学背景

Fourier 反演定理是数学分析、调和分析和信号处理中的核心结果，由法国数学家约瑟夫·傅里叶（Joseph Fourier）在研究热传导问题时开创，后经狄利克雷（Dirichlet）、黎曼（Riemann）、勒贝格（Lebesgue）和施瓦茨（Schwartz）等人严格化。该定理断言：在适当条件下，一个函数可以通过其 Fourier 变换完全恢复——即对函数先作 Fourier 变换，再作逆 Fourier 变换，就得到原函数。

## 直观解释

Fourier 反演定理揭示了一个深刻的对称性：任何一个足够好的函数都可以被分解为不同频率简谐波的叠加（Fourier 变换），而这些频率分量又可以被重新合成为原函数（逆 Fourier 变换）。这就像将一首交响乐分解为各个乐器的声音，然后再将它们重新混合成原来的乐曲。定理告诉我们：在数学上，这种分解和重构是完美的——不会丢失任何信息。

## 形式化表述

设 $f \in L^1(\mathbb{R}^n) \cap C(\mathbb{R}^n)$ 且其 Fourier 变换 $\hat{f} \in L^1(\mathbb{R}^n)$，则对几乎所有 $x \in \mathbb{R}^n$：

$$f(x) = \frac{1}{(2\pi)^n} \int_{{\mathbb{R}^n}} \hat{f}(\xi) e^{{i\langle \xi, x \rangle}} d\xi$$

其中 Fourier 变换定义为：

$$\hat{f}(\xi) = \int_{{\mathbb{R}^n}} f(x) e^{{-i\langle \xi, x \rangle}} dx$$

对于 Schwartz 函数 $f \in \mathcal{S}(\mathbb{R}^n)$，反演公式对所有 $x$ 点态成立。

其中：

- $\hat{f}$ 表示 $f$ 的 Fourier 变换
- $e^{{i\langle \xi, x \rangle}}$ 是复指数函数（平面波）
- $(2\pi)^n$ 是归一化常数（具体形式依赖于 Fourier 变换的约定）
- $\mathcal{S}(\mathbb{R}^n)$ 是速降函数空间（Schwartz 空间）

## 证明思路

1. **Fourier 核的积分**：计算 $\int e^{{-i\langle \xi, x - y \rangle}} d\xi$ 在分布意义下的值
2. **Fubini 定理**：对 $\hat{f}$ 充分好（如 Schwartz 函数）时，交换积分顺序
3. **恒等逼近**：利用 Gaussian 核 $e^{{-\varepsilon|\xi|^2}}$ 作为平滑因子
4. **控制收敛定理**：取极限得到无正则化因子的反演公式

核心洞察在于 Fourier 变换和逆变换构成 $L^2$ 上的酉算子对。

## 示例

### 示例 1：Gaussian 函数

$f(x) = e^{{-x^2/2}}$ 的 Fourier 变换是 $\hat{f}(\xi) = \sqrt{2\pi} e^{{-\xi^2/2}}$。应用反演定理可得原函数。

### 示例 2：热方程

热方程 $u_t = \Delta u$ 的基本解可以通过 Fourier 变换求解，再利用反演定理得到热核。

### 示例 3：信号处理

在音频压缩（如 MP3）中，信号先被 Fourier 变换到频域，进行有损压缩后，再通过逆 Fourier 变换重建时域信号。反演定理保证了（在无压缩时）完美重建的可能性。

## 应用

- **信号处理**：音频、图像和视频的压缩与滤波
- **量子力学**：位置表象与动量表象之间的幺正变换
- **偏微分方程**：热方程、波动方程和 Schrödinger 方程的求解
- **医学成像**：MRI 和 CT 中的图像重建算法
- **金融数学**：期权定价中的特征函数反演（如 Lévy 过程）

## 相关概念

- Fourier 变换 (Fourier Transform)：将函数分解为频率分量
- Schwartz 空间 (Schwartz Space)：速降光滑函数空间
- 调和分析 (Harmonic Analysis)：研究函数分解与合成的数学分支
- Plancherel 定理：Fourier 变换在 $L^2$ 上的等距性质
- 不确定性原理 (Uncertainty Principle)：时域与频域局部化的制约

## 参考

### 教材

- [E. Stein, G. Weiss. Introduction to Fourier Analysis on Euclidean Spaces. Princeton, 1971. Chapter 1]
- [W. Rudin. Functional Analysis. McGraw-Hill, 2nd edition, 1991. Chapter 7]

### 在线资源

- [Mathlib4 - FourierTransform](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/FourierTransform.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*