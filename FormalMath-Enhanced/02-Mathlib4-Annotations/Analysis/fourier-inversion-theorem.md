---
msc_primary: 00A99
processed_at: '2026-04-15'
title: Fourier 反演定理 (Fourier Inversion Theorem)
---
# Fourier 反演定理 (Fourier Inversion Theorem)

## Mathlib4 引用

```lean
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.FourierTransform

namespace FourierInversion

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- Fourier 反演定理：可积函数的 Fourier 变换的逆变换恢复原函数 -/
theorem fourier_inversion {f : V → ℂ} (hf : Integrable f) (hfc : Continuous f) (v : V) :
    𝓕⁻ (𝓕 f) v = f v := by
  -- 参见 Mathlib4 Analysis.Fourier.Inversion
  sorry

end FourierInversion
```

## 数学背景

Fourier 反演定理是调和分析与现代偏微分方程理论的基石之一。Joseph Fourier 在19世纪初研究热传导方程时首次系统使用了 Fourier 级数。该定理表明：在适当的正则性和可积性条件下，一个函数可以通过其 Fourier 变换完全恢复。这揭示了时域（或空域）与频域之间的对偶性，为信号处理、量子力学和数论提供了深刻洞见。

## 直观解释

Fourier 反演定理告诉我们：**一个信号既可以看作时间的函数，也可以看作频率的叠加，而且这两种视角包含完全等价的信息**。想象一首交响乐：时域视角是随时间变化的声波，频域视角则是各种乐器（不同频率）的组合。反演定理保证，只要知道了每种乐器的贡献（Fourier 变换），就能完美地重建整首乐曲（逆变换）。

## 形式化表述

设 $f \in L^1(\mathbb{R}^n)$ 且 $f$ 连续，则对几乎处处的 $x \in \mathbb{R}^n$：

$$f(x) = \int_{\mathbb{R}^n} \hat{f}(\xi) e^{2\pi i \langle x, \xi \rangle} d\xi$$

其中 Fourier 变换定义为：

$$\hat{f}(\xi) = \int_{\mathbb{R}^n} f(x) e^{-2\pi i \langle x, \xi \rangle} dx$$

在 Mathlib4 中，使用符号 `𝓕` 表示 Fourier 变换，`𝓕⁻` 表示逆 Fourier 变换。

## 证明思路

1. **Gauss 核逼近**：用 $e^{-\pi \varepsilon^2 |\xi|^2}$ 作为收敛因子控制积分
2. **Fubini 交换积分次序**：验证卷积与 Gauss 核的相互作用
3. **好核性质**：Gauss 核的卷积逼近原函数（恒等逼近）
4. **极限过渡**：令 $\varepsilon \to 0$，得到反演公式

核心难点在于缺少直接可积性时无法直接应用 Fubini 定理，需要通过正则化核获得足够的可积性控制。

## 示例

### 示例 1：Gauss 函数

设 $f(x) = e^{-\pi x^2}$，则 $\hat{f}(\xi) = e^{-\pi \xi^2}$。

验证反演：$\int_{-\infty}^{\infty} e^{-\pi \xi^2} e^{2\pi i x \xi} d\xi = e^{-\pi x^2} = f(x)$。

### 示例 2：矩形函数

设 $f(x) = \mathbf{1}_{[-1,1]}(x)$，则：

$$\hat{f}(\xi) = \frac{\sin(2\pi \xi)}{\pi \xi}$$

在 $f$ 的连续点，反演公式成立；在间断点 $x = \pm 1$ 收敛到平均值 $\frac{1}{2}$。

### 示例 3：热方程求解

一维热方程初值问题 $u_t = u_{xx}$，$u(0,x) = f(x)$。

对空间变量作 Fourier 变换：$\hat{u}(t,\xi) = e^{-4\pi^2 \xi^2 t}\hat{f}(\xi)$。

再应用反演定理即可得到热核表示的解。

## 应用

- **信号处理**：滤波、采样定理与频谱分析
- **量子力学**：位置表象与动量表象的等价性
- **偏微分方程**：常系数线性 PDE 的求解方法
- **数论**：Poisson 求和公式与 $\theta$ 函数
- **医学成像**：CT 与 MRI 的重建算法基础

## 相关概念

- Fourier 变换 (Fourier Transform)：将函数映射到频域的线性算子
- Plancherel 定理：$L^2$ 空间中 Fourier 变换的等距性
- 卷积定理：时域卷积对应频域乘积
- 不确定性原理：时域与频域的局部化限制
- Schwartz 空间 (Schwartz Space)：保证 Fourier 变换自同构的速降函数空间

## 参考

### 教材

- [Stein & Shakarchi. Fourier Analysis. Princeton, 2003. Chapters 2, 5]
- [Katznelson. An Introduction to Harmonic Analysis. Dover, 1976. Chapter 6]

### 在线资源

- [Mathlib4 文档 - Fourier.Inversion][https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/Inversion.html]
- [Mathlib4 文档 - FourierTransform][https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/FourierTransform.html]

---

*最后更新：2026-04-15 | 版本：v1.0.0*
