---
msc_primary: 97U50
processed_at: '2026-04-03'
title: Plancherel定理 (Plancherel Theorem)
---
# Plancherel定理 (Plancherel Theorem)

## Mathlib4 引用

```lean
import Mathlib.Analysis.Fourier.Plancherel
import Mathlib.Analysis.Fourier.FourierTransform

namespace PlancherelTheorem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Plancherel定理：L²函数的Fourier变换保持内积 -/
theorem plancherel {f g : 𝓢(ℝ, E)} : -- Schwartz空间
    inner (fourierTransform f) (fourierTransform g) = (2 * π) • inner f g := by
  -- 利用卷积定理和反演公式
  sorry

/-- Plancherel定理（范数形式）-/
theorem plancherel_norm {f : 𝓢(ℝ, E)} :
    ‖fourierTransform f‖ = Real.sqrt (2 * π) * ‖f‖ := by
  have h : inner (fourierTransform f) (fourierTransform f) = (2 * π) • inner f f :=
    plancherel
  simp [norm_eq_sqrt_inner] at h ⊢
  sorry

/-- L²延拓 -/
theorem fourier_transform_L2 [MeasurableSpace E] [BorelSpace E] :
    ∃ F : L²(ℝ, E) →ₗᵢ[ℂ] L²(ℝ, E),
      ∀ f : 𝓢(ℝ, E), F f = fourierTransform f := by
  -- 等距稠密延拓
  sorry

end PlancherelTheorem
```

## 数学背景

Plancherel定理由Michel Plancherel在1910年证明，是调和分析的核心结果。它表明Fourier变换在 $L^2$ 空间上是等距同构（差常数因子），将时域的 $L^2$ 范数与频域的 $L^2$ 范数联系起来。这一定理是信号处理、量子力学和偏微分方程的基础，提供了从时域到频域转换时能量守恒的数学保证。

## 直观解释

Plancherel定理告诉我们：**信号的总能量在时域和频域相等**。

想象一个声波信号。你可以描述它随时间的变化（时域），也可以描述它包含的频率成分（频域）。Plancherel定理说，无论用哪种方式描述，信号的"总能量"（$L^2$ 范数的平方）是一样的。这就像说，同一首乐曲，无论是在时间上测量其响度，还是在频率上测量其频谱，总能量不变。

## 形式化表述

设 $f \in L^2(\mathbb{R}^n)$，Fourier变换定义为：
$$\hat{f}(\xi) = \int_{\mathbb{R}^n} f(x) e^{-2\pi i x \cdot \xi} dx$$

**Plancherel定理**：

1. **等距性**：$\|\hat{f}\|_{L^2} = \|f\|_{L^2}$（适当归一化）
2. **内积保持**：$\langle \hat{f}, \hat{g} \rangle = \langle f, g \rangle$
3. **酉性**：Fourier变换延拓为 $L^2(\mathbb{R}^n)$ 上的酉算子

**反演公式**：$f(x) = \int_{\mathbb{R}^n} \hat{f}(\xi) e^{2\pi i x \cdot \xi} d\xi$（$L^2$ 意义下）

## 证明思路

1. **Schwartz空间**：
   - 在 $\mathcal{S}(\mathbb{R}^n)$（Schwartz空间）上直接计算
   - 利用Fourier变换的自伴性（差共轭）

2. **稠密性**：
   - $\mathcal{S}(\mathbb{R}^n)$ 在 $L^2(\mathbb{R}^n)$ 中稠密
   - 等距算子可唯一延拓到闭包

3. **卷积论证**：
   - $\int |\hat{f}|^2 = \int \hat{f} \overline{\hat{f}} = \int \hat{f} \widehat{\overline{f(-\cdot)}}$
   - 利用卷积定理和 $\delta$ 函数性质

4. **酉性**：
   - 等距+满射（由反演公式）= 酉算子

核心洞察是Fourier变换在适当归一化下的酉性。

## 示例

### 示例 1：Gauss函数

$f(x) = e^{-\pi x^2}$，则 $\hat{f}(\xi) = e^{-\pi \xi^2}$。

$\|f\|_{L^2}^2 = \int e^{-2\pi x^2} dx = \frac{1}{\sqrt{2}}$

$\|\hat{f}\|_{L^2}^2 = \frac{1}{\sqrt{2}}$，验证Plancherel等式。

### 示例 2：矩形函数

$f(x) = \chi_{[-a, a]}(x)$（区间示性函数）。

$\hat{f}(\xi) = 2a \text{sinc}(2a\xi)$，其中 $\text{sinc}(x) = \frac{\sin(\pi x)}{\pi x}$。

$\|f\|_{L^2}^2 = 2a$，$\|\hat{f}\|_{L^2}^2 = 2a$（Parseval等式）。

### 示例 3：信号处理

时域信号 $f(t)$ 的能量：$E = \int |f(t)|^2 dt$

频域表示：$E = \int |\hat{f}(\omega)|^2 d\omega$

应用：滤波器设计、频谱分析。

## 应用

- **信号处理**：Parseval定理、能量守恒
- **量子力学**：位置与动量波函数的 $L^2$ 范数
- **偏微分方程**：$L^2$ 估计和正则性理论
- **概率论**：特征函数的 $L^2$ 理论
- **编码理论**：频谱效率分析

## 相关概念

- [Fourier变换 (Fourier Transform)](./fourier-transform.md)：时频转换
- Parseval等式 (Parseval's Identity)：Plancherel的特例
- Schwartz空间 (Schwartz Space)：速降函数空间
- 酉算子 (Unitary Operator)：保持内积的算子
- 卷积定理 (Convolution Theorem)：Fourier变换的性质

## 参考

### 教材

- [Stein & Shakarchi. Fourier Analysis. Princeton, 2003. Chapter 5]
- [Katznelson. An Introduction to Harmonic Analysis. Dover, 1976. Chapter 6]

### 历史文献

- [Plancherel. Contribution à l'étude de la représentation d'une fonction arbitraire par des intégrales définies. 1910]

### 在线资源

- [Mathlib4 文档 - Plancherel][https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/Plancherel.html](需更新)
- [Wikipedia - Plancherel Theorem](https://en.wikipedia.org/wiki/Plancherel_theorem)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
