---
msc_primary: 97U50
processed_at: '2026-04-03'
---

# Plancherel定理

## Mathlib4 引用

```lean
import Mathlib.Analysis.Fourier.Plancherel

namespace Analysis

/-- Plancherel定理 -/
theorem plancherel_theorem
    {G : Type*} [TopologicalSpace G] [LocallyCompactSpace G]
    [CommGroup G] [IsTopologicalGroup G]
    {μ : Measure G} [IsHaarMeasure μ]
    {f : G → ℂ} (hf : Integrable f μ) (hL2 : f ∈ L2 μ) :
    ‖fourierTransform f‖_{L2(Ĝ)} = ‖f‖_{L2(G)} := by
  -- Fourier变换保持L^2范数
  sorry

/-- 逆Fourier变换 -/
theorem fourier_inversion_plancherel
    {G : Type*} [TopologicalSpace G] [LocallyCompactSpace G]
    [CommGroup G] [IsTopologicalGroup G]
    {f : G → ℂ} (hf : f ∈ L1 G ∩ L2 G) :
    fourierInverse (fourierTransform f) = f := by
  -- L^2上的Fourier反演
  sorry

end Analysis
```

## 数学背景

Plancherel定理由Michel Plancherel在1910年证明，是调和分析中最基本的结果之一。定理表明：Fourier变换在 $L^2$ 空间上是等距同构（在适当归一化下）。这为Fourier分析提供了坚实的理论基础，使得 $L^2$ 成为研究Fourier变换的自然空间。Plancherel定理推广了Parseval恒等式（有限维版本），是信号处理、量子力学和偏微分方程中的核心工具。

## 直观解释

Plancherel定理如同一个"能量守恒定律"：函数在时域和频域的"总能量"相同。想象一个信号——无论我们观察它的时间波形还是频谱分布，其总强度（$L^2$范数）保持不变。这反映了Fourier变换是"正交变换"的本质，只是将信号"旋转"到不同的坐标系（频域），而不改变其"长度"。

## 形式化表述

设 $G$ 是局部紧Abel群，$\hat{G}$ 是其对偶群（特征标群），$\mu$ 是Haar测度。

**Plancherel定理**：Fourier变换 $\mathcal{F}: L^2(G) \to L^2(\hat{G})$ 是Hilbert空间等距同构。

**Parseval恒等式**：对 $f \in L^2(G)$，
$$\int_G |f(x)|^2 d\mu(x) = \int_{\hat{G}} |\hat{f}(\chi)|^2 d\hat{\mu}(\chi)$$

**Fourier反演**：在 $L^2$ 意义下，$\mathcal{F}^{-1} = \mathcal{F}^*$（伴随算子）。

## 证明思路

1. **稠密子空间**：在 $L^2$ 中考虑 $L^1 \cap L^2$
2. **卷积性质**：利用卷积的Fourier变换
3. **近似单位**：构造Dirac序列
4. **等距延拓**：从稠密子空间延拓到全空间
5. **满射性证明**：Fourier变换是双射

## 示例

### 示例 1：圆周上的Plancherel

**问题**：验证 $S^1$ 上的Plancherel定理。

**解答**：

$L^2(S^1)$ 的Fourier级数：$f(x) = \sum_{n \in \mathbb{Z}} c_n e^{inx}$

Plancherel：$\frac{1}{2\pi}\int_0^{2\pi} |f(x)|^2 dx = \sum_{n \in \mathbb{Z}} |c_n|^2$

这是经典的Parseval恒等式。

### 示例 2：高斯函数的Fourier变换

**问题**：计算高斯函数 $e^{-\pi x^2}$ 的 $L^2$范数。

**解答**：

Fourier变换保持范数：$\|e^{-\pi x^2}\|_{L^2} = \|\mathcal{F}(e^{-\pi x^2})\|_{L^2}$

由于 $\mathcal{F}(e^{-\pi x^2}) = e^{-\pi \xi^2}$（自守），

$$\int_{-\infty}^{\infty} e^{-2\pi x^2} dx = \frac{1}{\sqrt{2}}$$

## 应用

- **信号处理**：能量谱密度
- **量子力学**：不确定性原理
- **偏微分方程**：Sobolev空间方法
- **数论**：L-函数的函数方程
- **随机过程**：Wiener过程的特征函数

## 相关概念

- [Fourier变换](./fourier-transform.md)：Plancherel定理的对象
- [Haar测度](./haar-measure.md)：局部紧群的测度
- [调和分析](./harmonic-analysis.md)：Plancherel定理的领域
- [不确定性原理](./uncertainty-principle.md)：Plancherel定理的推论
- [Pontryagin对偶](./pontryagin-duality.md)：局部紧Abel群的对偶理论

## 参考

### 教材

- Rudin, W. Fourier Analysis on Groups. Wiley, 1990.
- Katznelson, Y. An Introduction to Harmonic Analysis. Dover, 1976.

### 论文

- Plancherel, M. Contribution à l'étude de la représentation d'une fonction arbitraire par des intégrales définies. Rend. Circ. Mat. Palermo, 30: 289-335, 1910.

### 在线资源

- [Plancherel Theorem Wikipedia](https://en.wikipedia.org/wiki/Plancherel_theorem)
- [nLab - Plancherel Theorem](https://ncatlab.org/nlab/show/Plancherel+theorem)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
