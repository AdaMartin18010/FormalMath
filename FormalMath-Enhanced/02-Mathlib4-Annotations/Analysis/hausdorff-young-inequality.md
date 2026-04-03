---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# Hausdorff-Young不等式 (Hausdorff-Young Inequality)

## Mathlib4 引用

```lean
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Plancherel

namespace HausdorffYoung

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Hausdorff-Young不等式 -/
theorem hausdorff_young {p : ℝ≥0∞} (hp : 1 ≤ p ∧ p ≤ 2) {f : Lp ℂ p (volume : Measure ℝ)} :
    ‖fourierTransform f‖ ≤ ‖f‖ := by
  -- Riesz-Thorin插值
  sorry

/-- Pitt不等式（加权Hausdorff-Young）-/
theorem pitt_inequality {f : 𝓢(ℝ, ℂ)} {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (h : α + β ≤ 1) :
    ‖fun x => |x|^(β) • (fourierTransform f) x‖ ≤ C * ‖fun x => |x|^(-α) • f x‖ := by
  -- Hardy-Littlewood-Sobolev理论
  sorry

end HausdorffYoung
```

## 数学背景

Hausdorff-Young不等式由Felix Hausdorff和William Henry Young在1910年代证明，是调和分析中关于Fourier变换 $L^p$ 有界性的基本结果。该不等式表明Fourier变换将 $L^p$（$1 \leq p \leq 2$）映射到 $L^q$（$1/p + 1/q = 1$），且算子范数不超过1。这是Riesz-Thorin插值定理的经典应用，在信号处理、偏微分方程和概率论中有广泛应用。

## 直观解释

Hausdorff-Young不等式告诉我们：**Fourier变换在不同 $L^p$ 空间之间"平滑"地插值**。

想象 $L^1$ 和 $L^2$ 是两个不同的"世界"。我们知道Fourier变换在 $L^1$ 上是有界的（像有界），在 $L^2$ 上是等距的（Plancherel）。Hausdorff-Young说，对于中间的空间 $L^p$（$1 < p < 2$），Fourier变换也是有界的，且界可以插值得到。

## 形式化表述

设 $f \in L^p(\mathbb{R}^n)$，$1 \leq p \leq 2$，$\frac{1}{p} + \frac{1}{q} = 1$。

**Hausdorff-Young不等式**：
$$\|\hat{f}\|_{L^q} \leq \|f\|_{L^p}$$

**等号情形**：Gauss函数达到等号。

**端点**：

- $p = 1$：$\|\hat{f}\|_{L^\infty} \leq \|f\|_{L^1}$（直接估计）
- $p = 2$：$\|\hat{f}\|_{L^2} = \|f\|_{L^2}$（Plancherel）

## 证明思路

1. **端点估计**：
   - $p = 1$：直接由Fourier变换定义
   - $p = 2$：Plancherel定理

2. **Riesz-Thorin插值**：
   - 线性算子在复插值空间的有界性
   - $(L^1, L^2)_\theta = L^p$，$\frac{1}{p} = 1 - \frac{\theta}{2}$

3. **范数估计**：
   - 插值得算子范数 $\leq 1$

4. **等号情形分析**：
   - Gauss函数是唯一（差常数）达到等号的情形

核心洞察是复插值方法和端点估计的结合。

## 示例

### 示例 1：端点情形

$p = 1$：$f = \chi_{[-1,1]}$，$\hat{f}(\xi) = 2\text{sinc}(2\xi)$。

$\|\hat{f}\|_\infty = 2 = \|f\|_1$。

### 示例 2：中间情形

$p = 4/3$，$q = 4$。

Gauss函数：$f(x) = e^{-\pi x^2}$，$\hat{f} = f$。

$\|f\|_{4/3} = (\int e^{-4\pi x^2/3} dx)^{3/4} = (3/4)^{3/4} (2)^{-1/2}$

等号成立。

### 示例 3：信号处理

时域的 $L^p$ 约束转化为频域的 $L^q$ 约束。

应用：滤波器设计、频谱分析。

## 应用

- **信号处理**：时频分析的框架
- **偏微分方程**：Strichartz估计的基础
- **概率论**：特征函数的 $L^p$ 理论
- **不确定性原理**：Fourier变换的约束
- **量子力学**：波函数的表示

## 相关概念

- [Riesz-Thorin插值 (Riesz-Thorin Interpolation)](./riesz-thorin-interpolation.md)：复插值方法
- [Fourier变换 (Fourier Transform)](./fourier-transform.md)：时频转换
- [Lp空间 (Lp Space)](./lp-space.md)：可积函数空间
- [Plancherel定理 (Plancherel Theorem)](./plancherel-theorem.md)：$L^2$ 等距性
- [不确定性原理 (Uncertainty Principle)](./uncertainty-principle.md)：时频约束

## 参考

### 教材

- [Stein & Shakarchi. Fourier Analysis. Princeton, 2003. Chapter 2]
- [Grafakos. Classical Fourier Analysis. Springer, 2008. Chapter 1]

### 历史文献

- [Hausdorff. Eine Ausdehnung des Parsevalschen Satzes über Fourierreihen. 1923]
- [Young. On the multiplication of successions of Fourier constants. 1913]

### 在线资源

- [Mathlib4 文档 - Fourier](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/FourierTransform.html)
- [Wikipedia - Hausdorff-Young Inequality](https://en.wikipedia.org/wiki/Hausdorff%E2%80%93Young_inequality)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
