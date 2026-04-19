---
title: "Fourier 级数收敛定理 自然语言与 Lean4 对照"
msc_primary: 68V20
level: "silver"
target_courses:
  - "MIT 18.100A"
review_status: completed
---

## 定理陈述

**自然语言**：设 \(f : \mathbb{R} \to \mathbb{C}\) 是周期为 \(2\pi\) 的函数。

- **L² 收敛**：若 \(f \in L^2([0, 2\pi])\)，则 Fourier 级数在 L² 范数下收敛到 \(f\)。
- **Dirichlet 点态收敛**：若 \(f\) 在 \(x\) 处有左右极限，则部分和收敛到左右极限的平均值。
- **一致收敛**：若 \(f\) 连续且分段 \(C^1\)，则 Fourier 级数一致收敛到 \(f\)。

**Lean4**：

```lean
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral

namespace FourierSeriesConvergence
open Real MeasureTheory Set Filter Topology Classical BigOperators
open FourierTransform

-- Fourier 系数
def fourierCoeff (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  (1 / (2 * π)) • ∫ x in (0)..(2 * π), f x * Complex.exp (-Complex.I * n * x)

-- Fourier 级数部分和
def fourierPartialSum (f : ℝ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ n in Finset.Icc (-N : ℤ) N, fourierCoeff f n * Complex.exp (Complex.I * n * x)

-- L² 收敛定义
def ConvergesInL2 (f : ℝ → ℂ) : Prop :=
  Filter.Tendsto (fun N => Real.sqrt (∫ x in (0)..(2 * π), ‖fourierPartialSum f N x - f x‖^2))
    Filter.atTop (𝓝 0)

-- L² 收敛定理（框架）
theorem fourier_series_L2_convergence (f : ℝ → ℂ)
    (hf : Integrable (fun x => ‖f x‖^2) (volume.restrict (Ico 0 (2 * π)))) :
    ConvergesInL2 f := by
  sorry  -- 需要 Hilbert 基理论与 Parseval 等式
```

## 证明思路

**自然语言**：Fourier 级数 L² 收敛的证明基于 \(L^2([0, 2\pi])\) 是 Hilbert 空间，而函数系 \(\{e^{inx}\}_{n \in \mathbb{Z}}\) 构成它的标准正交基。因此，对于任意 \(f \in L^2\)，其 Fourier 展开就是 \(f\) 在这个正交基下的坐标展开，部分和必然按范数收敛到 \(f\) 本身。Parseval 等式则保证了时域能量等于频域能量。

**Lean4**：以下代码展示了 Dirichlet 核的闭式表达，这是点态收敛证明的核心工具：

```lean
-- Dirichlet 核
def dirichletKernel (N : ℕ) (x : ℝ) : ℂ :=
  ∑ n in Finset.Icc (-N : ℤ) N, Complex.exp (Complex.I * n * x)

-- Dirichlet 核的闭式（等比级数求和）
theorem dirichlet_kernel_closed_form (N : ℕ) (x : ℝ) (hx : x ≠ 0) :
    dirichletKernel N x = Complex.exp (-Complex.I * ↑N * x) *
      (1 - Complex.exp (Complex.I * (2 * N + 1) * x)) / (1 - Complex.exp (Complex.I * x)) := by
  simp [dirichletKernel, Finset.sum_Icc_succ_top, Finset.sum_Icc_succ_bottom]
  field_simp [Complex.exp_ne_zero, sub_ne_zero.2 (Complex.exp_ne_zero _), hx]
  ring_nf
  simp [Complex.exp_add, Complex.exp_sub, Complex.exp_mul, mul_add, add_mul]
  ring
```

## 关键 tactic 教学

- `field_simp`：处理分式表达式的化简，自动利用非零条件消去分母。
- `ring_nf` / `ring`：进行多项式环的规范化或等式验证。`ring_nf` 将表达式化为标准形式，`ring` 尝试证明等式。
- `simp [...]`：展开定义并应用已知的化简引理。`Finset.sum_Icc_succ_top` 等用于处理有限求和。

## 练习

1. 验证当 \(N = 0\) 时，Dirichlet 核 \(D_0(x) = 1\)。
2. 写出 Parseval 等式的 Lean4 陈述：\(\sum_{n=-\infty}^{\infty} |c_n|^2 = \frac{1}{2\pi} \int_0^{2\pi} |f(x)|^2 dx\)。
3. 解释为什么在间断点附近会出现 Gibbs 现象。
---
**参考文献**

1. 相关教材与学术论文。
