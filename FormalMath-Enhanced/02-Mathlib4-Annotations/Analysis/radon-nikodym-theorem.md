---
msc_primary: 00A99
processed_at: '2026-04-03'
title: Radon-Nikodym定理 (Radon-Nikodym Theorem)
---
# Radon-Nikodym定理 (Radon-Nikodym Theorem)

## Mathlib4 引用

```lean
import Mathlib.MeasureTheory.Measure.RadonNikodym
import Mathlib.MeasureTheory.Decomposition.SignedHahn

namespace RadonNikodym

variable {X : Type*} [MeasurableSpace X]
variable {μ ν : Measure X} [SigmaFinite μ] [SigmaFinite ν]

/-- Radon-Nikodym定理：绝对连续测度的密度存在 -/
theorem radon_nikodym (hνμ : ν ≪ μ) :
    ∃ f : X → ℝ≥0∞, Measurable f ∧
      ∀ s, MeasurableSet s → ν s = ∫⁻ x in s, f x ∂μ := by
  -- 应用Lebesgue分解
  sorry

/-- Radon-Nikodym导数的唯一性（几乎处处）-/
theorem radon_nikodym_unique {f g : X → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ s, MeasurableSet s → ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ) :
    f =ᵐ[μ] g := by
  sorry

/-- Radon-Nikodym导数的链式法则 -/
theorem radon_nikodym_chain_rule {μ ν ρ : Measure X} [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ρ]
    (hνμ : ν ≪ μ) (hρν : ρ ≪ ν) :
    (μ.rnDeriv ρ) =ᵐ[μ] (μ.rnDeriv ν) * (ν.rnDeriv ρ) := by
  sorry

end RadonNikodym
```

## 数学背景

Radon-Nikodym定理由Johann Radon在1913年（对欧几里得空间）和Otto Nikodym在1930年（对一般测度空间）证明。这是测度论中最深刻的定理之一，表明绝对连续测度可以表示为关于参考测度的积分。该定理是条件期望、鞅论、数理金融和风险中性测度理论的基础。

## 直观解释

Radon-Nikodym定理告诉我们：**如果一个测度相对于另一个测度"绝对连续"，那么它可以被表示为密度函数**。

想象有两个质量分布 $\mu$ 和 $\nu$。如果 $\nu$ 中任何"零质量"区域在 $\mu$ 中也是零质量（绝对连续），那么存在"密度"函数 $f$，使得 $\nu$ 可以通过对 $\mu$ 加权得到：$d\nu = f \, d\mu$。这就像说，一个分布可以完全由另一个分布和一个"转换因子"描述。

## 形式化表述

测度 $\nu$ **绝对连续**于 $\mu$（记作 $\nu \ll \mu$），如果 $\mu(A) = 0 \Rightarrow \nu(A) = 0$。

**Radon-Nikodym定理**：若 $\nu \ll \mu$ 且两者都是 $\sigma$-有限的，则存在非负可测函数 $f$（称为**Radon-Nikodym导数**或**密度**），使得：

$$\nu(E) = \int_E f \, d\mu$$

对所有可测集 $E$ 成立。

**记法**：$f = \frac{d\nu}{d\mu}$ 或 $d\nu = f \, d\mu$。

## 证明思路

1. **有限测度情形**：
   - 考虑集合 $\mathcal{G} = \{g : \int_E g \, d\mu \leq \nu(E), \forall E\}$
   - 取上确界 $f = \sup \mathcal{G}$
   - 证明等号成立

2. **σ-有限情形**：
   - 将空间分解为有限测度集的递增序列
   - 在每个分量上应用有限情形

3. **唯一性**：
   - 由积分的局部化性质
   - 若 $\int_E f \, d\mu = \int_E g \, d\mu$ 对所有 $E$，则 $f = g$ a.e.

核心洞察是凸集的极值点和Hahn分解。

## 示例

### 示例 1：概率密度

设 $\mu$ 是Lebesgue测度，$\nu$ 是概率测度，密度 $f(x) = \frac{1}{\sqrt{2\pi}} e^{-x^2/2}$。

$\nu \ll \mu$，Radon-Nikodym导数就是 $f$ 本身。

### 示例 2：离散情形

设 $\mu$ 是计数测度，$\nu$ 由质量函数 $p$ 给出。

$\nu \ll \mu$，密度 $f(x) = p(x)$。

### 示例 3：奇异测度

设 $\mu$ 是Lebesgue测度，$\nu$ 是Dirac测度 $\delta_0$。

$\nu$ 不绝对连续于 $\mu$（$\mu(\{0\}) = 0$ 但 $\nu(\{0\}) = 1$），定理不适用。

## 应用

- **概率论**：条件期望的定义 $E[X|\mathcal{F}]$
- **数理金融**：风险中性测度、Girsanov定理
- **统计推断**：似然函数、最大似然估计
- **信息论**：相对熵（Kullback-Leibler散度）
- **遍历理论**：不变测度的变化

## 相关概念

- [绝对连续性 (Absolute Continuity)](./absolute-continuity.md)：测度的绝对连续
- [Lebesgue分解 (Lebesgue Decomposition)](./lebesgue-decomposition.md)：测度的分解
- [条件期望 (Conditional Expectation)](./conditional-expectation.md)：Radon-Nikodym的应用
- [密度函数 (Density Function)](./density-function.md)：Radon-Nikodym导数
- [等价测度 (Equivalent Measures)](./equivalent-measures.md)：相互绝对连续

## 参考

### 教材

- [Folland. Real Analysis. Wiley, 2nd edition, 1999. Chapter 3]
- [Rudin. Real and Complex Analysis. McGraw-Hill, 3rd edition, 1987. Chapter 6]

### 历史文献

- [Radon. Theorie und Anwendungen der absolut additiven Mengenfunktionen. 1913]
- [Nikodym. Sur une généralisation des intégrales de M. J. Radon. 1930]

### 在线资源

- [Mathlib4 文档 - RadonNikodym](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/RadonNikodym.html)
- [Terry Tao - Radon-Nikodym](https://terrytao.wordpress.com/2009/01/09/254a-notes-3a-measure-theory-lebesgue-measure/)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
