---
msc_primary: 00A99
processed_at: '2026-04-03'
title: 最大模原理 (Maximum Modulus Principle)
---
# 最大模原理 (Maximum Modulus Principle)

## Mathlib4 引用

```lean
import Mathlib.Analysis.Complex.MaximumModulus
import Mathlib.Analysis.Complex.CauchyIntegral

namespace MaximumModulus

open Complex Metric

variable {U : Set ℂ} [hU : IsOpen U] {f : ℂ → ℂ}

/-- 最大模原理：非常数全纯函数在内部不取最大模 -/
theorem maximum_modulus_principle (hf : DifferentiableOn ℂ f U) (hU_conn : IsPreconnected U)
    (hf_ne_const : ¬ (∃ c, ∀ z ∈ U, f z = c)) (z₀ : ℂ) (hz₀ : z₀ ∈ U) :
    ¬ IsLocalMax (norm ∘ f) z₀ := by
  by_contra hmax
  -- 利用平均值性质
  have h_avg : ∃ r > 0, ball z₀ r ⊆ U ∧ ∀ z ∈ ball z₀ r, ‖f z‖ ≤ ‖f z₀‖ := by
    sorry
  -- 应用Cauchy积分公式
  sorry

/-- 最大模原理（边界形式）-/
theorem maximum_modulus_boundary {K : Set ℂ} (hK : IsCompact K) (hK_int : (interior K).Nonempty)
    (hf : DifferentiableOn ℂ f (interior K)) (hf_cont : ContinuousOn f K) :
    ∀ z ∈ interior K, ‖f z‖ ≤ ⨆ w ∈ frontier K, ‖f w‖ := by
  sorry

/-- 开映射定理 -/
theorem open_mapping (hf : DifferentiableOn ℂ f U) (hU_conn : IsPreconnected U)
    (hf_ne_const : ¬ (∃ c, ∀ z ∈ U, f z = c)) : IsOpenMap (f ∘ Subtype.val : U → ℂ) := by
  sorry

end MaximumModulus
```

## 数学背景

最大模原理由Karl Weierstrass在19世纪后期严格证明（虽然Cauchy早些时候已隐含使用），是复分析的基石之一。该原理揭示了全纯函数的刚性：非常数全纯函数不能在区域内部取到最大模。这一结果深刻反映了全纯函数由其在边界上的值唯一确定的特性，是证明开映射定理、Schwarz引理和许多其他复分析结果的关键工具。

## 直观解释

最大模原理告诉我们：**非常数全纯函数的"高度"只能在边界达到最大**。

想象全纯函数的模像一座山的地形。定理说，如果函数是全纯的（非常数），那么它不可能有山峰——最大值必须在边界上。这就像说，一片水域的表面如果是调和的（无源无汇），水位最高点一定在边界。这反映了全纯函数的"刚性"——局部行为强烈约束全局行为。

## 形式化表述

设 $U \subseteq \mathbb{C}$ 是区域（连通开集），$f: U \to \mathbb{C}$ 全纯。

**最大模原理**：

1. **局部形式**：若 $f$ 非常数，则 $|f|$ 在 $U$ 内没有局部最大值
2. **全局形式**：若 $\overline{U}$ 紧致，则 $|f|$ 的最大值在边界 $\partial U$ 上取得
3. **严格形式**：若 $|f|$ 在某内点达到上确界，则 $f$ 为常数

**开映射定理**：非常数全纯函数将开集映为开集。

## 证明思路

1. **平均值性质**：
   - 全纯函数满足：$f(z_0) = \frac{1}{2\pi} \int_0^{2\pi} f(z_0 + re^{i\theta}) d\theta$
   - 取模：$|f(z_0)| \leq \frac{1}{2\pi} \int_0^{2\pi} |f(z_0 + re^{i\theta})| d\theta$

2. **最大值的矛盾**：
   - 若 $|f|$ 在 $z_0$ 取最大，则 $|f(z_0)| \geq |f(z)|$ 对附近所有 $z$
   - 由平均值，必须有 $|f(z)| = |f(z_0)|$ 在整个圆周上

3. **恒等定理**：
   - $|f|^2$ 是调和的，满足最大值原理
   - 若在内点取最大，则 $|f|$ 局部常数
   - 由恒等定理，$f$ 整体常数

核心洞察是调和函数的平均值性质。

## 示例

### 示例 1：多项式

设 $f(z) = z^2 + 1$ 在单位圆盘 $\mathbb{D}$ 上。

在边界 $|z| = 1$：$|f(z)| = |z^2 + 1|$，最大值在 $z = \pm i$ 处为 2。

在内部：$|f(0)| = 1 < 2$，验证了最大模原理。

### 示例 2：指数函数

$e^z$ 在全平面全纯，无界，故在紧集上最大值在边界。

在圆盘 $|z| \leq R$：$|e^z| = e^{\text{Re } z}$，最大值在 $z = R$。

### 示例 3：反例说明必要性

设 $f(z) = |z|^2 = z\bar{z}$，这不是全纯函数（依赖 $\bar{z}$）。

在圆盘 $|z| \leq 1$：最大值在 $z = 0$（内点）为 0？不，$|z|^2$ 最大值在边界为 1。

反例需更精细：$f(z) = \text{Re}(z)$ 是调和但非全纯，最大值在边界。

## 应用

- **代数基本定理**：多项式必有根
- **Schwarz引理**：单位圆盘上的有界全纯函数
- **Phragmén-Lindelöf原理**：无界区域上的增长控制
- **插值理论**：函数的唯一性
- **控制理论**：系统的稳定性分析

## 相关概念

- [开映射定理 (Open Mapping Theorem)](./open-mapping-theorem.md)：全纯函数的开性
- 平均值性质 (Mean Value Property)：调和函数的特性
- 恒等定理 (Identity Theorem)：全纯函数的唯一性
- [Schwarz引理 (Schwarz Lemma)](./schwarz-lemma.md)：单位圆盘上的约束
- 调和函数 (Harmonic Function)：Laplace方程的解

## 参考

### 教材

- [Ahlfors. Complex Analysis. McGraw-Hill, 3rd edition, 1979. Chapter 4]
- [Stein & Shakarchi. Complex Analysis. Princeton, 2003. Chapter 3]

### 历史文献

- [Weierstrass. Zur Theorie der eindeutigen analytischen Funktionen. 1876]

### 在线资源

- [Mathlib4 文档 - MaximumModulus](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/MaximumModulus.html)[需更新]
- [Wikipedia - Maximum Modulus Principle](https://en.wikipedia.org/wiki/Maximum_modulus_principle)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
