---
msc_primary: 00A99
processed_at: '2026-04-03'
title: Schwarz引理 (Schwarz Lemma)
---
# Schwarz引理 (Schwarz Lemma)

## Mathlib4 引用

```lean
import Mathlib.Analysis.Complex.SchwarzLemma
import Mathlib.Analysis.Complex.UnitDisc.Basic

namespace SchwarzLemma

open Complex Metric

variable {f : ℂ → ℂ}

/-- Schwarz引理：单位圆盘到自身的全纯映射 -/
theorem schwarz_lemma (hf : DifferentiableOn ℂ f (ball 0 1))
    (hf0 : f 0 = 0) (hf_unit : MapsTo f (ball 0 1) (ball 0 1)) :
    ∀ z ∈ ball 0 1, ‖f z‖ ≤ ‖z‖ ∧ ‖deriv f 0‖ ≤ 1 := by
  intro z hz
  constructor
  · -- 证明 |f(z)| ≤ |z|
    have h1 : ‖f z / z‖ ≤ 1 := by
      apply MaximumModulus.maximum_modulus_principle_boundary
      -- 应用最大模原理
      sorry
    sorry
  · -- 证明 |f'(0)| ≤ 1
    sorry

/-- Schwarz引理的等号情形 -/
theorem schwarz_lemma_equality (hf : DifferentiableOn ℂ f (ball 0 1))
    (hf0 : f 0 = 0) (hf_unit : MapsTo f (ball 0 1) (ball 0 1))
    (heq : ∃ z ∈ ball 0 1, z ≠ 0 ∧ ‖f z‖ = ‖z‖) :
    ∃ θ : ℝ, f = λ z => exp (I * θ) * z := by
  sorry

/-- Schwarz-Pick引理 -/
theorem schwarz_pick_lemma (hf : DifferentiableOn ℂ f (ball 0 1))
    (hf_unit : MapsTo f (ball 0 1) (ball 0 1)) (z w : ℂ) (hz : z ∈ ball 0 1) (hw : w ∈ ball 0 1) :
    abs ((f z - f w) / (1 - conj (f w) * f z)) ≤ abs ((z - w) / (1 - conj w * z)) := by
  sorry

end SchwarzLemma
```

## 数学背景

Schwarz引理由Hermann Schwarz在1869年左右证明（虽然Karl Weierstrass也有类似结果），是复分析中最经典和最有用的结果之一。该引理给出了单位圆盘上保持原点的全纯映射的严格约束，揭示了这类映射的几何刚性。Schwarz引理是证明Riemann映射定理唯一性部分、研究单位圆盘自同构群和研究双曲几何的基础工具。

## 直观解释

Schwarz引理告诉我们：**单位圆盘到自身的全纯映射（保持原点）是"压缩"的**。

想象单位圆盘是一张橡皮膜，映射 $f$ 是拉伸或压缩。Schwarz引理说，如果 $f$ 把原点映射到原点，并且不超出圆盘，那么它不能太"激进"——每一点的像必须比原像更靠近原点（或相等）。这就像说，在保持原点的条件下，全纯映射只能"收缩"不能"膨胀"。

## 形式化表述

设 $f: \mathbb{D} \to \mathbb{D}$ 全纯（$\mathbb{D} = \{z : |z| < 1\}$），且 $f(0) = 0$。

**Schwarz引理**：

1. **压缩性质**：$|f(z)| \leq |z|$ 对所有 $z \in \mathbb{D}$
2. **导数约束**：$|f'(0)| \leq 1$

**等号情形**：

- 若存在 $z_0 \neq 0$ 使 $|f(z_0)| = |z_0|$，或 $|f'(0)| = 1$
- 则 $f(z) = e^{i\theta}z$（旋转）

## 证明思路

1. **定义辅助函数**：
   $$g(z) = \begin{cases} \frac{f(z)}{z} & z \neq 0 \\ f'(0) & z = 0 \end{cases}$$

2. **全纯性**：
   - $g$ 在 $\mathbb{D} \setminus \{0\}$ 全纯
   - 在 $z = 0$ 有可去奇点，由Riemann可去奇点定理，$g$ 在 $\mathbb{D}$ 全纯

3. **最大模原理**：
   - 对 $|z| = r < 1$：$|g(z)| = \frac{|f(z)|}{|z|} \leq \frac{1}{r}$
   - 令 $r \to 1$，得 $|g(z)| \leq 1$ 在 $\mathbb{D}$

4. **结论**：$|f(z)| \leq |z|$，$|f'(0)| = |g(0)| \leq 1$

核心洞察是 $g$ 的构造和最大模原理的应用。

## 示例

### 示例 1：旋转

$f(z) = e^{i\theta}z$，$|f(z)| = |z|$，达到等号。

这是Schwarz引理中等号成立的唯一情形。

### 示例 2：平方映射

$f(z) = z^2$，$f(0) = 0$，$|f(z)| = |z|^2 \leq |z|$（当 $|z| \leq 1$）。

严格压缩（除原点外）。$f'(0) = 0$。

### 示例 3：Möbius变换

$f(z) = \frac{z-a}{1-\bar{a}z}$，其中 $|a| < 1$。

这是单位圆盘的自同构，但 $f(0) = -a \neq 0$（除非 $a = 0$）。

## 应用

- **单位圆盘自同构**：完全分类 $\text{Aut}(\mathbb{D})$
- **双曲几何**：Poincaré度量的等距
- **Pick插值**：Nevanlinna-Pick理论
- **算子理论**：压缩算子的函数演算
- **动力系统**：圆盘上的迭代理论

## 相关概念

- 单位圆盘 (Unit Disc)：复平面的开单位球
- [最大模原理 (Maximum Modulus Principle)](./maximum-modulus-principle.md)：全纯函数的约束
- Möbius变换 (Möbius Transformation)：分式线性变换
- 双曲几何 (Hyperbolic Geometry)：非欧几何
- Poincaré度量 (Poincaré Metric)：双曲空间的度量

## 参考

### 教材

- [Ahlfors. Complex Analysis. McGraw-Hill, 3rd edition, 1979. Chapter 4]
- [Stein & Shakarchi. Complex Analysis. Princeton, 2003. Chapter 8]

### 历史文献

- [Schwarz. Zur Theorie der Abbildung. 1869]

### 在线资源

- [Mathlib4 文档 - SchwarzLemma][https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/SchwarzLemma.html](需更新)
- [Wikipedia - Schwarz Lemma](https://en.wikipedia.org/wiki/Schwarz_lemma)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
