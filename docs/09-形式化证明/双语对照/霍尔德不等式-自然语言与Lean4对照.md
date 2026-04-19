---
title: "Hölder 不等式 自然语言与 Lean4 对照"
msc_primary: 68V20
level: "silver"
target_courses:
  - "MIT 18.100A"
---

## 定理陈述

**自然语言**：设 \(p, q > 1\) 且 \(\frac{1}{p} + \frac{1}{q} = 1\)（称为共轭指数）。对于任意实数序列 \(a_i, b_i\)，有
\[
\sum_{i=1}^n |a_i b_i| \leq \left(\sum_{i=1}^n |a_i|^p\right)^{1/p} \left(\sum_{i=1}^n |b_i|^q\right)^{1/q}
\]
当 \(p = q = 2\) 时，这就是柯西-施瓦茨不等式。

**Lean4**：

```lean
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.NormedSpace.lpSpace
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace HolderInequality
open Real Finset BigOperators

-- 杨氏不等式
theorem young_inequality (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    {p q : ℝ} (hp : 1 < p) (hq : 1 < q) (hpq : 1/p + 1/q = 1) :
    a * b ≤ (a^p)/p + (b^q)/q := by
  sorry  -- 利用指数函数的凸性证明
```

## 证明思路

**自然语言**：Hölder 不等式的标准证明分为两步：

1. **杨氏不等式（Young's Inequality）**：对 \(a, b \geq 0\) 和共轭指数 \(p, q\)，有
   \[ab \leq \frac{a^p}{p} + \frac{b^q}{q}\]
   这可以通过指数函数 \(e^x\) 的凸性来证明。
2. **归一化方法**：不妨设 \(\sum |a_i|^p = \sum |b_i|^q = 1\)（否则将序列归一化）。对每一项应用杨氏不等式并求和，利用 \(\frac{1}{p} + \frac{1}{q} = 1\) 即得 \(\sum |a_i b_i| \leq 1\)。

**Lean4**：以下展示归一化版本的证明框架：

```lean
-- 离散 Hölder 不等式（归一化版本）
theorem holder_normalized {n : ℕ} (a b : Fin n → ℝ)
    {p q : ℝ} (hp : 1 < p) (hq : 1 < q) (hpq : 1/p + 1/q = 1)
    (ha : ∑ i, |a i| ^ p = 1) (hb : ∑ i, |b i| ^ q = 1) :
    ∑ i, |a i * b i| ≤ 1 := by
  calc
    ∑ i, |a i * b i| = ∑ i, |a i| * |b i| := by
      simp [abs_mul]
    _ ≤ ∑ i, ((|a i| ^ p)/p + (|b i| ^ q)/q) := by
      apply sum_le_sum
      intro i hi
      apply young_inequality
      · apply abs_nonneg
      · apply abs_nonneg
      · exact hp
      · exact hq
      · exact hpq
    _ = (∑ i, |a i| ^ p)/p + (∑ i, |b i| ^ q)/q := by
      simp [Finset.sum_add_distrib, Finset.sum_div]
    _ = 1/p + 1/q := by
      rw [ha, hb]
    _ = 1 := by
      exact hpq
```

## 关键 tactic 教学

- `calc`：链式等式/不等式推理。每一行给出当前的表达式和理由，自动传递关系。
- `sum_le_sum`：若对每个指标都有 \(x_i \leq y_i\)，则 \(\sum x_i \leq \sum y_i\)。
- `apply`：将定理应用到目标上。`apply young_inequality` 后，Lean 会自动生成对应的前提子目标。

## 练习

1. 补全 `young_inequality` 的证明（提示：利用 `exp` 和 `log` 的凸性）。
2. 从归一化版本推导一般 Hölder 不等式：如何处理 \(\sum |a_i|^p \neq 1\) 的情况？
3. 取 \(p = q = 2\)，说明 Hölder 不等式如何退化为柯西-施瓦茨不等式。
