---
title: "Taylor 定理（带 Lagrange 余项）自然语言与 Lean4 对照"
msc_primary: 68V20
level: "silver"
target_courses:
  - "MIT 18.100A"
review_status: completed
---

## 定理陈述

**自然语言**：设函数 $f$ 在包含 $x_0$ 的某个开区间内有 $n+1$ 阶连续导数，则对该区间内任意 $x$，存在 $\xi$ 位于 $x_0$ 与 $x$ 之间，使得
\[
f(x) = \sum_{k=0}^{n} \frac{f^{(k)}(x_0)}{k!}(x - x_0)^k + \frac{f^{(n+1)}(\xi)}{(n+1)!}(x - x_0)^{n+1}.
\]
其中最后一项称为 **Lagrange 余项**。

**Lean4**：

```lean
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor

namespace TaylorTheorem
open Real Set

-- 带 Lagrange 余项的 Taylor 定理
theorem taylor_lagrange {f : ℝ → ℝ} {x₀ x : ℝ} {n : ℕ}
    (hdiff : ContDiffOn ℝ (n + 1) f (Icc (min x₀ x) (max x₀ x))) :
    ∃ ξ ∈ Ioo (min x₀ x) (max x₀ x),
    f x = ∑ i ∈ Finset.range (n + 1),
            (iteratedDeriv i f x₀) * (x - x₀) ^ i / Nat.factorial i +
          iteratedDeriv (n + 1) f ξ * (x - x₀) ^ (n + 1) / Nat.factorial (n + 1) := by
  have h : x₀ ≤ x ∨ x ≤ x₀ := le_total x₀ x
  rcases h with hle | hge
  · rw [min_eq_left hle, max_eq_right hle] at hdiff
    have htaylor := taylor_mean_remainder_lagrange hdiff (by simp [hle]) n
    rcases htaylor with ⟨ξ, hξ, heq⟩
    use ξ
    constructor
    · exact hξ
    · rw [heq]
      field_simp
      <;> ring_nf <;> simp [mul_comm]
  · rw [min_eq_right (le_of_not_le hle), max_eq_left (le_of_not_le hle)] at hdiff
    have hge' : x ≤ x₀ := by linarith
    have htaylor := taylor_mean_remainder_lagrange hdiff (by simp [hge']) n
    rcases htaylor with ⟨ξ, hξ, heq⟩
    use ξ
    constructor
    · exact hξ
    · rw [heq]
      field_simp
      <;> ring_nf <;> simp [mul_comm]
end TaylorTheorem
```

## 证明思路

**自然语言**：Taylor 定理的经典证明采用**归纳法**结合**中值定理**（或 Cauchy 中值定理）。一个更简洁的方法如下：
1. 构造辅助函数
   $$g(t) = f(x) - \sum_{k=0}^n \frac{f^{(k)}(t)}{k!}(x - t)^k - \frac{R}{(n+1)!}(x - t)^{n+1},$$
   其中 $R$ 是一个待定常数，使得 $g(x_0) = 0$。
2. 验证 $g(x) = 0$。
3. 由 Rolle 定理，存在 $\xi$ 介于 $x_0$ 与 $x$ 之间使得 $g'(\xi) = 0$。
4. 直接计算 $g'(t)$ 可以发现大部分项相互抵消，最终得到 $g'(t) = -\frac{f^{(n+1)}(t)}{n!}(x - t)^n + \frac{R}{n!}(x - t)^n$。
5. 令 $g'(\xi) = 0$ 即得 $R = f^{(n+1)}(\xi)$。

**Lean4**：Mathlib4 中的 `taylor_mean_remainder_lagrange` 直接给出了带 Lagrange 余项的 Taylor 定理。代码中需要分 $x_0 \leq x$ 和 $x \leq x_0$ 两种情形来处理积分区间的定义域。

## 关键 tactic/概念 教学

- `ContDiffOn ℝ (n + 1) f S`：函数 $f$ 在集合 $S$ 上 $n+1$ 阶连续可微。
- `iteratedDeriv k f x₀`：$f$ 在 $x_0$ 处的 $k$ 阶导数 $f^{(k)}(x_0)$。
- `taylor_mean_remainder_lagrange`：Mathlib4 中带 Lagrange 余项的 Taylor 定理。
- `min x₀ x` / `max x₀ x`：处理 $x$ 在 $x_0$ 左右两侧时积分区间的统一写法。
- `field_simp <;> ring_nf <;> simp [mul_comm]`：化简分式和多项式表达式的组合 tactic。

## 练习

1. 取 $n = 0$，验证 Taylor 定理退化为中值定理。
2. 写出 $f(x) = e^x$ 在 $x_0 = 0$ 处的 $n$ 阶 Taylor 展开，并证明对任意固定 $x$，当 $n \to \infty$ 时余项趋于 0。
3. 在 Lean4 中验证 $\sin(x)$ 在 $x_0 = 0$ 处的 3 阶 Taylor 展开：$\sin(x) = x - x^3/6 + R_4(x)$。
---
**参考文献**

1. 相关教材与学术论文。
