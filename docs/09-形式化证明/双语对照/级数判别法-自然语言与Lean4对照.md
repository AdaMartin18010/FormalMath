---
title: "级数收敛判别法 自然语言与 Lean4 对照"
level: "silver"
target_courses:
  - "MIT 18.100A"
---

## 定理陈述

**自然语言**：
1. **比较判别法**（Comparison Test）：设 $\sum b_n$ 是收敛的正项级数，若 $|a_n| \leq b_n$ 对所有充分大的 $n$ 成立，则 $\sum a_n$ **绝对收敛**。
2. **比值判别法**（Ratio Test）：若 $\limsup_{n \to \infty} |a_{n+1}/a_n| = L < 1$，则 $\sum a_n$ 绝对收敛；若 $L > 1$，则发散。
3. **根值判别法**（Root Test）：若 $\limsup_{n \to \infty} |a_n|^{1/n} = L < 1$，则 $\sum a_n$ 绝对收敛；若 $L > 1$，则发散。

**Lean4**：

```lean
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.NormedSpace.Basic

namespace SeriesConvergenceTests
open BigOperators Topology

-- 比较判别法
theorem comparison_test {a b : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (hle : ∀ n, a n ≤ b n) (hsum : Summable b) : Summable a := by
  apply Summable.of_nonneg_of_le ha hle hsum

-- 绝对收敛的比较判别法
theorem comparison_test_abs {a b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    (hle : ∀ n, |a n| ≤ b n) (hsum : Summable b) : Summable a := by
  have h_abs : Summable (fun n => |a n|) := by
    apply Summable.of_nonneg_of_le (fun n => abs_nonneg (a n)) hle hsum
  exact summable_of_abs_summable h_abs

-- 比值判别法（简化版本）
theorem ratio_test {a : ℕ → ℝ} (ha : ∀ n, a n ≠ 0) {L : ℝ}
    (hL : L < 1) (hlim : Tendsto (fun n => |a (n + 1) / a n|) atTop (𝓝 L)) :
    Summable a := by
  sorry  -- 构造几何级数控制项

-- 根值判别法（简化版本）
theorem root_test {a : ℕ → ℝ} {L : ℝ} (hL : L < 1)
    (hlim : Tendsto (fun n => (|a n|) ^ (1 / n : ℝ)) atTop (𝓝 L)) :
    Summable a := by
  sorry
end SeriesConvergenceTests
```

## 证明思路

**自然语言**：
- **比较判别法**：由于 $0 \leq |a_n| \leq b_n$ 且 $\sum b_n$ 收敛，部分和 $\sum_{k=1}^n |a_k|$ 单调递增且有上界，故收敛。
- **比值判别法**：当 $L < 1$ 时，取 $r$ 满足 $L < r < 1$。存在 $N$ 使得 $n \geq N$ 时 $|a_{n+1}/a_n| < r$，从而 $|a_{N+k}| \leq |a_N| r^k$。后者与几何级数比较即得绝对收敛。
- **根值判别法**：类似地，当 $L < 1$ 时，$|a_n| \leq r^n$（对某个 $r < 1$ 和充分大的 $n$），再与几何级数比较。

**Lean4**：`Summable.of_nonneg_of_le` 是比较判别法的直接实现。`summable_of_abs_summable` 则从绝对收敛推出收敛。比值/根值判别法的完整证明需要用到 `Tendsto` 的定义来提取控制不等式，再结合几何级数的收敛性 `summable_geometric_of_norm_lt_one`。

## 关键 tactic/概念 教学

- `Summable`：级数收敛的抽象定义，基于部分和的极限存在。
- `Summable.of_nonneg_of_le`：非负项级数的比较判别法。
- `summable_of_abs_summable`：绝对收敛 ⇒ 收敛。
- `Tendsto f atTop (𝓝 L)`：序列 $f(n)$ 收敛到 $L$ 的滤子表述。
- `summable_geometric_of_norm_lt_one`：几何级数收敛定理。

## 练习

1. 判断 $\sum_{n=1}^\infty \frac{n^2}{2^n}$ 的收敛性，并在 Lean4 中尝试用比值判别法验证。
2. 判断 $\sum_{n=1}^\infty \frac{1}{(\ln n)^n}$（$n \geq 2$）的收敛性，说明为何根值判别法特别有效。
3. 构造一个级数使得比值判别法失效（$L = 1$）但根值判别法可以判定收敛。
