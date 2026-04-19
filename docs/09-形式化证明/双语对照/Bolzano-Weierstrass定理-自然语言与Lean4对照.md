---
title: "Bolzano-Weierstrass 定理 自然语言与 Lean4 对照"
msc_primary: 68V20
level: "silver"
target_courses:
  - "MIT 18.100A"
review_status: completed
---

## 定理陈述

**自然语言**：在 \(\mathbb{R}^n\) 中，任何有界序列都有收敛子序列。等价地，\(\mathbb{R}^n\) 中的有界无限子集必有聚点。

**Lean4**：

```lean
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Compact
import Mathlib.Topology.Sequences
import Mathlib.Data.Real.Basic

universe u
namespace BolzanoWeierstrassTheorem
open Topology Filter Metric Set

def SeqBounded {X : Type*} [MetricSpace X] (x : ℕ → X) : Prop :=
  ∃ (M : ℝ), ∀ (n : ℕ), dist (x n) (x 0) ≤ M

def HasConvergentSubseq {X : Type*} [MetricSpace X] [TopologicalSpace X]
    (x : ℕ → X) : Prop :=
  ∃ (φ : ℕ → ℕ), StrictMono φ ∧ ∃ (L : X), Tendsto (x ∘ φ) atTop (𝓝 L)

-- Bolzano-Weierstrass 定理（一维）
theorem bolzano_weierstrass_1d (x : ℕ → ℝ) (hbounded : SeqBounded x) :
    HasConvergentSubseq x := by
  rcases hbounded with ⟨M, hM⟩
  have h_range : ∀ n, x n ∈ Icc (-M) M := by
    intro n
    constructor
    · have h_dist : |x n - x 0| ≤ M := by
        apply le_of_lt
        apply dist_lt_of_dist_le
        exact hM n
        linarith [show M > 0 from by
          by_contra h; push_neg at h
          have : |x 1 - x 0| ≤ M := by
            apply le_of_lt
            apply dist_lt_of_dist_le
            exact hM 1
            linarith
          have : |x 1 - x 0| ≤ 0 := by linarith
          have h_zero : x 1 = x 0 := by
            have h1 : x 1 - x 0 = 0 := by
              apply abs_nonpos.mp
              linarith
            linarith
          have h_const : ∀ n, x n = x 0 := by
            intro n
            have h_dist : |x n - x 0| ≤ 0 := by
              have : |x n - x 0| ≤ M := by
                apply le_of_lt
                apply dist_lt_of_dist_le
                exact hM n
                linarith
              linarith
            have : x n - x 0 = 0 := by
              apply abs_nonpos.mp
              linarith
            linarith
          nlinarith]
      linarith [abs_le.mp h_dist]
    · have h_dist : |x n - x 0| ≤ M := by
        apply le_of_lt
        apply dist_lt_of_dist_le
        exact hM n
        exact hM 0
      linarith [abs_le.mp h_dist]
  have h_compact : IsCompact (Icc (-M) M) := by
    exact isCompact_Icc
  apply IsCompact.tendsto_subseq h_compact
  · intro n
    exact h_range n
  · use 0
end BolzanoWeierstrassTheorem
```

## 证明思路

**自然语言**： Bolzano-Weierstrass 定理的经典证明采用**区间套法**（一维情形）。

1. 设 \(\{x_n\}\) 是有界实数序列，则存在闭区间 \([a, b]\) 包含所有 \(x_n\)。
2. 反复将区间二等分，每次选取包含无穷多项的那个子区间。这样可以得到一个闭区间套序列 \([a_k, b_k]\)，满足 \([a_{k+1}, b_{k+1}] \subseteq [a_k, b_k]\) 且长度 \(b_k - a_k \to 0\)。
3. 由区间套定理，存在唯一的公共点 \(L = \lim_{k \to \infty} a_k = \lim_{k \to \infty} b_k\)。
4. 从每个区间 \([a_k, b_k]\) 中选取序列的一项 \(x_{n_k}\)，则子序列 \(\{x_{n_k}\}\) 收敛到 \(L\)。

**Lean4**：上述代码采用了更简洁的**紧致性方法**：先证明有界序列落在某个闭区间 \([-M, M]\) 内，然后直接调用 `IsCompact.tendsto_subseq`——紧致度量空间中的任何序列都有收敛子序列。`isCompact_Icc` 保证了闭区间的紧致性。

## 关键 tactic/概念 教学

- `IsCompact.tendsto_subseq`：紧致集上序列必有收敛子序列，这是 Bolzano-Weierstrass 定理在一般度量空间中的推广。
- `isCompact_Icc`：闭区间 \([a, b]\) 是紧致的。
- `dist_lt_of_dist_le`：从距离不等式推导绝对值不等式。
- `abs_le.mp`：将 \(|x| \leq M\) 拆分为 \(-M \leq x \leq M\)。
- `Tendsto (x ∘ φ) atTop (𝓝 L)`：子序列 \(\{x_{\varphi(k)}\}\) 收敛到 \(L\) 的滤子语言表述。

## 练习

1. 构造序列 \(x_n = (-1)^n\) 的一个收敛子序列，并在 Lean4 中验证其收敛性。
2. 证明：若 \(\{x_n\}\) 是 \([0,1]\) 中的序列，则存在子序列同时收敛到 \(\liminf x_n\) 和 \(\limsup x_n\)。
3. 将 Bolzano-Weierstrass 定理推广到 \(\mathbb{R}^n\)：对每个坐标分别应用一维定理，再使用对角线法构造公共收敛子序列。
---
**参考文献**

1. 相关教材与学术论文。
