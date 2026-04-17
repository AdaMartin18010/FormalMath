---
title: "一致连续性与 Heine-Cantor 定理 自然语言与 Lean4 对照"
level: "silver"
target_courses:
  - "MIT 18.100A"
---

## 定理陈述

**自然语言**：设 $f: X \to Y$ 是从紧致度量空间 $(X, d_X)$ 到度量空间 $(Y, d_Y)$ 的连续函数，则 $f$ 在 $X$ 上是**一致连续**的。即：对任意 $\varepsilon > 0$，存在 $\delta > 0$，使得对任意 $x, y \in X$，只要 $d_X(x, y) < \delta$，就有 $d_Y(f(x), f(y)) < \varepsilon$。

**Lean4**：

```lean
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.UniformSpace.Basic

namespace HeineCantorTheorem
open Topology Metric

-- 一致连续性的度量空间定义
def UniformlyContinuous' {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x y : X, dist x y < δ → dist (f x) (f y) < ε

-- Heine-Cantor 定理
theorem heine_cantor {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] {f : X → Y} (hf : Continuous f) :
    UniformlyContinuous' f := by
  have huc : UniformContinuous f := by
    apply CompactSpace.uniformContinuous_of_continuous hf
  rw [Metric.uniformContinuous_iff] at huc
  exact huc

-- 闭区间上的经典版本
theorem heine_cantor_Icc {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) :
    ∀ ε > 0, ∃ δ > 0, ∀ x y : ℝ, x ∈ Icc a b → y ∈ Icc a b →
      |x - y| < δ → |f x - f y| < ε := by
  sorry  -- 利用紧致性与连续性推导
end HeineCantorTheorem
```

## 证明思路

**自然语言**：Heine-Cantor 定理的经典证明采用反证法：
1. 假设 $f$ 不一致连续，则存在 $\varepsilon > 0$ 使得对所有 $\delta = 1/n$，都有点 $x_n, y_n$ 满足 $|x_n - y_n| < 1/n$ 但 $|f(x_n) - f(y_n)| \geq \varepsilon$。
2. 由 $X$ 的紧致性，$\{x_n\}$ 有收敛子列 $x_{n_k} \to x$。
3. 由于 $|x_{n_k} - y_{n_k}| \to 0$，也有 $y_{n_k} \to x$。
4. 由 $f$ 的连续性，$f(x_{n_k}) \to f(x)$ 且 $f(y_{n_k}) \to f(x)$，从而 $|f(x_{n_k}) - f(y_{n_k})| \to 0$，这与 $|f(x_{n_k}) - f(y_{n_k})| \geq \varepsilon$ 矛盾。

**Lean4**：Mathlib4 中 `CompactSpace.uniformContinuous_of_continuous` 直接给出了拓扑版本的一致连续性。然后通过 `Metric.uniformContinuous_iff` 将滤子语言转换为更直观的 $\varepsilon$-$\delta$ 表述。

## 关键 tactic/概念 教学

- `UniformContinuous`：拓扑学中的一致连续性，基于均匀结构（uniform structure）。
- `CompactSpace.uniformContinuous_of_continuous`：Heine-Cantor 定理的核心形式。
- `Metric.uniformContinuous_iff`：将拓扑一致连续性翻译为度量空间的 $\varepsilon$-$\delta$ 定义。
- `dist x y`：度量空间中的距离函数，在 $\mathbb{R}$ 上等同于 `|x - y|`。
- `ContinuousOn` / `Continuous`：集合上的连续性与全局连续性。

## 练习

1. 证明 $f(x) = 1/x$ 在 $(0, 1]$ 上连续但不一致连续，说明紧致性条件不可去掉。
2. 证明 $f(x) = \sqrt{x}$ 在 $[0, 1]$ 上一致连续，并尝试在 Lean4 中给出 $\delta$ 关于 $\varepsilon$ 的显式表达式。
3. 设 $f: \mathbb{R} \to \mathbb{R}$ 连续且周期为 $T$，证明 $f$ 在 $\mathbb{R}$ 上一致连续。
