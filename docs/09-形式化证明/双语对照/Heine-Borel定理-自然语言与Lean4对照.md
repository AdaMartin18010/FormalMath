---
title: "Heine-Borel 定理 自然语言与 Lean4 对照"
level: "silver"
target_courses:
  - "MIT 18.100A"
---

## 定理陈述

**自然语言**：在 \(\mathbb{R}^n\) 中，子集 \(K\) 是紧致的（每个开覆盖都有有限子覆盖）当且仅当 \(K\) 是闭集且有界集。

**Lean4**：

```lean
import Mathlib.Topology.MetricSpace.Compact
import Mathlib.Analysis.NormedSpace.FiniteDimension
import Mathlib.Data.Real.Basic

universe u
namespace HeineBorelTheorem
open Topology Metric Set Bornology

-- Heine-Borel 定理（ℝⁿ）
theorem heine_borel {n : ℕ} {K : Set (Fin n → ℝ)} :
    IsCompact K ↔ IsClosed K ∧ IsBounded K := by
  rw [isCompact_iff_isClosed_bounded]

-- 一维版本
theorem heine_borel_1d {K : Set ℝ} :
    IsCompact K ↔ IsClosed K ∧ IsBounded K := by
  rw [isCompact_iff_isClosed_bounded]

-- 闭区间紧致性
theorem compact_Icc {a b : ℝ} (hle : a ≤ b) : IsCompact (Icc a b) := by
  exact isCompact_Icc

-- 闭球的紧致性（ℝⁿ）
theorem compact_closedBall {n : ℕ} (x : Fin n → ℝ) (r : ℝ) (hr : 0 < r) :
    IsCompact (Metric.closedBall x r) := by
  apply isCompact_closedBall x hr
end HeineBorelTheorem
```

## 证明思路

**自然语言**：Heine-Borel 定理需要证明两个方向。

1. **紧致 ⟹ 闭且有界**：
   - **闭性**：在 Hausdorff 空间（如 \(\mathbb{R}^n\)）中，紧致集一定是闭集。证明思路是：对任意不在 \(K\) 中的点 \(x\)，利用 Hausdorff 性质为 \(x\) 和 \(K\) 中每一点构造不相交的开邻域。由紧致性，有限个这样的邻域即可覆盖 \(K\)，它们的交构成 \(x\) 的一个与 \(K\) 不相交的开邻域，因此 \(x\) 是 \(K\) 的补集的内点。
   - **有界性**：用一族以原点为中心、半径递增的开球覆盖 \(K\)。由紧致性，存在有限子覆盖，因此 \(K\) 包含在半径最大的那个球中，故 \(K\) 有界。

2. **闭且有界 ⟹ 紧致**：
   - 先证明闭区间 \([a, b]\) 是紧致的。这可以通过 Bolzano-Weierstrass 定理的区间套证明，或者直接证明任何开覆盖都有有限子覆盖（Lebesgue 数方法）。
   - 在 \(\mathbb{R}^n\) 中，有界闭集可以被包含在一个足够大的闭方体 \([-M, M]^n\) 中。
   - 有限个紧致集的乘积仍是紧致的（Tychonoff 定理的有限版本），因此 \([-M, M]^n\) 是紧致的。
   - 紧致集的闭子集仍是紧致的，所以 \(K\) 是紧致的。

**Lean4**：Mathlib4 的 `isCompact_iff_isClosed_bounded` 直接实现了 Heine-Borel 定理。上述代码同时展示了一维版本、闭区间的紧致性 `isCompact_Icc` 以及闭球的紧致性 `isCompact_closedBall`。

## 关键 tactic/概念 教学

- `isCompact_iff_isClosed_bounded`：Mathlib4 中 Heine-Borel 定理的核心实现。
- `IsCompact`：紧致性的拓扑定义（开覆盖的有限子覆盖）。
- `IsClosed`：闭集，即补集为开集。
- `IsBounded`：有界集，可被某个球包含。
- `isCompact_Icc`：闭区间紧致的标准引理。
- `isCompact_closedBall`：有限维赋范空间中闭球的紧致性。

## 练习

1. 证明单位球面 \(S^{n-1} = \{x \in \mathbb{R}^n \mid \|x\| = 1\}\) 是紧致的。
2. 举例说明：在无穷维赋范空间（如 \(\ell^2\)）中，闭单位球不是紧致的。
3. 在 Lean4 中证明：紧致集上的连续实值函数必能取到最大值和最小值（提示：使用 `IsCompact.exists_isMaxOn`）。
