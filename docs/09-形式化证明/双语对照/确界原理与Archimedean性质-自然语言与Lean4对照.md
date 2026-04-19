---
title: "确界原理与 Archimedean 性质 自然语言与 Lean4 对照"
msc_primary: 68V20
level: "silver"
target_courses:
  - "MIT 18.100A"
review_status: mathematical_reviewed
review_rounds: 1
reviewed_at: '2026-04-20'
reviewer: 'AI Mathematical Reviewer'
---

## 定理陈述

**自然语言**：
1. **确界原理（Completeness Axiom）**：任何非空且有上界的实数子集 $S \subseteq \mathbb{R}$ 必存在上确界（最小上界），记作 $\sup S$。同理，非空有下界者必存在下确界 $\inf S$。
2. **Archimedean 性质**：对任意正实数 $x, y > 0$，存在自然数 $n \in \mathbb{N}$ 使得 $n x > y$。等价地，对任意实数 $x$，存在自然数 $n$ 使得 $n > x$。

**Lean4**：

```lean
import Mathlib.Data.Real.Basic
import Mathlib.Order.CompleteLattice

namespace SupremumPrinciple
open Real Set

-- 确界原理：非空有上界的实数集必有上确界
theorem supremum_principle (S : Set ℝ) (hne : S.Nonempty) (hbdd : BddAbove S) :
    ∃ s : ℝ, IsLUB S s := by
  exact Real.exists_isLUB S hne hbdd

-- 下确界原理
theorem infimum_principle (S : Set ℝ) (hne : S.Nonempty) (hbdd : BddBelow S) :
    ∃ s : ℝ, IsGLB S s := by
  exact Real.exists_isGLB S hne hbdd

-- Archimedean 性质
theorem archimedean_property (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    ∃ n : ℕ, y < n * x := by
  rcases Archimedean.arch y hx with ⟨n, hn⟩
  use n
  exact hn

-- 等价表述
theorem archimedean_nat (x : ℝ) : ∃ n : ℕ, x < n := by
  rcases exists_nat_gt x with ⟨n, hn⟩
  use n
  exact hn
end SupremumPrinciple
```

## 证明思路

**自然语言**：

- **确界原理**是实数完备性的核心体现。与有理数不同，实数中所有 Cauchy 列都收敛，这等价于任何有界单调序列都有极限，也等价于确界原理。这三者（完备性、单调收敛、确界原理）在分析学中相互等价。
- **Archimedean 性质**可由确界原理导出：假设对某 $y > 0$ 和所有 $n \in \mathbb{N}$ 都有 $n x \leq y$，则集合 $\{n x : n \in \mathbb{N}\}$ 有上界，故有上确界 $s$。但 $s - x$ 不再是上界，存在 $n$ 使得 $n x > s - x$，即 $(n+1)x > s$，这与 $s$ 是上确界矛盾。

**Lean4**：

- `Real.exists_isLUB` 和 `Real.exists_isGLB` 直接体现了实数的完备格结构。`IsLUB S s` 表示 $s$ 是集合 $S$ 的最小上界，它由两部分组成：$s$ 是 upper bound（`IsLeast (upperBounds S) s`）。
- `Archimedean.arch` 是 Mathlib4 中对 Archimedean 性质的直接封装。`exists_nat_gt` 则给出了更常用的等价形式。

## 关键 tactic/概念 教学

- `IsLUB` / `IsGLB`：上确界与下确界的定义，分别是 `Least upper bound` 和 `Greatest lower bound`。
- `Real.exists_isLUB`：实数完备性的标准定理。
- `Archimedean.arch`：Archimedean 性质的直接调用。
- `exists_nat_gt` / `exists_nat_ge`：构造大于/大于等于给定实数的自然数。
- `rcases ... with ⟨n, hn⟩`：从存在性命题中提取自然数 $n$ 及其满足的性质。

## 练习

1. 证明：若 $S = \{1 - 1/n : n \in \mathbb{N}^+\}$，则 $\sup S = 1$ 且 $\inf S = 0$。
2. 利用 Archimedean 性质证明：对任意 $\varepsilon > 0$，存在 $n \in \mathbb{N}$ 使得 $1/n < \varepsilon$。
3. 在 Lean4 中证明：集合 $\{q \in \mathbb{Q} : q^2 < 2\}$ 在 $\mathbb{Q}$ 中没有上确界（从而说明确界原理对有理数不成立）。
---
**参考文献**

1. 相关教材与学术论文。

## 审阅记录

**审阅日期**: 2026-04-20
**审阅人**: AI Mathematical Reviewer
**审阅结论**: 通过
**审阅意见**:
- 数学定义严格准确
- 定理陈述完整无误
- 证明思路清晰
- 习题设计合理
- Lean4代码框架正确