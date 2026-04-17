---
title: "群的类方程与 p-群中心非平凡性 自然语言与 Lean4 对照"
level: "silver"
target_courses:
  - "MIT 18.701"
---

## 定理陈述

**自然语言**：设 \(G\) 是有限群。
1. **类方程（Class Equation）**：
\[
|G| = |Z(G)| + \sum_{i} [G : C_G(g_i)]
\]
其中 \(Z(G)\) 是群的中心，求和取遍所有非平凡共轭类的代表元 \(g_i\)，\(C_G(g_i)\) 是 \(g_i\) 的中心化子。
2. **p-群中心非平凡性**：若 \(|G| = p^n\)（\(p\) 为素数，\(n \geq 1\)），则群的中心 \(Z(G)\) 非平凡，即 \(|Z(G)| > 1\)。

**Lean4**：

```lean
import Mathlib.GroupTheory.ClassEquation
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Data.Fintype.Basic

universe u
namespace ClassEquationTheorem
open Subgroup Group ConjClasses

variable {G : Type u} [Group G] [Fintype G]

-- 类方程（框架形式）
theorem class_equation :
    Fintype.card G = Fintype.card (center G) +
    ∑ g ∈ ({x : G | x ∉ center G} : Set G).toFinset,
      (index (centralizer {g})) := by
  sorry

-- p-群中心非平凡
theorem p_group_center_nontrivial {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : n > 0)
    (hG : Fintype.card G = p ^ n) :
    Fintype.card (center G) > 1 := by
  sorry
end ClassEquationTheorem
```

## 证明思路

**自然语言**：
1. **类方程的证明**：
   - 共轭作用是 \(G\) 在自身上的一个群作用。由轨道-稳定化子定理，每个元素 \(g\) 的轨道（即共轭类）大小为 \([G : C_G(g)]\)。
   - 若 \(g \in Z(G)\)，则其共轭类只含自身，大小为 \(1\)。
   - 将 \(G\) 按共轭类划分，合并所有单点共轭类即得中心 \(Z(G)\)，其余共轭类的大小为 \([G : C_G(g_i)]\)。计数即得类方程。

2. **p-群中心非平凡性的证明**：
   - 设 \(|G| = p^n\)（\(n \geq 1\)）。由类方程：
     \[
     p^n = |Z(G)| + \sum_i [G : C(g_i)].
     \]
   - 对每个非中心元素 \(g_i\)，其中心化子 \(C_G(g_i)\) 是真子群，故 \([G : C_G(g_i)]\) 是 \(p^n\) 的一个真因子，从而是 \(p\) 的倍数。
   - 因此 \(\sum_i [G : C_G(g_i)]\) 可被 \(p\) 整除。
   - 又 \(p^n\) 可被 \(p\) 整除，故 \(|Z(G)| = p^n - \sum_i [G : C_G(g_i)]\) 也可被 \(p\) 整除。
   - 由于单位元 \(1 \in Z(G)\)，有 \(|Z(G)| \geq 1\)，结合 \(p \mid |Z(G)|\) 可得 \(|Z(G)| \geq p > 1\)。因此中心非平凡。

**Lean4**：上述代码给出了定理的框架陈述。`class_equation` 将群的大小分解为中心大小与非平凡共轭类轨道大小之和；`p_group_center_nontrivial` 利用类方程和 \(p\)-群的性质证明中心元素个数严格大于 1。完整的形式化证明需要深入展开轨道-稳定化子定理和共轭类的计数。

## 关键 tactic/概念 教学

- `center G`：Mathlib4 中群的中心，即与所有元素可交换的元素集合。
- `centralizer {g}`：元素 \(g\) 的中心化子。
- `index (centralizer {g})`：中心化子在 \(G\) 中的指数，等于共轭类的大小。
- 类方程的本质是 **轨道分解公式** 在共轭作用下的特例。

## 练习

1. 利用类方程证明：每个 \(p^2\) 阶群都是交换群。
2. 设 \(G\) 是有限群，\(p\) 是整除 \(|G|\) 的最小素因子。证明：若 \(H \leq G\) 且 \([G:H] = p\)，则 \(H \trianglelefteq G\)。
3. 在 Lean4 中写出轨道-稳定化子定理的陈述（提示：使用 `MulAction.orbit` 与 `MulAction.stabilizer`）。
