---
title: "霍尔婚配定理 自然语言与 Lean4 对照"
msc_primary: 68V20
level: "silver"
target_courses:
  - "MIT 18.310 / 组合数学"
review_status: completed
---

## 定理陈述

**自然语言**：设 \(G = (X, Y, E)\) 是有限二分图。对于子集 \(S \subseteq X\)，令 \(N(S)\) 表示 \(S\) 的邻域。则存在覆盖 \(X\) 的匹配当且仅当霍尔条件成立：
\[
\forall S \subseteq X, \quad |N(S)| \geq |S|
\]

**Lean4**：

```lean
import Mathlib.Combinatorics.Hall.Marriage
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic

universe u v
namespace HallsMarriageTheorem
open Finset

variable {ι : Type u} [Fintype ι] {α : Type v}

-- 霍尔婚配定理：核心形式
theorem halls_marriage_theorem {t : ι → Finset α} :
    (∀ s : Finset ι, s.card ≤ (s.biUnion t).card) ↔
    ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  rw [Finset.all_card_le_biUnion_card_iff_exists_injective]
```

## 证明思路

**自然语言**：霍尔婚配定理的经典证明使用数学归纳法：

1. **基例**：\(|X| = 1\) 时，由霍尔条件知 \(N(X) \geq 1\)，故存在匹配。
2. **归纳步骤**：分两种情况讨论：
   - **情况 A**：对所有非空真子集 \(S \subsetneq X\)，严格不等式 \(|N(S)| > |S|\) 成立。此时可任选一条边加入匹配，然后对剩余图应用归纳假设。
   - **情况 B**：存在某个非空真子集 \(S\) 使得 \(|N(S)| = |S|\)。此时将图分成两部分：\(S \cup N(S)\) 和 \(X \setminus S \cup Y \setminus N(S)\)，分别应用归纳假设。

**Lean4**：Mathlib4 通过 `Finset.all_card_le_biUnion_card_iff_exists_injective` 直接封装了上述归纳证明。以下展示该定理的一个等价表述（使用嵌入 `↪`）以及“系统不同代表”（SDR）的应用：

```lean
-- 等价表述：存在单射嵌入
theorem halls_marriage_theorem' {t : ι → Finset α} :
    (∀ s : Finset ι, s.card ≤ (s.biUnion t).card) ↔
    ∃ f : ι ↪ α, ∀ x, f x ∈ t x := by
  rw [Finset.all_card_le_biUnion_card_iff_exists_injective']

-- 系统不同代表（SDR）
theorem sdr_exists {ι : Type u} [Fintype ι] {α : Type v} {A : ι → Finset α} :
    (∃ f : ι → α, Function.Injective f ∧ ∀ i, f i ∈ A i) ↔
    ∀ s : Finset ι, s.card ≤ (s.biUnion A).card := by
  rw [← halls_marriage_theorem]
```

## 关键 tactic 教学

- `rw [lemma]`：`rewrite` 的缩写，用等式或等价关系替换目标中的表达式。`←` 表示反向重写。
- `constructor`：将 `↔` 目标拆分为 `→` 和 `←` 两个子目标。
- `intro` / `rcases`：`intro` 引入假设；`rcases`（recursive cases）则用于对复杂结构（如存在量词、合取）进行模式匹配分解。

## 练习

1. 用霍尔婚配定理证明：每个 \(k\)-正则二分图都有完美匹配。
2. 将霍尔条件翻译成“婚配解释”：在什么条件下，每个男孩都能娶一个他认识的女孩？
3. 在 Lean4 中证明：若 \(|X| = |Y|\) 且霍尔条件成立，则存在完美匹配（即双射）。
---
**参考文献**

1. 相关教材与学术论文。
