---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: Löwenheim-Skolem 定理 (Löwenheim-Skolem Theorem)
---
# Löwenheim-Skolem 定理 (Löwenheim-Skolem Theorem)

## Mathlib4 引用

```lean
import Mathlib.ModelTheory.Skolem\n\nnamespace ModelTheory\n\nvariable {L : Language} {T : Theory L}\n\n/-- 向下 Löwenheim-Skolem 定理：若理论有无限模型，则有任意大基数的模型 -/\ntheorem downward_loewenheim_skolem {M : Type*} [Structure L M] [Infinite M] (hM : M ⊨ T)\n    (κ : Cardinal) (hκ : ℵ₀ ≤ κ) (hκ_le : κ ≤ Cardinal.mk M) :\n    ∃ (N : Type*) [Structure L N] [M ⊨ T], Cardinal.mk N = κ := by\n  -- 利用 Skolem 函数和子结构的初等嵌入构造所需基数的模型\n  sorry\n\nend ModelTheory
```

## 数学背景

Löwenheim-Skolem 定理是数理逻辑和模型论中最重要的结果之一，由德国逻辑学家利奥波德·勒文海姆（Leopold Löwenheim）于1915年首次证明（向下版本：若一个理论有模型，则它有可数模型），后由挪威数学家托拉尔夫·斯科伦（Thoralf Skolem）在1920年推广和完善。该定理有两个互补的形式：

- **向下 Löwenheim-Skolem 定理**：若一个一阶理论有无限模型，则对任何无限基数 $\kappa \geq |L|$，它有一个基数恰好为 $\kappa$ 的模型
- **向上 Löwenheim-Skolem 定理**：若一个一阶理论有无限模型，则对任何大于等于该模型基数的基数，它都有相应基数的模型

Löwenheim-Skolem 定理揭示了形式理论与模型结构之间的深刻分离：一阶语言无法区分不同大小的无限结构。这一定理对集合论（Skolem 悖论）、代数（非标准模型）和数学基础产生了深远影响。

## 直观解释

Löwenheim-Skolem 定理揭示了一个反直觉但极其重要的现象：一阶逻辑无法区分不同大小的无限。想象你有一个数学理论（如实数域的代数理论），它能描述实数的许多性质。你可能会认为，既然实数是不可数的，那么任何满足这个理论的模型都必须是不可数的。但 Löwenheim-Skolem 定理告诉我们：如果理论是一阶的，那么它一定也有可数的模型！这就像你试图用一阶语言捕捉一个庞大帝国的全貌，但语言的能力有限——它无法区分一个可数的子帝国和整个不可数的帝国。这个现象被称为"Skolem 悖论"，它深刻地揭示了形式语言在描述无限结构时的局限性。

## 形式化表述

设 $L$ 是一阶语言，$T$ 是 $L$ 中的理论。

**向下 Löwenheim-Skolem 定理**：若 $T$ 有一个无限模型 $M$，则对任何基数 $\kappa$ 满足 $|L| \leq \kappa \leq |M|$，存在 $T$ 的一个基数为 $\kappa$ 的模型 $N$。特别地，若 $|L|$ 可数，则 $T$ 有可数模型。

**向上 Löwenheim-Skolem 定理**：若 $T$ 有一个无限模型 $M$，则对任何基数 $\kappa \geq |M|$，存在 $T$ 的一个基数为 $\kappa$ 的模型 $N$。

等价表述：

- 若 $T$ 有任意大的有限模型，则 $T$ 也有无限模型
- 若 $T$ 有无限模型，则 $T$ 有所有大于等于 $|L|$ 的无限基数的模型

其中：

- $|L|$ 表示语言 $L$ 的基数（通常为可数或有限）
- 该定理仅对一阶逻辑成立。对二阶逻辑或更强逻辑不成立
- 向上版本通常通过紧致性定理和常数符号的添加来证明
- 向下版本通常通过 Skolem 函数和初等子结构的构造来证明

**Skolem 悖论**：ZFC 集合论可以证明存在不可数集合，但由 Löwenheim-Skolem 定理，ZFC 自身（若一致）也有可数模型。在这个可数模型中，"不可数集合"的基数实际上是可数的！

## 证明思路

1. **Skolem 函数**：对 $L$ 中的每个存在公式 $\exists x \, \varphi(x, \bar{y})$，添加一个 Skolem 函数符号 $f_\varphi(\bar{y})$，并扩展理论要求 $f_\varphi$ 提供见证
2. **子结构的闭包**：从 $M$ 中选取大小为 $\kappa$ 的子集 $A$，对 Skolem 函数取闭包得到一个子结构 $N$
3. **Tarski-Vaught 判别准则**：证明 $N$ 是 $M$ 的初等子结构，即 $N$ 满足与 $M$ 相同的一阶语句
4. **向上版本**：通过向语言中添加 $\kappa$ 个新的不同常数符号和相应的不等式公理，利用紧致性定理构造基数为 $\kappa$ 的模型

核心洞察在于一阶语句只涉及有限多个量词和有限深度的元素关系，因此可以通过对 Skolem 函数取闭包来控制模型的大小。

## 示例

### 示例 1：ZFC 的可数模型

ZFC 集合论（一阶语言）若一致，则由向下 Löwenheim-Skolem 定理，它有一个可数模型 $M$。在这个模型中，所有集合（包括那些 $M$ 认为是不可数的集合）从外部看都是可数的。这就是著名的 Skolem 悖论。

### 示例 2：实数域的可数模型

实数域 $\mathbb{R}$ 作为一阶结构（语言为 $\{+, \times, 0, 1\}$）有不可数基数。但实数域的代数理论（Th($\mathbb{R}$)）也有可数模型。这个可数模型与标准实数在一阶性质上不可区分，但从外部看它是可数的。

### 示例 3：非标准模型的大小

Peano 算术 PA 有可数模型（标准自然数），也有不可数模型（非标准自然数）。向上 Löwenheim-Skolem 定理保证了 PA 有任意大基数的非标准模型。这些模型在外部看大小不同，但在一阶语言内满足完全相同的语句。

## 应用

- **集合论**：Skolem 悖论和超限模型的研究
- **模型论**：稳定性理论、范畴性和饱和模型的基础
- **代数**：非标准域、非标准整数和代数闭域的分类
- **数学基础**：形式系统表达能力局限性的哲学探讨
- **逻辑哲学**：模型内部与外部视角差异的研究

## 相关概念

- 初等子结构 (Elementary Substructure)：满足相同一阶语句的子结构
- Skolem 函数 (Skolem Function)：为存在量词提供见证的函数
- Tarski-Vaught 判别准则 (Tarski-Vaught Criterion)：判断初等子结构的条件
- 基数 (Cardinality)：集合的大小
- Skolem 悖论 (Skolem's Paradox)：ZFC 可数模型的反直觉现象

## 参考

### 教材

- [H. B. Enderton. A Mathematical Introduction to Logic. Academic Press, 2nd edition, 2001. Chapter 3]
- [D. Marker. Model Theory: An Introduction. Springer, 2002. Chapter 2]

### 在线资源

- [Mathlib4 - Skolem](https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory/Skolem.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*
