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
import Mathlib.ModelTheory.Skolem
import Mathlib.ModelTheory.Satisfiability

namespace LowenheimSkolem

variable {L : Language.{u, v}} {T : Theory L} {M : Type w}
  [L.Structure M] [Nonempty M]

/-- 向上 Löwenheim-Skolem 定理：若 M ⊨ T 且 κ ≥ max(|L|, |M|)，
    则存在基数为 κ 的模型 N ⊨ T 使得 M ↪ N -/
theorem exists_elementarilyEquivalent_card_ge (hM : M ⊨ T)
    (κ : Cardinal) (hκ : κ ≥ max (Cardinal.mk M) L.card) :
    ∃ (N : Type*) (hN : L.Structure N), N ⊨ T ∧
      Nonempty (M ↪[L] N) ∧ Cardinal.mk N = κ := by
  -- 参见 Mathlib4 ModelTheory.Skolem 与相关模块
  sorry

/-- 向下 Löwenheim-Skolem 定理：对任意无穷模型 M ⊨ T 和
    任意无穷子集 A ⊆ M，存在初等子结构 N ≺ M 使得 A ⊆ N
    且 |N| ≤ max(|A|, |L|) -/
theorem exists_elementarySubstructure_card_le
    (hM : M ⊨ T) (A : Set M) (hA : A.Infinite) :
    ∃ (N : L.Substructure M), N.ElementarySubstructure M ∧
      A ⊆ N ∧ Cardinal.mk N ≤ max (Cardinal.mk A) L.card := by
  -- 参见 Mathlib4 ModelTheory.Substructures 相关构造
  sorry

end LowenheimSkolem
```

## 数学背景

Löwenheim-Skolem 定理是模型论中最早建立的深刻结果之一，由 Leopold Löwenheim（1915）首先证明向下情形，后经 Thoralf Skolem（1920）推广与完善。该定理揭示了一阶逻辑的惊人特性：如果一个一阶理论有无穷模型，那么它对任何大于等于语言基数的无穷基数都有模型。这意味着一阶逻辑无法精确刻画无穷结构的大小——无论你想描述多么“巨大”的集合，一阶理论总有一个可数模型来满足它。这一定理对集合论（Skolem 悖论）和代数（非标准模型）产生了深远影响。

## 直观解释

Löwenheim-Skolem 定理告诉我们：**一阶语言是“近视”的——它看不清无穷结构的真实大小**。想象你试图用一阶语言描述整个宇宙（不可数集合），定理断言：无论你描述得多详尽，总有人口普查官（模型论学家）能找到一个可数大小的“微型宇宙”，里面的一切一阶性质都与真实宇宙一模一样。反过来，如果你有一个小模型，也可以把它膨胀到任意大而不失任何一阶真理。

这正是为什么一阶集合论 ZFC 如果有模型，就同时有可数的和不可数的模型——Skolem 悖论的根源。

## 形式化表述

设 $L$ 为一阶语言，$T$ 为 $L$ 上的理论，$M$ 为 $T$ 的无穷模型。

**向下 Löwenheim-Skolem 定理**：设 $A \subseteq M$ 为无穷子集，$|A| \geq |L|$，则存在 $M$ 的初等子结构 $N \prec M$ 使得 $A \subseteq N$ 且 $|N| = |A|$。特别地，若 $|L| \leq \aleph_0$，则任何无穷模型都有可数初等子结构。

**向上 Löwenheim-Skolem 定理**：设 $\kappa \geq \max(|M|, |L|)$ 为基数，则存在模型 $N \vDash T$ 使得 $M$ 可初等嵌入到 $N$ 中，且 $|N| = \kappa$。

在 Mathlib4 中，这些结果通过 Skolem 函数、紧致性定理和初等子结构的构造实现，分散于 `ModelTheory.Skolem`、`ModelTheory.Satisfiability` 和 `ModelTheory.Substructures` 等模块。

## 证明思路

**向下 L-S 定理**：
1. **Skolem 函数**：对每个存在公式 $\exists x \phi(x, \bar{y})$，添加一个 Skolem 函数 $f_\phi(\bar{y})$，使得若 $M \vDash \exists x \phi(x, \bar{a})$，则 $M \vDash \phi(f_\phi(\bar{a}), \bar{a})$
2. **封闭集合**：取包含 $A$ 的最小 Skolem 封闭子集 $N \subseteq M$
3. **Tarski-Vaught 判别法**：证明 $N$ 满足 Tarski-Vaught 条件，从而 $N \prec M$
4. **基数控制**：由于 Skolem 函数的数量不超过 $\max(|L|, |A|)$，闭包的大小也不超过此基数

**向上 L-S 定理**：
1. **添加常元**：对目标基数 $\kappa$，向语言中添加 $\kappa$ 个新常元符号 $\{c_\alpha : \alpha < \kappa\}$
2. **分离公理**：构造理论 $T' = T \cup \{c_\alpha \neq c_\beta : \alpha \neq \beta\}$
3. **紧致性定理**：由紧致性定理，$T'$ 有模型（因为任何有限子集只涉及有限多个不同常元）
4. **Löwenheim-Skolem 向下**：若得到模型过大，再用向下定理得到恰好基数为 $\kappa$ 的模型

## 示例

### 示例 1：Skolem 悖论

ZFC 集合论证明存在不可数集合（如实数集 $\mathbb{R}$）。但如果 ZFC 有一阶模型 $M$，由向下 L-S 定理，存在可数模型 $N \vDash \text{ZFC}$。在 $N$ 中，“不可数集”只是从 $N$ 的内部看没有 $N$-可数的双射，但从外部看 $N$ 本身可数，因此该集合实际上是可数的。这被称为 Skolem 悖论，揭示了模型内部与外部视角的差异。

### 示例 2：非标准实数

考虑实数域的理论 $Th(\mathbb{R})$。由向上 L-S 定理，存在不可数的初等扩张 $^*\mathbb{R} \succ \mathbb{R}$，其中包含无穷小和无穷大元素（非标准分析的基础）。同样，也存在可数的非标准模型。

### 示例 3：Peano 算术的可数模型

PA 有不可数多个互不同构的可数模型（由 Ryll-Nardzewski 定理）。向下 L-S 定理保证了任何 PA 的不可数模型都有可数初等子结构，且这些子结构本身也是 PA 的模型。

## 应用

- **非标准分析**：利用非标准模型构造无穷小与无穷大
- **集合论**：强制法、内模型与大基数理论中的模型论工具
- **代数**：Artin 猜想、$p$-adic 域与代数闭域的模型论研究
- **计算复杂性**：有限模型论在数据库理论和描述复杂性中的应用
- **数理哲学**：Skolem 悖论与数学实在论的争论

## 相关概念

- 初等子结构 (Elementary Substructure)：保持所有一阶公式真值的子结构
- Skolem 函数 (Skolem Function)：消去存在量词的函数符号
- Tarski-Vaught 判别法 (Tarski-Vaught Test)：判定子结构是否为初等子结构的准则
- 紧致性定理 (Compactness Theorem)：L-S 向上定理证明中的关键工具
- 非标准模型 (Nonstandard Model)：与标准模型初等等价的模型

## 参考

### 教材

- [Hodges. A Shorter Model Theory. Cambridge, 1997. Chapter 3]
- [Marker. Model Theory: An Introduction. Springer, 2002. Chapter 2]

### 历史文献

- [Löwenheim. Über Möglichkeiten im Relativkalkül. Mathematische Annalen, 1915]
- [Skolem. Logisch-kombinatorische Untersuchungen über die Erfüllbarkeit oder Beweisbarkeit mathematischer Sätze. Skrifter utgit av Videnskapsselskapet i Kristiania, 1920]

### 在线资源

- [Mathlib4 文档 - Skolem][https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory/Skolem.html]
- [Mathlib4 文档 - Satisfiability][https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory/Satisfiability.html]

---

*最后更新：2026-04-15 | 版本：v1.0.0*
