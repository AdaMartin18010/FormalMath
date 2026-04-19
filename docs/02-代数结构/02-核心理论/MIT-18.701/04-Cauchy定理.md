---
title: Cauchy 定理（群论）
msc_primary: 08A99
level: silver
target_courses:
- MIT 18.701
date: '2026-04-17'
references:
  textbooks:
  - id: artin_algebra
    type: textbook
    title: Algebra
    authors:
    - Michael Artin
    publisher: Pearson
    edition: 2nd
    year: 2011
    isbn: 978-0132413770
    msc: 16-01
    chapters:
    - 'Chapter 7: More Group Theory, Section 7.2'
    url: null
    pages: 185-190
  - id: strang_la
    type: textbook
    title: Introduction to Linear Algebra
    authors:
    - Gilbert Strang
    publisher: Wellesley-Cambridge Press
    edition: 5th
    year: 2016
    isbn: 978-0980232776
    msc: 15-01
    chapters: 
    url: null
  - id: dummit_foote_aa
    type: textbook
    title: Abstract Algebra
    authors:
    - David S. Dummit
    - Richard M. Foote
    publisher: Wiley
    edition: 3rd
    year: 2003
    isbn: 978-0471433347
    msc: 13-01
    chapters:
    - 'Chapter 4: Group Actions, Section 4.1 (Cauchy''s Theorem)'
    url: null
    pages: 93-96
  databases:
  - id: nlab
    type: database
    name: nLab
    entry_url: https://ncatlab.org/nlab/show/{entry}
    consulted_at: 2026-04-17
  - id: stacks_project
    type: database
    name: Stacks Project
    entry_url: https://stacks.math.columbia.edu/tag/{tag}
    consulted_at: 2026-04-17
  - id: zbmath
    type: database
    name: zbMATH Open
    entry_url: https://zbmath.org/?q=an:{zb_id}
    consulted_at: 2026-04-17
---

## 1. 引言

Cauchy 定理是有限群论中关于 $p$-阶元素存在性的基本结果，它是证明 Sylow 第一定理的关键工具。

## 2. 定理陈述

### 定理 2.1（Cauchy 定理）

设 $G$ 为有限群，$p$ 为素数。若 $p \mid |G|$，则 $G$ 中存在阶为 $p$ 的元素。从而 $G$ 存在阶为 $p$ 的循环子群。

## 3. 完整证明

**证明**：
对 $|G|$ 使用数学归纳法。

- **基例**：$|G| = 1$ 时，不存在素数 $p \mid 1$，定理 vacuously 成立。$|G| = p$ 时，$G$ 为 $p$ 阶循环群，显然存在 $p$ 阶元素。

- **归纳假设**：设对所有阶小于 $|G|$ 且被 $p$ 整除的有限群，结论成立。

- **归纳步骤**：考虑类方程（class equation）
  $$|G| = |Z(G)| + \sum_{i=1}^k [G : C(g_i)],$$
  其中 $Z(G)$ 是 $G$ 的中心，$g_1, \dots, g_k$ 取遍 $G \setminus Z(G)$ 中所有非平凡共轭类的代表元，$C(g_i)$ 为 $g_i$ 的中心化子。

  分两种情形讨论：

  **情形 1**：$p \nmid |Z(G)|$。
  因为 $p \mid |G|$，而 $|G| = |Z(G)| + \sum [G : C(g_i)]$，且每个 $[G : C(g_i)] > 1$（因为 $g_i \notin Z(G)$）。若所有 $[G : C(g_i)]$ 都被 $p$ 整除，则右边 $\equiv |Z(G)| \not\equiv 0 \pmod p$，与左边被 $p$ 整除矛盾。因此存在某个 $i$ 使得 $p \nmid [G : C(g_i)]$。于是
  $$p \mid |C(g_i)| = \frac{|G|}{[G : C(g_i)]}。$$
  又因为 $g_i \notin Z(G)$，所以 $C(g_i) < G$（真子群）。由归纳假设，$C(g_i)$ 中存在阶为 $p$ 的元素，该元素也属于 $G$。

  **情形 2**：$p \mid |Z(G)|$。
  此时 $Z(G)$ 是交换群且 $p \mid |Z(G)|$。对交换群的 Cauchy 定理可以用如下方式证明：取 $a \in Z(G)$ 且 $a \neq 1$。若 $p \mid \operatorname{order}(a)$，设 $\operatorname{order}(a) = p \cdot m$，则 $a^m$ 的阶为 $p$，证毕。若 $p \nmid \operatorname{order}(a)$，考虑商群 $Z(G)/\langle a \rangle$，其阶为 $|Z(G)|/\operatorname{order}(a) < |Z(G)|$ 且仍被 $p$ 整除。由归纳假设，该商群有 $p$ 阶元素，提升回 $Z(G)$ 即得 $Z(G)$ 中有 $p$ 阶元素。

  设 $N = \langle x \rangle \le Z(G)$ 为 $p$ 阶子群。因为 $N \le Z(G)$，所以 $N \trianglelefteq G$。考虑商群 $G/N$，其阶为 $|G|/p < |G|$，且仍被 $p$ 整除（若 $n \ge 2$；若 $n=1$ 则 $G/N$ 阶为 $m$ 不被 $p$ 整除，此时 $N$ 本身就是 Sylow $p$-子群，已满足要求）。由归纳假设，$G/N$ 中存在 $p$ 阶元素，对应回 $G$ 中即得 $p$ 阶元素。

综上，Cauchy 定理得证。 ∎

**Lean4 双语对照**：

```lean
import Mathlib.GroupTheory.Sylow
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.ZMod.Basic

universe u

namespace CauchyTheorem

open Subgroup Group

variable {G : Type u} [Group G] [Fintype G]

-- Cauchy定理：若 p | |G|，则 G 有 p 阶元素
theorem cauchy_theorem {p : ℕ} [Fact p.Prime] (hp : p ∣ Fintype.card G) :
    ∃ (g : G), orderOf g = p := by
  /- 使用 Mathlib4 的素数阶元素存在性定理 -/
  apply exists_prime_orderOf_dvd_card p hp

-- 推论：存在 p 阶子群
theorem cauchy_subgroup {p : ℕ} [Fact p.Prime] (hp : p ∣ Fintype.card G) :
    ∃ (H : Subgroup G), Fintype.card H = p := by
  rcases cauchy_theorem hp with ⟨g, hg⟩
  use zpowers g
  rw [zpowers_equiv_zmod g] at *
  rw [Fintype.card_zmod]
  rw [hg]

end CauchyTheorem
```

**代码解读**：

- `exists_prime_orderOf_dvd_card` 是 Mathlib 中 Cauchy 定理的核心实现。
- `zpowers g` 构造由 $g$ 生成的循环子群。
- `zpowers_equiv_zmod g` 将该循环子群同构于 $\mathbb{Z}/p\mathbb{Z}$，从而其基数为 $p$。

## 4. 习题与详细解答

### 习题 1

设 $G$ 为 $p^n$ 阶群（$p$ 为素数）。证明 $Z(G) \neq \{1\}$。

**解答**：
考虑类方程 $|G| = |Z(G)| + \sum [G : C(g_i)]$。每个非平凡共轭类的指数 $[G : C(g_i)]$ 都大于 $1$ 且整除 $|G| = p^n$，故被 $p$ 整除。于是
$$|Z(G)| = |G| - \sum [G : C(g_i)] \equiv 0 \pmod p。$$
因此 $p \mid |Z(G)|$，而 $|Z(G)| \ge 1$（至少含单位元），故 $|Z(G)| \ge p > 1$，即 $Z(G) \neq \{1\}$。 ∎

### 习题 2

设 $G$ 为 $p^2$ 阶群（$p$ 为素数）。证明 $G$ 为交换群。

**解答**：
由习题 1，$|Z(G)| = p$ 或 $p^2$。若 $|Z(G)| = p^2$，则 $G = Z(G)$ 为交换群。若 $|Z(G)| = p$，则 $|G/Z(G)| = p$，故 $G/Z(G)$ 为循环群。但众所周知，若 $G/Z(G)$ 为循环群，则 $G$ 必为交换群，矛盾。因此 $|Z(G)| = p^2$，$G$ 交换。 ∎

### 习题 3

设 $G$ 为有限群，$p$ 为 $|G|$ 的最小素因子，$H \le G$ 且 $[G:H] = p$。证明 $H \trianglelefteq G$。

**解答**：
考虑 $G$ 在左陪集空间 $G/H$ 上的左乘作用。这给出同态 $\varphi: G \to S_p$。则 $G/\ker\varphi \cong \operatorname{im}\varphi \le S_p$。于是 $|G/\ker\varphi|$ 整除 $p!$。因为 $p$ 是 $|G|$ 的最小素因子，$|G/\ker\varphi|$ 中所有素因子均 $\ge p$。但 $|G/\ker\varphi| \mid p!$ 意味着其素因子只能 $\le p$。因此 $|G/\ker\varphi|$ 只能是 $p$ 的幂次。又 $[G:H] = p$ 且 $\ker\varphi \le H$，可得 $[G:\ker\varphi] = p$，从而 $\ker\varphi = H$。因为核总是正规子群，故 $H \trianglelefteq G$。 ∎

## 5. 常见误区分析

1. **忽略归纳假设的适用范围**：在使用归纳法时，必须确保子群或商群的阶严格小于 $|G|$，否则归纳假设无法应用。
2. **混淆群的交换性**：证明中对 $Z(G)$ 使用了交换群的 Cauchy 定理。若直接在一般群上套用交换群的论证，会出错。
3. **误认为 Cauchy 定理推出 Sylow 定理**：Cauchy 定理仅保证 $p^1$ 阶子群的存在性，而 Sylow 第一定理要求 $p^n$ 阶子群。二者不可互相替代。
