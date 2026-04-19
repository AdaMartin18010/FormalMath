---
title: Sylow 第一定理
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
    - 'Chapter 7: More Group Theory, Section 7.7'
    url: null
    pages: 205-210
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
    - 'Chapter 5: Group Actions, Section 5.4 (Sylow Theorems)'
    url: null
    pages: 139-146
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
review_status: completed
---

## 1. 引言

Sylow 定理是有限群论的基石，提供了 $p$-子群存在性、共轭性与计数条件的完整描述。本节聚焦 Sylow 第一定理。

## 2. 定义

**定义 2.1（$p$-群）** 设 $p$ 为素数。有限群 $G$ 称为 **$p$-群**，如果 $|G| = p^n$（$n \ge 0$）。

**定义 2.2（Sylow $p$-子群）** 设 $|G| = p^n m$ 且 $p \nmid m$。$G$ 的阶为 $p^n$ 的子群称为 **Sylow $p$-子群**。

## 3. Cauchy 定理

在证明 Sylow 第一定理之前，我们需要以下关键工具。

### 定理 3.1（Cauchy 定理）

设 $G$ 为有限群，$p$ 为素数，若 $p \mid |G|$，则 $G$ 中存在阶为 $p$ 的元素（从而存在 $p$ 阶子群）。

**证明**：
对 $|G|$ 使用归纳法。

- **基例**：$|G| = p$ 时，$G$ 为循环群，显然存在 $p$ 阶元素。
- **归纳步骤**：假设结论对所有阶小于 $|G|$ 且被 $p$ 整除的群成立。
  考虑类方程
  $$|G| = |Z(G)| + \sum_{i} [G : C(g_i)],$$
  其中求和取遍非中心共轭类的代表元 $g_i$。
  - 若 $p \nmid |Z(G)|$，则必有某个 $i$ 使得 $p \nmid [G : C(g_i)]$（否则右边被 $p$ 整除而左边 $|Z(G)|$ 不被 $p$ 整除，矛盾）。于是 $p^n \mid |C(g_i)|$。因为 $C(g_i) < G$，由归纳假设 $C(g_i)$ 有 Sylow $p$-子群，从而 $G$ 也有。
  - 若 $p \mid |Z(G)|$，因为 $Z(G)$ 是交换群，由交换群的 Cauchy 定理（可用结构定理或归纳），$Z(G)$ 中存在 $p$ 阶元素，生成 $p$ 阶子群 $N \le Z(G)$。于是 $N \trianglelefteq G$。考虑商群 $G/N$，其阶为 $|G|/p < |G|$，且仍被 $p^{n-1}$ 整除。由归纳假设，$G/N$ 有 Sylow $p$-子群 $\bar{P}$，设 $\bar{P} = P/N$。则 $|P| = |N| \cdot |\bar{P}| = p \cdot p^{n-1} = p^n$，即 $P$ 是 $G$ 的 Sylow $p$-子群。 ∎

**Lean4 双语对照**：

```lean
-- Cauchy定理：若 p | |G|，则 G 有 p 阶元素
theorem cauchy_theorem {G : Type u} [Group G] [Fintype G] {p : ℕ}
    [Fact p.Prime] (hp : p ∣ Fintype.card G) :
    ∃ (g : G), orderOf g = p := by
  /- 使用Mathlib4的Cauchy定理 -/
  apply exists_prime_orderOf_dvd_card p hp

-- Cauchy定理的推论：存在p阶子群
theorem cauchy_subgroup {G : Type u} [Group G] [Fintype G] {p : ℕ}
    [Fact p.Prime] (hp : p ∣ Fintype.card G) :
    ∃ (H : Subgroup G), Fintype.card H = p := by
  rcases cauchy_theorem hp with ⟨g, hg⟩
  use zpowers g
  rw [zpowers_equiv_zmod g] at *
  rw [Fintype.card_zmod]
  rw [hg]
```

## 4. Sylow 第一定理

### 定理 4.1

设 $G$ 为有限群，$p$ 为素数，$|G| = p^n m$ 且 $p \nmid m$。则 $G$ 存在 Sylow $p$-子群，即存在子群 $P \le G$ 使得 $|P| = p^n$。

**证明**：
对 $|G|$ 进行归纳。

- 若 $n=0$，则 $p^0 = 1$，平凡子群 $\{1\}$ 即为 Sylow $p$-子群。
- 设 $n \ge 1$。使用类方程
  $$|G| = |Z(G)| + \sum_{i} [G : C(g_i)]。$$
  - **情形 1**：$p \nmid |Z(G)|$。则存在某个 $g_i$ 使得 $p \nmid [G : C(g_i)]$。于是 $p^n \mid |C(g_i)|$。因为 $g_i$ 非中心，$C(g_i) < G$（真子群）。由归纳假设 $C(g_i)$ 有 Sylow $p$-子群 $P$，且 $|P| = p^n$，故 $P$ 也是 $G$ 的 Sylow $p$-子群。
  - **情形 2**：$p \mid |Z(G)|$。由 Cauchy 定理，$Z(G)$ 有 $p$ 阶子群 $N$。因为 $N \le Z(G)$，故 $N \trianglelefteq G$。考虑商群 $G/N$，其阶为 $p^{n-1} m$。由归纳假设，$G/N$ 有 Sylow $p$-子群 $\bar{P} = P/N$，其中 $P \le G$ 且 $|P| = |N| \cdot |\bar{P}| = p \cdot p^{n-1} = p^n$。因此 $P$ 是 $G$ 的 Sylow $p$-子群。

综上，Sylow $p$-子群存在。 ∎

**Lean4 双语对照**：

```lean
theorem sylow_first_theorem {G : Type u} [Group G] [Fintype G] {p : ℕ} [Fact p.Prime]
    (n : ℕ) (m : ℕ) (hm : p.Coprime m) (hG : Fintype.card G = p ^ n * m) :
    ∃ (P : Sylow p G), Fintype.card P = p ^ n := by
  have h : ∃ (P : Sylow p G), True := by
    use default
  rcases h with ⟨P, -⟩
  use P
  have h_card_P : Fintype.card P = p ^ n := by
    have h_pgroup : IsPGroup p P := by
      exact Sylow.isPGroup' P
    rcases h_pgroup with ⟨k, hk⟩
    have h_dvd : Fintype.card P ∣ Fintype.card G := by
      exact card_subgroup_dvd_card (P.toSubgroup)
    rw [hG] at h_dvd
    rw [hk] at h_dvd
    have h_k_le_n : k ≤ n := by
      have h : p ^ k ∣ p ^ n * m := h_dvd
      have h_coprime : p ^ n.Coprime m := by
        exact Nat.Coprime.pow_left n hm
      have h_pk_pn : p ^ k ∣ p ^ n := by
        exact Nat.Coprime.dvd_of_dvd_mul_right h_coprime h
      exact Nat.pow_dvd_pow_iff_le_right (Nat.Prime.one_lt Fact.out).le h_pk_pn
    have h_k_eq_n : k = n := by
      have h_max : ∀ (k' : ℕ), p ^ k' ∣ Fintype.card G → k' ≤ n := by
        intro k' h_pk'
        rw [hG] at h_pk'
        have h_coprime : p ^ n.Coprime m := by
          exact Nat.Coprime.pow_left n hm
        have h_pk'_pn : p ^ k' ∣ p ^ n := by
          exact Nat.Coprime.dvd_of_dvd_mul_right h_coprime h_pk'
        exact Nat.pow_dvd_pow_iff_le_right (Nat.Prime.one_lt Fact.out).le h_pk'_pn
      have h_k_max : ∀ (k' : ℕ), k' > k → ¬(p ^ k' ∣ Fintype.card P) := by
        intro k' hk' h_pk'
        rw [hk] at h_pk'
        have : p ^ k' ∣ p ^ k := h_pk'
        have : k' ≤ k := by
          exact Nat.pow_dvd_pow_iff_le_right (Nat.Prime.one_lt Fact.out).le this
        linarith
      have h_n_le_k : n ≤ k := by
        by_contra h
        push_neg at h
        have : p ^ n ∣ Fintype.card P := by
          rw [hk]
          exact pow_dvd_pow p h
        exact h_k_max n h this
      linarith
    rw [h_k_eq_n] at hk
    exact hk
  exact h_card_P
```

## 5. 习题与详细解答

### 习题 1

设 $|G| = pq$，其中 $p < q$ 为素数且 $p \nmid (q-1)$。证明 $G$ 为循环群。

**解答**：
设 $n_p, n_q$ 分别为 Sylow $p$-子群与 Sylow $q$-子群的个数。由 Sylow 第三定理，$n_p \mid q$ 且 $n_p \equiv 1 \pmod p$。因为 $q$ 为素数，$n_p = 1$ 或 $q$。若 $n_p = q$，则 $q \equiv 1 \pmod p$，即 $p \mid (q-1)$，矛盾。故 $n_p = 1$，Sylow $p$-子群 $P$ 正规。同理 $n_q = 1$，Sylow $q$-子群 $Q$ 正规。因为 $|P| = p$, $|Q| = q$ 且 $P \cap Q = \{1\}$，有 $G \cong P \times Q \cong \mathbb{Z}/p\mathbb{Z} \times \mathbb{Z}/q\mathbb{Z} \cong \mathbb{Z}/pq\mathbb{Z}$。故 $G$ 为循环群。 ∎

### 习题 2

设 $|G| = 12 = 2^2 \cdot 3$。证明 $G$ 必有正规 Sylow $2$-子群或正规 Sylow $3$-子群。

**解答**：
设 $n_2, n_3$ 分别为 Sylow $2$-子群、Sylow $3$-子群的个数。则 $n_3 \mid 4$ 且 $n_3 \equiv 1 \pmod 3$，故 $n_3 = 1$ 或 $4$。若 $n_3 = 1$，则 Sylow $3$-子群正规。
若 $n_3 = 4$，则 $G$ 中有 $4 \times (3-1) = 8$ 个 $3$ 阶元素。剩余 $12-8=4$ 个元素必构成唯一的 Sylow $2$-子群，故 $n_2 = 1$，即 Sylow $2$-子群正规。 ∎

### 习题 3

计算 $S_4$ 中 Sylow $3$-子群的个数。

**解答**：
$|S_4| = 24 = 2^3 \cdot 3$。Sylow $3$-子群的阶为 $3$。设个数为 $n_3$。则 $n_3 \mid 8$ 且 $n_3 \equiv 1 \pmod 3$。于是 $n_3 = 1$ 或 $4$。因为 $S_4$ 中 $3$-循环有 $8$ 个，每个 Sylow $3$-子群（阶为 $3$ 的循环群）含 $2$ 个 $3$-循环，故 $n_3 = 8/2 = 4$。 ∎

## 6. 常见误区分析

1. **混淆 $p$-子群与 Sylow $p$-子群**：$p$-子群的阶为 $p^k$（$k \le n$），而 Sylow $p$-子群的阶必须是 $p^n$（极大）。
2. **忽略 $p \nmid m$ 的条件**：在分解 $|G| = p^n m$ 时，必须保证 $p$ 与 $m$ 互素，否则 $n$ 的定义不唯一。
3. **误认为 Sylow 子群唯一**：Sylow 第一定理只保证存在性。唯一性仅在特殊条件下成立（如 $|G| = pq$ 且 $p \nmid (q-1)$）。
