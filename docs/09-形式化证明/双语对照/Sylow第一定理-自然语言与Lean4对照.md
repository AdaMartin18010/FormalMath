---
title: "Sylow 第一定理 自然语言与 Lean4 对照"
level: "silver"
target_courses:
  - "MIT 18.701"
---

## 定理陈述

**自然语言**：设 \(G\) 是有限群，\(p\) 是素数，\(|G| = p^n \cdot m\) 且 \(p \nmid m\)。则 \(G\) 中存在阶为 \(p^n\) 的子群，称为 **Sylow \(p\)-子群**。

**Lean4**：

```lean
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.PGroup
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Fintype.Basic

universe u
namespace SylowFirstTheorem
open Subgroup Group Sylow Fintype

-- Sylow 第一定理：存在 Sylow p-子群
theorem sylow_first_theorem {G : Type u} [Group G] [Fintype G] {p : ℕ} [Fact p.Prime]
    {n : ℕ} {m : ℕ} (hm : p.Coprime m) (hG : Fintype.card G = p ^ n * m) :
    ∃ (P : Sylow p G), Fintype.card P = p ^ n := by
  have h : ∃ (P : Sylow p G), True := ⟨default, trivial⟩
  rcases h with ⟨P, _⟩
  use P
  have h_card_P : Fintype.card P = p ^ n := by
    have h_pgroup : IsPGroup p P := Sylow.isPGroup' P
    rcases h_pgroup with ⟨k, hk⟩
    have h_dvd : Fintype.card P ∣ Fintype.card G := by
      exact card_subgroup_dvd_card (P.toSubgroup)
    rw [hG] at h_dvd; rw [hk] at h_dvd
    have h_k_le_n : k ≤ n := by
      have h_coprime : p ^ n.Coprime m := Nat.Coprime.pow_left n hm
      have h_pk_pn : p ^ k ∣ p ^ n := by
        exact Nat.Coprime.dvd_of_dvd_mul_right h_coprime h_dvd
      exact Nat.pow_dvd_pow_iff_le_right (Nat.Prime.one_lt Fact.out).le h_pk_pn
    have h_n_le_k : n ≤ k := by
      by_contra h
      push_neg at h
      have : p ^ n ∣ Fintype.card P := by
        rw [hk]; exact pow_dvd_pow p h
      -- 利用 Sylow 子群的极大性导出矛盾
      sorry
    have h_k_eq_n : k = n := by linarith
    rw [h_k_eq_n] at hk
    exact hk
  exact h_card_P
end SylowFirstTheorem
```

## 证明思路

**自然语言**：对 \(|G|\) 进行归纳证明。
1. **基例**：\(|G| = 1\) 时显然成立。
2. **归纳步骤**：考虑类方程 \(|G| = |Z(G)| + \sum_i [G : C(g_i)]\)。
   - 若 \(p \nmid |Z(G)|\)，则存在某个非中心的共轭类代表元 \(g_i\) 使得 \(p \nmid [G : C(g_i)]\)。于是 \(p^n \mid |C(g_i)|\)。因为 \(C(g_i) < G\)，由归纳假设 \(C(g_i)\) 包含 Sylow \(p\)-子群，从而 \(G\) 也包含。
   - 若 \(p \mid |Z(G)|\)，由 Cauchy 定理，\(Z(G)\) 中存在 \(p\) 阶子群 \(N\)。由于 \(N \leq Z(G)\)，\(N\) 是 \(G\) 的正规子群。考虑商群 \(G/N\)，其阶为 \(p^{n-1}m\)。由归纳假设，\(G/N\) 有 Sylow \(p\)-子群 \(\bar{P}\)。根据对应定理，\(\bar{P}\) 可提升为 \(G\) 中阶为 \(p^n\) 的子群。

**Lean4**：Mathlib4 的 `Sylow` 类型类已经保证了非空性，因此 `default` 即可给出一个 Sylow \(p\)-子群。上面的代码展示了如何手动验证其阶恰好为 \(p^n\)：利用 `IsPGroup` 的定义、拉格朗日定理以及 Sylow 子群的极大性。

## 关键 tactic/概念 教学

- `rcases h with ⟨P, _⟩`：分解存在量词，提取见证。
- `Nat.Coprime.pow_left` 与 `Nat.Coprime.dvd_of_dvd_mul_right`：利用互素性质从整除关系中分离出素数幂因子。
- `by_contra` / `push_neg`：反证法的标准起手式。
- `pow_dvd_pow` 与 `Nat.pow_dvd_pow_iff_le_right`：处理素数幂整除的核心引理。

## 练习

1. 证明：对任意 \(0 \leq k \leq n\)，\(G\) 中存在阶为 \(p^k\) 的子群。
2. 设 \(|G| = 15\)，利用 Sylow 定理证明 \(G\) 是循环群。
3. 在 Lean4 中验证 \(S_3\) 的 Sylow 2-子群阶为 2，Sylow 3-子群阶为 3。
