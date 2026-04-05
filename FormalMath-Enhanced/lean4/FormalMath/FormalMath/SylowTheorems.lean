/-
# Sylow三大定理

## 数学背景

Sylow定理是有限群论中最基本的结果之一。
对于有限群G和素数p整除|G|，Sylow p-子群是G的极大p-子群。

## 三大定理
1. **第一定理**：Sylow p-子群存在
2. **第二定理**：所有Sylow p-子群共轭
3. **第三定理**：Sylow p-子群的数量满足特定同余条件

## Mathlib4对应
- `Mathlib.GroupTheory.Sylow`
- `Mathlib.GroupTheory.PGroup`

本文件基于Mathlib4中已证明的Sylow定理，建立符合教学需求的定理表述。
-/

import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.Coset
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Nat.Factors

namespace SylowTheorems

open Subgroup Group MulAction

variable {G : Type*} [Group G] [Finite G] 
variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ)

/-
## Sylow p-子群的定义

Sylow p-子群是群G的子群P，满足：
1. P是p-群（|P|是p的幂）
2. P是极大的：若P ≤ Q且Q是p-子群，则P = Q

等价地，若|G| = pⁿ·m且p∤m，则|P| = pⁿ
-/
def IsSylowPSubgroup (P : Subgroup G) : Prop :=
  IsPGroup p P ∧ ∀ (Q : Subgroup G), IsPGroup p Q → P ≤ Q → P = Q

/-
## Sylow第一定理（存在性）

**定理陈述**：若pⁿ整除|G|，则G存在阶为pⁿ的子群。

**数学意义**：这是Sylow定理的基础，保证了p-子群的存在性。

**证明思路**：
1. 首先证明Sylow p-子群存在（Mathlib中已证明：Sylow.nonempty）
2. Sylow p-子群的阶是p在|G|中的最高幂
3. 利用Mathlib中的PGroup结构定理

**参考**: Dummit & Foote, Theorem 4.1.1, p. 139
-/
theorem sylow_first_theorem 
    (hdiv : p ^ n ∣ Nat.card G) :
    ∃ P : Subgroup G, Nat.card P = p ^ n := by
  -- Sylow p-子群存在
  have h_nonempty : Nonempty (Sylow p G) := Sylow.nonempty p G
  
  -- 由条件p^n | |G|，我们知道n ≤ v_p(|G|)
  have h_le : n ≤ Nat.factorization (Nat.card G) p := by
    rw [← Nat.pow_dvd_iff_le_factorization]
    · exact hdiv
    · exact Nat.card_pos.ne'
    · exact hp.1
  
  -- Sylow p-子群S的阶为p^{v_p(|G|)}
  rcases h_nonempty with ⟨S⟩
  have h_card_S : Nat.card S = p ^ (Nat.factorization (Nat.card G) p) := by
    rw [Sylow.card_eq_prime_pow]
    exact hp.1
  
  -- 利用p-群的子群存在定理
  -- 对于p-群，对每个k ≤ v_p(|G|)，存在阶为p^k的子群
  have h_pgroup : IsPGroup p S := by
    exact IsPGroup.of_card (by rw [h_card_S]; exact Nat.pow_dvd_pow p (by simp))
  
  -- 利用p-群的子群存在性
  obtain ⟨P, hP_le, hP_card⟩ := IsPGroup.exists_subgroup_card_pow h_pgroup h_le
  
  use P
  exact hP_card

/-
## Sylow p-子群的阶

**定理**：若P是Sylow p-子群，则|P| = p^{v_p(|G|)}

其中v_p(|G|)表示p在|G|的质因数分解中的指数。

**参考**: Dummit & Foote, Proposition 4.1.2, p. 139
-/
theorem sylow_card 
    (P : Subgroup G) (hP : IsSylowPSubgroup p P) :
    Nat.card P = p ^ (Nat.factorization (Nat.card G) p) := by
  rcases hP with ⟨h_pgroup, hmax⟩
  
  -- Sylow p-子群作为极大p-子群，其阶必然是p的最高幂
  have h_card : Nat.card P = p ^ (Nat.factorization (Nat.card G) p) := by
    -- 由极大性导出阶的等式
    rw [isPGroup_iff] at h_pgroup
    rcases h_pgroup with ⟨k, hk⟩
    
    -- 证明k = v_p(|G|)
    have h_k_eq : k = Nat.factorization (Nat.card G) p := by
      -- k ≤ v_p(|G|)（由Lagrange定理）
      have h_le : k ≤ Nat.factorization (Nat.card G) p := by
        have h_dvd : p ^ k ∣ Nat.card G := by
          rw [← hk]
          exact Subgroup.card_subgroup_dvd_card P
        rw [← Nat.pow_dvd_iff_le_factorization]
        · exact h_dvd
        · exact Nat.card_pos.ne'
        · exact hp.1
      
      -- k ≥ v_p(|G|)（由极大性）
      have h_ge : k ≥ Nat.factorization (Nat.card G) p := by
        by_contra h_lt
        push_neg at h_lt
        -- 若k < v_p(|G|)，则可构造更大的p-子群，与极大性矛盾
        -- 设|S| = p^{v_p(|G|)}，则|S| > |P|
        have h_exists : ∃ (S : Sylow p G), True := by
          exact ⟨Sylow.nonempty p G |>.some, trivial⟩
        rcases h_exists with ⟨S, _⟩
        have hS_card := Sylow.card_eq_prime_pow p G S hp.1
        -- S包含一个阶为p^k的子群，这与P的极大性矛盾
        have : p ^ (Nat.factorization (Nat.card G) p) > p ^ k := by
          apply Nat.pow_lt_pow_right
          · exact hp.1.pos
          · exact h_lt
        -- 由极大性条件，P的阶应该是最大的p-幂
        linarith [hmax S (IsPGroup.of_card (by rw [hS_card]; exact Nat.pow_dvd_pow p (by simp))) (by
          have : Nat.card P ≤ Nat.card S := by
            rw [hk, hS_card]
            apply Nat.pow_le_pow_right
            · exact hp.1.pos
            · exact h_le
          -- 由于阶不同，P严格小于S
          sorry -- 需要更精细的论证
        )]
      
      linarith
    
    rw [hk, h_k_eq]
  
  exact h_card

/-
## Sylow第二定理（共轭性）

**定理陈述**：G的任意两个Sylow p-子群都是共轭的。

即：若P和Q都是Sylow p-子群，则存在g∈G使得Q = gPg⁻¹

**数学意义**：这说明Sylow p-子群在共轭作用下形成单一轨道，具有"本质唯一性"。

**证明思路**：
1. 考虑一个Sylow p-子群P在G/Q（Q的陪集空间）上的左乘作用
2. 由轨道-稳定化子定理，轨道大小整除|P| = p^k
3. 由类方程，|G/Q| = Σ|轨道|
4. 由于p∤|G/Q|，必有一个轨道大小为1（不动点）
5. 这个不动点给出gQ使得PgQ = gQ，即g⁻¹Pg ⊆ Q
6. 由阶的比较得g⁻¹Pg = Q

**参考**: Dummit & Foote, Theorem 4.1.2, p. 140
-/
theorem sylow_second_theorem 
    (P Q : Subgroup G) (hP : IsSylowPSubgroup p P) (hQ : IsSylowPSubgroup p Q) :
    ∃ g : G, Q = conjugate g P := by
  -- 将IsSylowPSubgroup转换为Sylow类型
  have hP_sylow : ∃ (S : Sylow p G), S.toSubgroup = P := by
    -- 构造Sylow类型：P是p-群且阶为p^{v_p(|G|)}
    have h_pgroup : IsPGroup p P := hP.1
    have h_card : Nat.card P = p ^ (Nat.factorization (Nat.card G) p) := by
      -- 利用极大性和p-群性质
      rcases hP with ⟨h_pg, h_max⟩
      rw [isPGroup_iff] at h_pg
      rcases h_pg with ⟨k, hk⟩
      -- 证明k = v_p(|G|)
      have h_k_max : k = Nat.factorization (Nat.card G) p := by
        have h_le : k ≤ Nat.factorization (Nat.card G) p := by
          have h_dvd : p ^ k ∣ Nat.card G := by
            rw [← hk]
            exact Subgroup.card_subgroup_dvd_card P
          rw [← Nat.pow_dvd_iff_le_factorization]
          · exact h_dvd
          · exact Nat.card_pos.ne'
          · exact hp.1
        -- 极大性意味着k必须是最大的
        have h_max_pow : ∀ (m : ℕ), m > k → ¬(p ^ m ∣ Nat.card P) := by
          intro m hm hdiv
          have : p ^ m ∣ p ^ k := by
            rw [← hk]
            exact hdiv
          have : m ≤ k := by
            exact (Nat.pow_dvd_pow_iff_le_right hp.1.pos).mp this
          linarith
        -- 结合得到k = v_p(|G|)
        have h_ge : k ≥ Nat.factorization (Nat.card G) p := by
          by_contra h
          push_neg at h
          have h_card_G : p ^ (Nat.factorization (Nat.card G) p) ∣ Nat.card G := by
            apply Nat.ordProj_dvd
          have : p ^ (k + 1) ∣ p ^ (Nat.factorization (Nat.card G) p) := by
            apply Nat.pow_dvd_pow p
            omega
          -- 构造矛盾
          sorry
        linarith
      rw [hk, h_k_max]
    -- 使用Sylow类型构造
    let S : Sylow p G := {
      toSubgroup := P
      isPGroup' := h_pgroup
      isMaximal' := by
        intro Q hQ hle
        rw [h_max Q hQ hle]
    }
    exact ⟨S, rfl⟩
  
  have hQ_sylow : ∃ (T : Sylow p G), T.toSubgroup = Q := by
    -- 类似构造
    sorry
  
  rcases hP_sylow with ⟨S, hS⟩
  rcases hQ_sylow with ⟨T, hT⟩
  
  -- 使用Mathlib的共轭性定理
  have h_conjugate : ∃ g : G, T = conjugate g S := by
    have := Sylow.isConj p G S T
    rcases this with ⟨g, hg⟩
    use g
    rw [hg]
    rfl
  
  rcases h_conjugate with ⟨g, hg⟩
  use g
  rw [← hT, hg, hS]
  rfl

/-
## Sylow第三定理（数量定理）- 模条件

**定理陈述**：设n_p是Sylow p-子群的数量，则n_p ≡ 1 (mod p)

**证明思路**：
1. 考虑G通过共轭作用在所有Sylow p-子群组成的集合X上
2. 取定一个Sylow p-子群P，考虑P在X上的作用（作为G的子作用）
3. P的不动点恰好是P自身（由第二定理）
4. 由类方程，|X| ≡ |不动点| ≡ 1 (mod p)

**参考**: Dummit & Foote, Theorem 4.1.3, part (iii), p. 143
-/
theorem sylow_third_theorem_mod 
    (n_p : ℕ) (hn_p : n_p = Fintype.card (Sylow p G)) :
    n_p ≡ 1 [MOD p] := by
  -- 直接使用Mathlib中已证明的定理
  rw [hn_p]
  exact Sylow.card_eq_one_mod_p p G

/-
## Sylow第三定理（数量定理）- 整除条件

**定理陈述**：设n_p是Sylow p-子群的数量，则n_p | [G : P] = |G|/|P|

**证明思路**：
1. 由轨道-稳定化子定理，n_p = |G| / |N_G(P)|
2. 由于P ≤ N_G(P)，有|N_G(P)| = |P|·|N_G(P)/P|
3. 因此n_p = |G| / (|P|·|N_G(P)/P|) = (|G|/|P|) / |N_G(P)/P|
4. 故n_p | |G|/|P|

**参考**: Dummit & Foote, Theorem 4.1.3, part (iii), p. 143
-/
theorem sylow_third_theorem_div 
    (n_p : ℕ) (hn_p : n_p = Fintype.card (Sylow p G)) (P : Sylow p G) :
    n_p ∣ Nat.card G / Nat.card P := by
  -- 直接使用Mathlib中已证明的定理
  rw [hn_p]
  exact Sylow.card_dvd_index P

/-
## Sylow定理的应用：p-群的可解性

**定理**：阶为pⁿ的群是可解群。

**证明思路**：
1. p-群的中心Z(G)非平凡
2. G/Z(G)是阶更小的p-群
3. 对|G|进行归纳，G/Z(G)可解
4. Z(G)是阿贝尔群（故可解）
5. 可解群的扩张仍可解

**参考**: Dummit & Foote, Theorem 6.1.4, p. 199
-/
theorem p_group_solvable 
    (h : IsPGroup p G) : IsSolvable G := by
  -- 直接使用Mathlib中的定理
  exact IsPGroup.isSolvable h

/-
## Sylow定理的应用：pq阶群

**定理**：若|G| = pq，其中p < q都是素数且p∤(q-1)，
则G是循环群。

**证明思路**：
1. n_q ≡ 1 (mod q) 且 n_q | p，故n_q = 1
2. 唯一的Sylow q-子群Q正规
3. n_p ≡ 1 (mod p) 且 n_p | q
4. 若n_p = q，则p | (q-1)，矛盾
5. 故n_p = 1，Sylow p-子群P也正规
6. G ≅ P × Q ≅ Z_p × Z_q ≅ Z_{pq}（由中国剩余定理）

**参考**: Dummit & Foote, Proposition 5.5.1, p. 143
-/
theorem pq_group_cyclic 
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) 
    (hlt : p < q) (hnot_div : ¬(p ∣ q - 1))
    (hG : Nat.card G = p * q) :
    IsCyclic G := by
  -- 分析Sylow q-子群
  have h_card_q : Fintype.card (Sylow q G) = 1 := by
    -- n_q | p且n_q ≡ 1 (mod q)
    -- 由于p < q，唯一可能是n_q = 1
    have h_nq_dvd : Fintype.card (Sylow q G) ∣ p := by
      rw [← hG]
      apply Sylow.card_dvd_index
    have h_nq_mod : Fintype.card (Sylow q G) ≡ 1 [MOD q] := by
      apply Sylow.card_eq_one_mod_p
    -- p < q且n_q | p，所以n_q = 1或p
    -- 若n_q = p，则p ≡ 1 (mod q)，即q | (p-1)，与p < q矛盾
    have h_nq_eq_1_or_p : Fintype.card (Sylow q G) = 1 ∨ Fintype.card (Sylow q G) = p := by
      have h_dvd : Fintype.card (Sylow q G) ∣ p := h_nq_dvd
      have h_pos : Fintype.card (Sylow q G) > 0 := Fintype.card_pos
      have : Fintype.card (Sylow q G) ≤ p := Nat.le_of_dvd (by linarith [hp.pos]) h_dvd
      interval_cases h : Fintype.card (Sylow q G) <;> try { simp }
      · -- n_q = 1
        left; rfl
      · -- 其他情况需要检查
        sorry
    rcases h_nq_eq_1_or_p with (h1 | hp_eq)
    · exact h1
    · -- 若n_q = p，则p ≡ 1 (mod q)
      have h_contra : p ≡ 1 [MOD q] := by
        rw [← hp_eq]
        exact h_nq_mod
      -- p ≡ 1 (mod q)意味着q | (p-1)
      have h_q_dvd : q ∣ p - 1 := by
        rw [Nat.ModEq] at h_contra
        rw [← Nat.dvd_iff_mod_eq_zero, Nat.sub_mod_eq_zero_of_mod_eq]
        exact h_contra
      -- 但p < q，所以p - 1 < q，因此q ∤ (p-1)除非p = 1
      have h_lt : p - 1 < q := by
        omega
      have h_contra' : q ∣ p - 1 → p - 1 = 0 := by
        intro h
        have : p - 1 < q := h_lt
        have : q ≤ p - 1 := by
          exact Nat.le_of_dvd (by omega) h
        omega
      have h_p_eq_1 : p = 1 := by
        specialize h_contra' h_q_dvd
        omega
      -- p = 1不是素数，矛盾
      have h_not_prime : ¬p.Prime := by
        rw [h_p_eq_1]
        norm_num
      contradiction
  
  -- 分析Sylow p-子群
  have h_card_p : Fintype.card (Sylow p G) = 1 := by
    -- n_p | q且n_p ≡ 1 (mod p)
    have h_np_dvd : Fintype.card (Sylow p G) ∣ q := by
      rw [← hG]
      apply Sylow.card_dvd_index
    have h_np_mod : Fintype.card (Sylow p G) ≡ 1 [MOD p] := by
      apply Sylow.card_eq_one_mod_p
    -- n_p = 1或q
    have h_np_eq_1_or_q : Fintype.card (Sylow p G) = 1 ∨ Fintype.card (Sylow p G) = q := by
      have h_dvd : Fintype.card (Sylow p G) ∣ q := h_np_dvd
      have h_pos : Fintype.card (Sylow p G) > 0 := Fintype.card_pos
      have : Fintype.card (Sylow p G) ≤ q := Nat.le_of_dvd (by linarith [hq.pos]) h_dvd
      interval_cases h : Fintype.card (Sylow p G) <;> try { simp }
      sorry
    rcases h_np_eq_1_or_q with (h1 | hq_eq)
    · exact h1
    · -- 若n_p = q，则q ≡ 1 (mod p)，即p | (q-1)
      have h_contra : q ≡ 1 [MOD p] := by
        rw [← hq_eq]
        exact h_np_mod
      have h_p_dvd : p ∣ q - 1 := by
        rw [Nat.ModEq] at h_contra
        rw [← Nat.dvd_iff_mod_eq_zero, Nat.sub_mod_eq_zero_of_mod_eq]
        exact h_contra
      -- 这与条件矛盾
      contradiction
  
  -- 两个Sylow子群都正规，G是直积
  -- 进一步证明循环性
  sorry -- 需要构造同构

/-
## Frattini论断

**定理**：若H是G的正规子群，P是H的Sylow p-子群，
则G = H·N_G(P)

**证明思路**：
1. 对任意g∈G，gPg⁻¹ ⊆ gHg⁻¹ = H（因H正规）
2. gPg⁻¹是H的Sylow p-子群
3. 由Sylow第二定理（在H中），存在h∈H使gPg⁻¹ = hPh⁻¹
4. 故h⁻¹g ∈ N_G(P)，即g ∈ hN_G(P) ⊆ H·N_G(P)

**参考**: Dummit & Foote, Theorem 6.1.4, p. 199
-/
theorem frattini_argument 
    (H : Subgroup G) (hH : H.Normal) 
    (P : Subgroup H) (hP : IsPGroup p P) :
    G = (H : Set G) * (normalizer (P.map H.subtype) : Set G) := by
  -- Frattini论断的核心是证明G = H · N_G(P)
  -- 对于任意g ∈ G，需要证明g ∈ H · N_G(P)
  have h_subset : (G : Set G) ⊆ (H : Set G) * (normalizer (P.map H.subtype) : Set G) := by
    intro g hg
    -- gPg⁻¹ ⊆ H（因为H正规）
    have h_conj : (P.map (MulAut.conj g).toMonoidHom).map H.subtype ≤ H := by
      sorry
    -- gPg⁻¹也是H的Sylow p-子群
    have h_sylow : IsPGroup p ((P.map (MulAut.conj g).toMonoidHom).map H.subtype) := by
      sorry
    -- 存在h ∈ H使得gPg⁻¹ = hPh⁻¹
    sorry
  
  -- 反向包含是显然的
  have h_superset : (H : Set G) * (normalizer (P.map H.subtype) : Set G) ⊆ (G : Set G) := by
    intro x hx
    rcases hx with ⟨h, n, hh, hn, rfl⟩
    exact Subgroup.mul_mem G (H.subtype hh) (by sorry)
  
  -- 因此G = H · N_G(P)
  sorry

end SylowTheorems
