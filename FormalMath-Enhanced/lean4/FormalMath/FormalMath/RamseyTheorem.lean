/-
# Ramsey定理

Ramsey定理是组合数学中的经典定理，表明在足够大的结构中必然出现秩序。

## 定理陈述

对于任意给定的颜色数r和大小k₁,...,kᵣ，存在N使得K_N的边用r种颜色着色时，
必存在i使得有kᵢ个顶点的单色团。

## 参考
- Diestel《图论》第九章
- Mathlib4: Mathlib.Combinatorics.SimpleGraph.Ramsey

作者: FormalMath项目
日期: 2026年4月
版本: 4.20.0
-/ 

import Mathlib

namespace RamseyTheory

open Finset

/-! ## 基础定义 -/

/-- 完全图K_n的边着色：将顶点对的集合映射到颜色 -/
def EdgeColoring (n : ℕ) (r : ℕ) := Finset (Fin n) → Fin r

/-- 顶点集s在着色c下是单色（颜色i）的 -/
def Monochromatic (n : ℕ) (r : ℕ) (s : Finset (Fin n)) (i : Fin r) 
    (c : EdgeColoring n r) : Prop :=
  ∀ (x : Fin n) (_hx : x ∈ s) (y : Fin n) (_hy : y ∈ s), x ≠ y → c {x, y} = i

/-- Ramsey数R(k₁,...,kᵣ)：使得K_N的r-边着色必包含单色K_{kᵢ}的最小N -/
noncomputable def ramseyNumber (r : ℕ) (k : Fin r → ℕ) : ℕ :=
  sInf { N : ℕ | N > 0 ∧ ∀ c : EdgeColoring N r, 
    ∃ i : Fin r, ∃ s : Finset (Fin N), 
      s.card = k i ∧ Monochromatic N r s i c }

/-! ## 辅助引理 -/

/-- 将着色限制到子集上 -/
noncomputable def restrictColoring {n m r : ℕ} (s : Finset (Fin n)) (hs : s.card = m) 
    (c : EdgeColoring n r) : EdgeColoring m r :=
  let emb : Fin m ↪ Fin n := {
    toFun := fun i => (Finset.orderIsoOfFin s hs i : Fin n)
    inj' := by intro i j hij; simpa using hij
  }
  fun e => c (Finset.map emb e)

/-- 限制着色保持单色性 -/
lemma Monochromatic_restrict {n m r : ℕ} (s : Finset (Fin n)) (hs : s.card = m)
    (c : EdgeColoring n r) (i : Fin r) (t : Finset (Fin m)) :
    Monochromatic m r t i (restrictColoring s hs c) ↔
    Monochromatic n r (Finset.map (Finset.orderIsoOfFin s hs).toEmbedding t) i c := by
  simp [Monochromatic, restrictColoring]
  <;> aesop

/-- 鸽巢原理：如果n个物品放入r个盒子，至少有一个盒子有⌈n/r⌉个物品 -/
lemma pigeonhole_principle {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (n : ℕ) (hn : Fintype.card α > n * Fintype.card β) :
    ∃ b : β, {a : α | f a = b}.toFinset.card > n := by
  by_contra h
  push_neg at h
  have h_eq : ∀ b : β, {a : α | f a = b}.toFinset = Finset.univ.filter (fun a => f a = b) := by
    intro b
    ext a
    simp [Set.toFinset]
  have h1 : ∑ b : β, {a : α | f a = b}.toFinset.card = Fintype.card α := by
    simp_rw [h_eq]
    rw [←Finset.card_univ]
    rw [Finset.card_eq_sum_card_image f Finset.univ]
    apply Finset.sum_subset (Finset.subset_univ (Finset.univ.image f))
    intro b _ hb
    simp at hb ⊢
    exact hb
  have h2 : ∑ b : β, {a : α | f a = b}.toFinset.card ≤ Fintype.card β * n := by
    simp_rw [h_eq]
    apply Finset.sum_le_card_nsmul
    intro b _
    have : (Finset.univ.filter (fun a => f a = b)).card ≤ n := by
      have h' := h b
      simp [Set.toFinset] at h'
      exact h'
    exact this
  have h3 : Fintype.card α ≤ Fintype.card β * n := by linarith
  have h4 : Fintype.card β * n < Fintype.card α := by
    rw [mul_comm]
    exact hn
  linarith

/-- 对于正数k，存在足够大的N使得性质成立 -/
lemma exists_large_N (k : ℕ) (_hk : k > 0) : ∃ N : ℕ, N ≥ k := by
  use k

/-- 构造指定大小的有限集 -/
lemma exists_finset_of_card (n N : ℕ) (hN : N ≥ n) : 
    ∃ s : Finset (Fin N), s.card = n := by
  use (Finset.univ : Finset (Fin n)).map (Fin.castLEEmb hN)
  simp

/-- 二元Ramsey定理：对任意s,t>0，存在N使得任意2-着色必有大小为s的红色团或大小为t的蓝色团 -/
theorem RamseyTheorem2 (s t : ℕ) (hs : s > 0) (ht : t > 0) :
    ∃ N : ℕ, N > 0 ∧ ∀ c : EdgeColoring N 2, 
    (∃ s' : Finset (Fin N), s'.card = s ∧ Monochromatic N 2 s' 0 c) ∨
    (∃ t' : Finset (Fin N), t'.card = t ∧ Monochromatic N 2 t' 1 c) := by
  /- 对s+t进行归纳证明 -/
  induction' h : s + t using Nat.strongRecOn with n ih generalizing s t
  by_cases h_s1 : s = 1
  · -- s = 1时，N=1即可（单个顶点平凡地构成1-团）
    rw [h_s1]
    use 1
    constructor
    · norm_num
    · intro c
      left
      use {0}
      constructor
      · simp
      · simp [Monochromatic]
  by_cases h_t1 : t = 1
  · -- t = 1时同理
    rw [h_t1]
    use 1
    constructor
    · norm_num
    · intro c
      right
      use {0}
      constructor
      · simp
      · simp [Monochromatic]
  -- s > 1且t > 1
  have hs' : s - 1 > 0 := by omega
  have ht' : t - 1 > 0 := by omega
  have h1 : s - 1 + t < n := by
    rw [←h]
    omega
  have h2 : s + (t - 1) < n := by
    rw [←h]
    omega
  obtain ⟨N1, hN1_pos, hN1⟩ := ih (s - 1 + t) h1 (s - 1) t hs' ht (by omega)
  obtain ⟨N2, hN2_pos, hN2⟩ := ih (s + (t - 1)) h2 s (t - 1) hs ht' (by omega)
  let N := N1 + N2
  use N
  constructor
  · -- N > 0
    omega
  · intro c
    -- 取顶点0，按从0出发的边颜色分类
    let S0 := Finset.filter (fun v : Fin N => v ≠ 0 ∧ c {0, v} = 0) Finset.univ
    let S1 := Finset.filter (fun v : Fin N => v ≠ 0 ∧ c {0, v} = 1) Finset.univ
    have h_card : S0.card + S1.card = N - 1 := by
      have : S0 ∪ S1 = Finset.univ \ {0} := by
        ext v
        simp [S0, S1]
        by_cases h_v0 : v = 0
        · simp [h_v0]
        · simp [h_v0]
          fin_cases c {0, v} <;> simp
      have h_disj : Disjoint S0 S1 := by
        rw [Finset.disjoint_iff_inter_eq_empty]
        ext v
        simp [S0, S1]
      rw [←Finset.card_union_of_disjoint h_disj, this]
      simp [Finset.card_erase_of_mem]
    have h_cases : S0.card ≥ N1 ∨ S1.card ≥ N2 := by
      by_contra h
      push_neg at h
      have : S0.card + S1.card ≤ N1 - 1 + (N2 - 1) := by
        have h1 : S0.card ≤ N1 - 1 := by omega
        have h2 : S1.card ≤ N2 - 1 := by omega
        omega
      omega
    rcases h_cases with hS0 | hS1
    · -- S0足够大，包含N1个顶点
      obtain ⟨T0, hT0_sub, hT0_card⟩ := exists_smaller_set S0 N1 (by omega)
      have hT0_card' : T0.card = N1 := by linarith
      have h_ramsey := hN1 (restrictColoring T0 hT0_card' c)
      rcases h_ramsey with (⟨s', hs'_card, hs'_mono⟩) | (⟨t', ht'_card, ht'_mono⟩)
      · -- T0中有红色(s-1)-团，加入顶点0得到红色s-团
        left
        use insert 0 (Finset.map (Finset.orderIsoOfFin T0 hT0_card').toEmbedding s')
        constructor
        · -- 计算团的大小
          have h0 : 0 ∉ Finset.map (Finset.orderIsoOfFin T0 hT0_card').toEmbedding s' := by
            simp
            intro x hx h_contra
            have : (Finset.orderIsoOfFin T0 hT0_card' x : Fin N) ∈ T0 := by
              simp [h_contra]
            have : (Finset.orderIsoOfFin T0 hT0_card' x : Fin N) ≠ 0 := by
              have hT0 : T0 ⊆ S0 := hT0_sub
              have hS0_mem : (Finset.orderIsoOfFin T0 hT0_card' x : Fin N) ∈ S0 := hT0 this
              simp [S0] at hS0_mem
              exact hS0_mem.1
            contradiction
          rw [Finset.card_insert_of_not_mem h0]
          rw [hs'_card]
          simp [hT0_card']
          omega
        · -- 证明单色性
          simp [Monochromatic] at hs'_mono ⊢
          intro x hx y hy hxy
          by_cases hx0 : x = 0
          · -- x = 0，y在T0映射中
            rw [hx0]
            by_cases hy0 : y = 0
            · contradiction
            · have hy' : y ∈ Finset.map (Finset.orderIsoOfFin T0 hT0_card').toEmbedding s' := hy
              simp at hy'
              rcases hy' with ⟨w, hw, rfl⟩
              have hT0 : (Finset.orderIsoOfFin T0 hT0_card' w : Fin N) ∈ S0 := by
                apply hT0_sub
                simp [hw]
              simp [S0] at hT0
              have : c {0, (Finset.orderIsoOfFin T0 hT0_card' w : Fin N)} = 0 := hT0.2
              rw [show ({0, (Finset.orderIsoOfFin T0 hT0_card' w : Fin N)} : Finset (Fin N)) = {x, y} by simp [hx0]; ext z; simp; tauto]
              exact this
          · -- x ≠ 0
            by_cases hy0 : y = 0
            · -- y = 0
              rw [hy0]
              have hx' : x ∈ Finset.map (Finset.orderIsoOfFin T0 hT0_card').toEmbedding s' := hx
              simp at hx'
              rcases hx' with ⟨w, hw, rfl⟩
              have hT0 : (Finset.orderIsoOfFin T0 hT0_card' w : Fin N) ∈ S0 := by
                apply hT0_sub
                simp [hw]
              simp [S0] at hT0
              have : c {0, (Finset.orderIsoOfFin T0 hT0_card' w : Fin N)} = 0 := hT0.2
              rw [show ({0, (Finset.orderIsoOfFin T0 hT0_card' w : Fin N)} : Finset (Fin N)) = {y, x} by simp [hy0]; ext z; simp; tauto]
              rw [show c {y, x} = c {x, y} by rw [Finset.pair_comm]]
              exact this
            · -- x, y都在T0映射中
              have hx' : x ∈ Finset.map (Finset.orderIsoOfFin T0 hT0_card').toEmbedding s' := hx
              have hy' : y ∈ Finset.map (Finset.orderIsoOfFin T0 hT0_card').toEmbedding s' := hy
              have h_mono : Monochromatic N 2 (Finset.map (Finset.orderIsoOfFin T0 hT0_card').toEmbedding s') 0 c := by
                rw [←Monochromatic_restrict T0 hT0_card' c 0 s']
                exact hs'_mono
              simp [Monochromatic] at h_mono
              exact h_mono x hx' y hy' hxy
      · -- T0中有蓝色t-团
        right
        use Finset.map (Finset.orderIsoOfFin T0 hT0_card').toEmbedding t'
        constructor
        · rw [ht'_card]; simp [hT0_card']
        · rw [←Monochromatic_restrict T0 hT0_card' c 1 t']
          exact ht'_mono
    · -- S1足够大，包含N2个顶点
      obtain ⟨T1, hT1_sub, hT1_card⟩ := exists_smaller_set S1 N2 (by omega)
      have hT1_card' : T1.card = N2 := by linarith
      have h_ramsey := hN2 (restrictColoring T1 hT1_card' c)
      rcases h_ramsey with (⟨s', hs'_card, hs'_mono⟩) | (⟨t', ht'_card, ht'_mono⟩)
      · -- T1中有红色s-团
        left
        use Finset.map (Finset.orderIsoOfFin T1 hT1_card').toEmbedding s'
        constructor
        · rw [hs'_card]; simp [hT1_card']
        · rw [←Monochromatic_restrict T1 hT1_card' c 0 s']
          exact hs'_mono
      · -- T1中有蓝色(t-1)-团，加入顶点0得到蓝色t-团
        right
        use insert 0 (Finset.map (Finset.orderIsoOfFin T1 hT1_card').toEmbedding t')
        constructor
        · -- 计算团的大小
          have h0 : 0 ∉ Finset.map (Finset.orderIsoOfFin T1 hT1_card').toEmbedding t' := by
            simp
            intro x hx h_contra
            have : (Finset.orderIsoOfFin T1 hT1_card' x : Fin N) ∈ T1 := by
              simp [h_contra]
            have : (Finset.orderIsoOfFin T1 hT1_card' x : Fin N) ≠ 0 := by
              have hT1 : T1 ⊆ S1 := hT1_sub
              have hS1_mem : (Finset.orderIsoOfFin T1 hT1_card' x : Fin N) ∈ S1 := hT1 this
              simp [S1] at hS1_mem
              exact hS1_mem.1
            contradiction
          rw [Finset.card_insert_of_not_mem h0]
          rw [ht'_card]
          simp [hT1_card']
          omega
        · -- 证明单色性
          simp [Monochromatic] at ht'_mono ⊢
          intro x hx y hy hxy
          by_cases hx0 : x = 0
          · -- x = 0
            rw [hx0]
            by_cases hy0 : y = 0
            · contradiction
            · have hy' : y ∈ Finset.map (Finset.orderIsoOfFin T1 hT1_card').toEmbedding t' := hy
              simp at hy'
              rcases hy' with ⟨w, hw, rfl⟩
              have hT1 : (Finset.orderIsoOfFin T1 hT1_card' w : Fin N) ∈ S1 := by
                apply hT1_sub
                simp [hw]
              simp [S1] at hT1
              have : c {0, (Finset.orderIsoOfFin T1 hT1_card' w : Fin N)} = 1 := hT1.2
              rw [show ({0, (Finset.orderIsoOfFin T1 hT1_card' w : Fin N)} : Finset (Fin N)) = {x, y} by simp [hx0]; ext z; simp; tauto]
              exact this
          · -- x ≠ 0
            by_cases hy0 : y = 0
            · -- y = 0
              rw [hy0]
              have hx' : x ∈ Finset.map (Finset.orderIsoOfFin T1 hT1_card').toEmbedding t' := hx
              simp at hx'
              rcases hx' with ⟨w, hw, rfl⟩
              have hT1 : (Finset.orderIsoOfFin T1 hT1_card' w : Fin N) ∈ S1 := by
                apply hT1_sub
                simp [hw]
              simp [S1] at hT1
              have : c {0, (Finset.orderIsoOfFin T1 hT1_card' w : Fin N)} = 1 := hT1.2
              rw [show ({0, (Finset.orderIsoOfFin T1 hT1_card' w : Fin N)} : Finset (Fin N)) = {y, x} by simp [hy0]; ext z; simp; tauto]
              rw [show c {y, x} = c {x, y} by rw [Finset.pair_comm]]
              exact this
            · -- x, y都在T1映射中
              have hx' : x ∈ Finset.map (Finset.orderIsoOfFin T1 hT1_card').toEmbedding t' := hx
              have hy' : y ∈ Finset.map (Finset.orderIsoOfFin T1 hT1_card').toEmbedding t' := hy
              have h_mono : Monochromatic N 2 (Finset.map (Finset.orderIsoOfFin T1 hT1_card').toEmbedding t') 1 c := by
                rw [←Monochromatic_restrict T1 hT1_card' c 1 t']
                exact ht'_mono
              simp [Monochromatic] at h_mono
              exact h_mono x hx' y hy' hxy

/-! ## Ramsey定理证明 -/

/-- 
Ramsey定理（简化版本）：对于任意颜色数r和大小k₁,...,kᵣ，
存在N使得K_N的边用r种颜色着色时，
必存在i使得有kᵢ个顶点的单色团。

这是Ramsey定理的经典形式，证明采用对r的归纳法，
将r色问题归约为2色问题。
-/ 
theorem RamseyTheorem (r : ℕ) (hr : r > 0) (k : Fin r → ℕ) 
    (hk : ∀ i, k i > 0) :
    ∃ N : ℕ, N > 0 ∧ ∀ c : EdgeColoring N r, 
    ∃ i : Fin r, ∃ s : Finset (Fin N), 
      s.card = k i ∧ Monochromatic N r s i c := by
  
  -- 对r进行归纳
  induction r with
  | zero => 
    -- r = 0与hr矛盾
    linarith
  
  | succ r ih =>
    -- 处理r = 1的情况（基础情形）
    cases r with
    | zero =>
      -- r = 1的情况：只有一个颜色
      use k 0
      constructor
      · exact hk 0
      · intro c
        use 0
        -- 取整个顶点集作为单色团
        use Finset.univ
        constructor
        · -- 证明card = k 0
          have h1 : (Finset.univ : Finset (Fin (k 0))).card = k 0 := by
            rw [Finset.card_univ]
            simp [Fintype.card_fin]
          exact h1
        · -- 证明是单色的
          intro x _ y _ hxy
          have : c {x, y} = 0 := by
            have h : ∀ i : Fin 1, i = 0 := by intro i; fin_cases i; simp
            exact h (c {x, y})
          exact this
    
    | succ r =>
      -- r ≥ 2的情况：使用归纳假设和二元Ramsey定理
      -- 将r+2种颜色归约为2种颜色：颜色0 vs 剩余r+1种颜色
      let k' : Fin (r + 1) → ℕ := fun i => k i.succ
      have hk' : ∀ i, k' i > 0 := by
        intro i
        exact hk i.succ
      obtain ⟨N1, hN1_pos, hN1⟩ := ih (by linarith) k' hk'
      have h_ramsey2 := RamseyTheorem2 (k 0) N1 (hk 0) hN1_pos
      rcases h_ramsey2 with ⟨N, hN_pos, hN⟩
      use N
      constructor
      · exact hN_pos
      · intro c
        -- 定义2-着色：颜色0保持，其余颜色统一为1
        let c2 : EdgeColoring N 2 := fun e => if c e = 0 then 0 else 1
        have h2 := hN c2
        rcases h2 with (⟨s', hs'_card, hs'_mono⟩) | (⟨t', ht'_card, ht'_mono⟩)
        · -- 存在颜色0的大小为k0的团
          left
          use 0
          use s'
          constructor
          · exact hs'_card
          · simp [Monochromatic] at hs'_mono ⊢
            intro x hx y hy hxy
            have : c2 {x, y} = 0 := hs'_mono x hx y hy hxy
            simp [c2] at this
            exact this
        · -- 存在大小为N1的团，所有边颜色不为0
          have ht'_mono' : ∀ (x y : Fin N), x ∈ t' → y ∈ t' → x ≠ y → c {x, y} ≠ 0 := by
            simp [Monochromatic] at ht'_mono
            intro x y hx hy hxy
            have : c2 {x, y} = 1 := ht'_mono x hx y hy hxy
            simp [c2] at this
            exact this
          -- 构造(r+1)-着色
          let c' : EdgeColoring N1 (r + 1) := fun e =>
            let mapped := Finset.map (Finset.orderIsoOfFin t' ht'_card').toEmbedding e
            if h : c mapped = 0 then
              0
            else
              Fin.pred (c mapped) (by simpa using h)
          have hN1' := hN1 c'
          rcases hN1' with ⟨i, s'', hs''_card, hs''_mono⟩
          use i.succ
          use Finset.map (Finset.orderIsoOfFin t' ht'_card').toEmbedding s''
          constructor
          · rw [hs''_card]
            simp
          · -- 证明单色性
            simp [Monochromatic] at hs''_mono ⊢
            intro x hx y hy hxy
            have hx' : x ∈ Finset.map (Finset.orderIsoOfFin t' ht'_card').toEmbedding s'' := hx
            have hy' : y ∈ Finset.map (Finset.orderIsoOfFin t' ht'_card').toEmbedding s'' := hy
            simp at hx' hy'
            rcases hx' with ⟨a, ha, rfl⟩
            rcases hy' with ⟨b, hb, rfl⟩
            have h_ab : a ≠ b := by
              intro h_eq
              apply hxy
              simp [h_eq]
            have h_c' : c' {a, b} = i := hs''_mono a ha b hb h_ab
            have h_ne0 : c (Finset.map (Finset.orderIsoOfFin t' ht'_card').toEmbedding {a, b}) ≠ 0 := by
              have h1 : (Finset.orderIsoOfFin t' ht'_card' a : Fin N) ∈ t' := by simp
              have h2 : (Finset.orderIsoOfFin t' ht'_card' b : Fin N) ∈ t' := by simp
              have h3 : (Finset.orderIsoOfFin t' ht'_card' a : Fin N) ≠ (Finset.orderIsoOfFin t' ht'_card' b : Fin N) := by
                intro h_eq
                apply hxy
                have h_eq' : (Finset.orderIsoOfFin t' ht'_card' a : {x // x ∈ t'}) = (Finset.orderIsoOfFin t' ht'_card' b : {x // x ∈ t'}) := by
                  apply Subtype.ext
                  exact h_eq
                have : a = b := (Finset.orderIsoOfFin t' ht'_card').injective h_eq'
                contradiction
              exact ht'_mono' _ _ h1 h2 h3
            simp [c', h_ne0] at h_c'
            have h_eq : c (Finset.map (Finset.orderIsoOfFin t' ht'_card').toEmbedding {a, b}) = i.succ := by
              rw [h_c']
              simp
            have h_set_eq : (Finset.map (Finset.orderIsoOfFin t' ht'_card').toEmbedding {a, b} : Finset (Fin N)) = {x, y} := by
              ext z
              simp
              constructor
              · rintro (rfl | rfl)
                · tauto
                · tauto
              · rintro (rfl | rfl)
                · tauto
                · tauto
            rw [h_set_eq]
            exact h_eq

/-- 
经典的二元Ramsey定理（r = 2的特殊情形）：
对于任意s, t ≥ 1，存在N使得K_N的边用2种颜色（红/蓝）着色时，
要么存在s个顶点的红色团，要么存在t个顶点的蓝色团。

这是Ramsey定理最著名的形式，也是Diestel《图论》中陈述的形式。
-/ 
theorem RamseyTheoremBinary (s t : ℕ) (hs : s > 0) (ht : t > 0) :
    ∃ N : ℕ, N > 0 ∧ ∀ c : EdgeColoring N 2, 
    (∃ s' : Finset (Fin N), s'.card = s ∧ Monochromatic N 2 s' 0 c) ∨
    (∃ t' : Finset (Fin N), t'.card = t ∧ Monochromatic N 2 t' 1 c) := by
  exact RamseyTheorem2 s t hs ht

/-- 
Ramsey数的一般上界：R(s, t) ≤ 2^(s+t-2)
这是证明Ramsey定理存在性的关键递推关系。
-/ 
lemma ramsey_upper_bound_general (s t : ℕ) (hs : s > 0) (ht : t > 0) :
    ramseyNumber 2 (λ i => if i = 0 then s else t) ≤ 2 ^ (s + t - 2) := by
  induction' h : s + t using Nat.strongRecOn with n ih generalizing s t
  by_cases h_s1 : s = 1
  · rw [h_s1]
    simp [ramseyNumber, Monochromatic]
    apply Nat.sInf_le
    constructor
    · norm_num
    · intro c
      left
      use {0}
      constructor <;> simp
  by_cases h_t1 : t = 1
  · rw [h_t1]
    simp [ramseyNumber, Monochromatic]
    apply Nat.sInf_le
    constructor
    · norm_num
    · intro c
      right
      use {0}
      constructor <;> simp
  have hs' : s - 1 > 0 := by omega
  have ht' : t - 1 > 0 := by omega
  have h1 : s - 1 + t < n := by rw [←h]; omega
  have h2 : s + (t - 1) < n := by rw [←h]; omega
  have h_ub1 := ih (s - 1 + t) h1 (s - 1) t hs' ht (by omega)
  have h_ub2 := ih (s + (t - 1)) h2 s (t - 1) hs ht' (by omega)
  have h_rec := ramseyNumber_recurrence s t (by omega) (by omega)
  have h3 : ramseyNumber 2 (λ i => if i = 0 then s else t) ≤ 
      ramseyNumber 2 (λ i => if i = 0 then s - 1 else t) + 
      ramseyNumber 2 (λ i => if i = 0 then s else t - 1) := h_rec
  have h4 : ramseyNumber 2 (λ i => if i = 0 then s - 1 else t) ≤ 2 ^ (s - 1 + t - 2) := h_ub1
  have h5 : ramseyNumber 2 (λ i => if i = 0 then s else t - 1) ≤ 2 ^ (s + (t - 1) - 2) := h_ub2
  have h6 : 2 ^ (s - 1 + t - 2) + 2 ^ (s + (t - 1) - 2) = 2 ^ (s + t - 2) := by
    have h1 : s - 1 + t - 2 = s + t - 3 := by omega
    have h2 : s + (t - 1) - 2 = s + t - 3 := by omega
    have h3 : s + t - 2 = s + t - 3 + 1 := by omega
    rw [h1, h2, h3]
    ring
  linarith [h3, h4, h5, h6]

/-- 
Ramsey数的递推上界：R(s, t) ≤ R(s-1, t) + R(s, t-1)
这是证明Ramsey定理存在性的关键递推关系。
-/ 
lemma ramseyNumber_recurrence (s t : ℕ) (hs : s > 1) (ht : t > 1) :
    ramseyNumber 2 (λ i => if i = 0 then s else t) ≤ 
    ramseyNumber 2 (λ i => if i = 0 then s - 1 else t) + 
    ramseyNumber 2 (λ i => if i = 0 then s else t - 1) := by
  let N1 := ramseyNumber 2 (λ i => if i = 0 then s - 1 else t)
  let N2 := ramseyNumber 2 (λ i => if i = 0 then s else t - 1)
  let N := N1 + N2
  dsimp [ramseyNumber]
  apply Nat.sInf_le
  constructor
  · -- 证明N > 0
    have hN1_pos : N1 > 0 := by
      have h : N1 ∈ {N | N > 0 ∧ ∀ c : EdgeColoring N 2, ∃ i s', s'.card = (if i = 0 then s - 1 else t) ∧ Monochromatic N 2 s' i c} := by
        apply Nat.sInf_mem
        obtain ⟨N, hN_pos, hN⟩ := RamseyTheorem2 (s - 1) t (by omega) ht
        use N
        constructor
        · exact hN_pos
        · intro c
          specialize hN c
          rcases hN with (⟨s', hs'_card, hs'_mono⟩) | (⟨t', ht'_card, ht'_mono⟩)
          · use 0, s'
            constructor
            · simp [hs'_card]
            · exact hs'_mono
          · use 1, t'
            constructor
            · simp [ht'_card]
            · exact ht'_mono
      exact h.1
    have hN2_pos : N2 > 0 := by
      have h : N2 ∈ {N | N > 0 ∧ ∀ c : EdgeColoring N 2, ∃ i s', s'.card = (if i = 0 then s else t - 1) ∧ Monochromatic N 2 s' i c} := by
        apply Nat.sInf_mem
        obtain ⟨N, hN_pos, hN⟩ := RamseyTheorem2 s (t - 1) hs (by omega)
        use N
        constructor
        · exact hN_pos
        · intro c
          specialize hN c
          rcases hN with (⟨s', hs'_card, hs'_mono⟩) | (⟨t', ht'_card, ht'_mono⟩)
          · use 0, s'
            constructor
            · simp [hs'_card]
            · exact hs'_mono
          · use 1, t'
            constructor
            · simp [ht'_card]
            · exact ht'_mono
      exact h.1
    omega
  · -- 证明N满足Ramsey性质
    intro c
    have h_ramsey := RamseyTheorem2 s t hs ht
    rcases h_ramsey with ⟨N', hN'_pos, hN'⟩
    have hN1_prop : ∀ c : EdgeColoring N1 2, (∃ s' : Finset (Fin N1), s'.card = s - 1 ∧ Monochromatic N1 2 s' 0 c) ∨ (∃ t' : Finset (Fin N1), t'.card = t ∧ Monochromatic N1 2 t' 1 c) := by
      have h : N1 ∈ {N | N > 0 ∧ ∀ c : EdgeColoring N 2, ∃ i s', s'.card = (if i = 0 then s - 1 else t) ∧ Monochromatic N 2 s' i c} := by
        apply Nat.sInf_mem
        obtain ⟨N, hN_pos, hN⟩ := RamseyTheorem2 (s - 1) t (by omega) ht
        use N
        constructor
        · exact hN_pos
        · intro c
          specialize hN c
          rcases hN with (⟨s', hs'_card, hs'_mono⟩) | (⟨t', ht'_card, ht'_mono⟩)
          · use 0, s'
            constructor
            · simp [hs'_card]
            · exact hs'_mono
          · use 1, t'
            constructor
            · simp [ht'_card]
            · exact ht'_mono
      exact h.2
    have hN2_prop : ∀ c : EdgeColoring N2 2, (∃ s' : Finset (Fin N2), s'.card = s ∧ Monochromatic N2 2 s' 0 c) ∨ (∃ t' : Finset (Fin N2), t'.card = t - 1 ∧ Monochromatic N2 2 t' 1 c) := by
      have h : N2 ∈ {N | N > 0 ∧ ∀ c : EdgeColoring N 2, ∃ i s', s'.card = (if i = 0 then s else t - 1) ∧ Monochromatic N 2 s' i c} := by
        apply Nat.sInf_mem
        obtain ⟨N, hN_pos, hN⟩ := RamseyTheorem2 s (t - 1) hs (by omega)
        use N
        constructor
        · exact hN_pos
        · intro c
          specialize hN c
          rcases hN with (⟨s', hs'_card, hs'_mono⟩) | (⟨t', ht'_card, ht'_mono⟩)
          · use 0, s'
            constructor
            · simp [hs'_card]
            · exact hs'_mono
          · use 1, t'
            constructor
            · simp [ht'_card]
            · exact ht'_mono
      exact h.2
    -- 使用与RamseyTheorem2相同的证明结构
    let S0 := Finset.filter (fun v : Fin N => v ≠ 0 ∧ c {0, v} = 0) Finset.univ
    let S1 := Finset.filter (fun v : Fin N => v ≠ 0 ∧ c {0, v} = 1) Finset.univ
    have h_card : S0.card + S1.card = N - 1 := by
      have : S0 ∪ S1 = Finset.univ \ {0} := by
        ext v
        simp [S0, S1]
        by_cases h_v0 : v = 0
        · simp [h_v0]
        · simp [h_v0]
          fin_cases c {0, v} <;> simp
      have h_disj : Disjoint S0 S1 := by
        rw [Finset.disjoint_iff_inter_eq_empty]
        ext v
        simp [S0, S1]
      rw [←Finset.card_union_of_disjoint h_disj, this]
      simp [Finset.card_erase_of_mem]
    have h_cases : S0.card ≥ N1 ∨ S1.card ≥ N2 := by
      by_contra h
      push_neg at h
      have : S0.card + S1.card ≤ N1 - 1 + (N2 - 1) := by
        have h1 : S0.card ≤ N1 - 1 := by omega
        have h2 : S1.card ≤ N2 - 1 := by omega
        omega
      omega
    rcases h_cases with hS0 | hS1
    · obtain ⟨T0, hT0_sub, hT0_card⟩ := exists_smaller_set S0 N1 (by omega)
      have hT0_card' : T0.card = N1 := by linarith
      have h_ramsey := hN1_prop (restrictColoring T0 hT0_card' c)
      rcases h_ramsey with (⟨s', hs'_card, hs'_mono⟩) | (⟨t', ht'_card, ht'_mono⟩)
      · left
        use 0
        use insert 0 (Finset.map (Finset.orderIsoOfFin T0 hT0_card').toEmbedding s')
        constructor
        · have h0 : 0 ∉ Finset.map (Finset.orderIsoOfFin T0 hT0_card').toEmbedding s' := by
            simp
            intro x hx h_contra
            have : (Finset.orderIsoOfFin T0 hT0_card' x : Fin N) ∈ T0 := by simp [h_contra]
            have : (Finset.orderIsoOfFin T0 hT0_card' x : Fin N) ≠ 0 := by
              have hT0 : T0 ⊆ S0 := hT0_sub
              have hS0_mem : (Finset.orderIsoOfFin T0 hT0_card' x : Fin N) ∈ S0 := hT0 this
              simp [S0] at hS0_mem
              exact hS0_mem.1
            contradiction
          rw [Finset.card_insert_of_not_mem h0]
          rw [hs'_card]
          simp [hT0_card']
          omega
        · simp [Monochromatic] at hs'_mono ⊢
          intro x hx y hy hxy
          by_cases hx0 : x = 0
          · rw [hx0]
            by_cases hy0 : y = 0
            · contradiction
            · have hy' : y ∈ Finset.map (Finset.orderIsoOfFin T0 hT0_card').toEmbedding s' := hy
              simp at hy'
              rcases hy' with ⟨w, hw, rfl⟩
              have hT0 : (Finset.orderIsoOfFin T0 hT0_card' w : Fin N) ∈ S0 := by
                apply hT0_sub
                simp [hw]
              simp [S0] at hT0
              have : c {0, (Finset.orderIsoOfFin T0 hT0_card' w : Fin N)} = 0 := hT0.2
              rw [show ({0, (Finset.orderIsoOfFin T0 hT0_card' w : Fin N)} : Finset (Fin N)) = {x, y} by simp [hx0]; ext z; simp; tauto]
              exact this
          · by_cases hy0 : y = 0
            · rw [hy0]
              have hx' : x ∈ Finset.map (Finset.orderIsoOfFin T0 hT0_card').toEmbedding s' := hx
              simp at hx'
              rcases hx' with ⟨w, hw, rfl⟩
              have hT0 : (Finset.orderIsoOfFin T0 hT0_card' w : Fin N) ∈ S0 := by
                apply hT0_sub
                simp [hw]
              simp [S0] at hT0
              have : c {0, (Finset.orderIsoOfFin T0 hT0_card' w : Fin N)} = 0 := hT0.2
              rw [show ({0, (Finset.orderIsoOfFin T0 hT0_card' w : Fin N)} : Finset (Fin N)) = {y, x} by simp [hy0]; ext z; simp; tauto]
              rw [show c {y, x} = c {x, y} by rw [Finset.pair_comm]]
              exact this
            · have hx' : x ∈ Finset.map (Finset.orderIsoOfFin T0 hT0_card').toEmbedding s' := hx
              have hy' : y ∈ Finset.map (Finset.orderIsoOfFin T0 hT0_card').toEmbedding s' := hy
              have h_mono : Monochromatic N 2 (Finset.map (Finset.orderIsoOfFin T0 hT0_card').toEmbedding s') 0 c := by
                rw [←Monochromatic_restrict T0 hT0_card' c 0 s']
                exact hs'_mono
              simp [Monochromatic] at h_mono
              exact h_mono x hx' y hy' hxy
      · right
        use 1
        use Finset.map (Finset.orderIsoOfFin T0 hT0_card').toEmbedding t'
        constructor
        · rw [ht'_card]; simp [hT0_card']
        · rw [←Monochromatic_restrict T0 hT0_card' c 1 t']
          exact ht'_mono
    · obtain ⟨T1, hT1_sub, hT1_card⟩ := exists_smaller_set S1 N2 (by omega)
      have hT1_card' : T1.card = N2 := by linarith
      have h_ramsey := hN2_prop (restrictColoring T1 hT1_card' c)
      rcases h_ramsey with (⟨s', hs'_card, hs'_mono⟩) | (⟨t', ht'_card, ht'_mono⟩)
      · left
        use 0
        use Finset.map (Finset.orderIsoOfFin T1 hT1_card').toEmbedding s'
        constructor
        · rw [hs'_card]; simp [hT1_card']
        · rw [←Monochromatic_restrict T1 hT1_card' c 0 s']
          exact hs'_mono
      · right
        use 1
        use insert 0 (Finset.map (Finset.orderIsoOfFin T1 hT1_card').toEmbedding t')
        constructor
        · have h0 : 0 ∉ Finset.map (Finset.orderIsoOfFin T1 hT1_card').toEmbedding t' := by
            simp
            intro x hx h_contra
            have : (Finset.orderIsoOfFin T1 hT1_card' x : Fin N) ∈ T1 := by simp [h_contra]
            have : (Finset.orderIsoOfFin T1 hT1_card' x : Fin N) ≠ 0 := by
              have hT1 : T1 ⊆ S1 := hT1_sub
              have hS1_mem : (Finset.orderIsoOfFin T1 hT1_card' x : Fin N) ∈ S1 := hT1 this
              simp [S1] at hS1_mem
              exact hS1_mem.1
            contradiction
          rw [Finset.card_insert_of_not_mem h0]
          rw [ht'_card]
          simp [hT1_card']
          omega
        · simp [Monochromatic] at ht'_mono ⊢
          intro x hx y hy hxy
          by_cases hx0 : x = 0
          · rw [hx0]
            by_cases hy0 : y = 0
            · contradiction
            · have hy' : y ∈ Finset.map (Finset.orderIsoOfFin T1 hT1_card').toEmbedding t' := hy
              simp at hy'
              rcases hy' with ⟨w, hw, rfl⟩
              have hT1 : (Finset.orderIsoOfFin T1 hT1_card' w : Fin N) ∈ S1 := by
                apply hT1_sub
                simp [hw]
              simp [S1] at hT1
              have : c {0, (Finset.orderIsoOfFin T1 hT1_card' w : Fin N)} = 1 := hT1.2
              rw [show ({0, (Finset.orderIsoOfFin T1 hT1_card' w : Fin N)} : Finset (Fin N)) = {x, y} by simp [hx0]; ext z; simp; tauto]
              exact this
          · by_cases hy0 : y = 0
            · rw [hy0]
              have hx' : x ∈ Finset.map (Finset.orderIsoOfFin T1 hT1_card').toEmbedding t' := hx
              simp at hx'
              rcases hx' with ⟨w, hw, rfl⟩
              have hT1 : (Finset.orderIsoOfFin T1 hT1_card' w : Fin N) ∈ S1 := by
                apply hT1_sub
                simp [hw]
              simp [S1] at hT1
              have : c {0, (Finset.orderIsoOfFin T1 hT1_card' w : Fin N)} = 1 := hT1.2
              rw [show ({0, (Finset.orderIsoOfFin T1 hT1_card' w : Fin N)} : Finset (Fin N)) = {y, x} by simp [hy0]; ext z; simp; tauto]
              rw [show c {y, x} = c {x, y} by rw [Finset.pair_comm]]
              exact this
            · have hx' : x ∈ Finset.map (Finset.orderIsoOfFin T1 hT1_card').toEmbedding t' := hx
              have hy' : y ∈ Finset.map (Finset.orderIsoOfFin T1 hT1_card').toEmbedding t' := hy
              have h_mono : Monochromatic N 2 (Finset.map (Finset.orderIsoOfFin T1 hT1_card').toEmbedding t') 1 c := by
                rw [←Monochromatic_restrict T1 hT1_card' c 1 t']
                exact ht'_mono
              simp [Monochromatic] at h_mono
              exact h_mono x hx' y hy' hxy

/-- Ramsey数的基本性质：R(k, k) ≤ 4^k -/
lemma ramseyNumber_upper_bound (k : ℕ) (_hk : k > 0) :
    ramseyNumber 2 (λ i => if i = 0 then k else k) ≤ 4 ^ k := by
  have h := ramsey_upper_bound_general k k (by assumption) (by assumption)
  have h2 : 2 ^ (k + k - 2) ≤ 4 ^ k := by
    have : k + k - 2 ≤ 2 * k := by omega
    have h3 : 2 ^ (k + k - 2) ≤ 2 ^ (2 * k) := by apply Nat.pow_le_pow_of_le_right; norm_num; omega
    have h4 : 2 ^ (2 * k) = 4 ^ k := by
      rw [show 4 = 2 ^ 2 by norm_num]
      rw [pow_mul]
    linarith
  linarith

/-- Ramsey数下界：R(k, k) ≥ 2^(k/2)（Erdős的下界）

**说明**：Erdős使用概率方法证明的下界。完整的形式化证明需要：
1. 有限图上的概率空间构造
2. 随机2-着色下单色k-团的期望计算
3. 期望小于1时存在无单色k-团的着色

该证明涉及较深的概率论和组合计数技巧，超出本项目当前范围。
此处使用axiom标记这一经典结果。-/
axiom ramseyNumber_lower_bound (k : ℕ) (hk : k ≥ 3) :
    2 ^ (k / 2) ≤ ramseyNumber 2 (λ i => if i = 0 then k else k)

/-- 
多色Ramsey定理（更一般的陈述）：
对于r种颜色和给定的团大小，存在Ramsey数
-/ 
theorem RamseyTheoremMulticolor (r : ℕ) (hr : r ≥ 2) (k : Fin r → ℕ) 
    (hk : ∀ i, k i ≥ 2) :
    ∃ N : ℕ, N > 0 ∧ ∀ c : EdgeColoring N r, 
    ∃ i : Fin r, ∃ s : Finset (Fin N), 
      s.card = k i ∧ Monochromatic N r s i c := by
  -- 转化为已证明的形式
  have h1 : ∀ i, k i > 0 := by
    intro i
    have := hk i
    linarith
  exact RamseyTheorem r (by linarith) k h1

/-- 
无限Ramsey定理的陈述：
对于任意r种颜色的完全图K_ℕ，存在无限单色子集

这是有限Ramsey定理到无限的推广，使用递归构造证明。
-/ 
theorem InfiniteRamsey {α : Type*} [Infinite α] [DecidableEq α] (r : ℕ) (hr : r > 0)
    (c : α → α → Fin r) (h_symm : ∀ x y, c x y = c y x) 
    (h_irrefl : ∀ x, c x x = ⟨0, hr⟩) :
    ∃ i : Fin r, ∃ s : Set α, s.Infinite ∧ 
      ∀ x ∈ s, ∀ y ∈ s, x ≠ y → c x y = i := by

  have step : ∀ (A : Set α), A.Infinite → 
      ∃ (v : α) (i : Fin r), v ∈ A ∧ {w ∈ A | w ≠ v ∧ c v w = i}.Infinite := by
    intro A hA
    have hA_nonempty : A.Nonempty := by
      apply Set.nonempty_of_not_isEmpty
      intro h_empty
      rw [h_empty] at hA
      simp at hA
    let v := Classical.choice hA_nonempty
    have hA'_inf : (A \ {v}).Infinite := by
      apply Set.Infinite.diff
      exact hA
      apply Set.toFinite
    have : ∃ i : Fin r, Set.Infinite {w ∈ A | w ≠ v ∧ c v w = i} := by
      have h1 : Infinite ↑(A \ {v}) := by rwa [Set.infinite_coe_iff]
      obtain ⟨i, hi⟩ := Finite.exists_infinite_fiber (fun (w : ↑(A \ {v})) => c v w.1)
      use i
      have h2 : {w ∈ A | w ≠ v ∧ c v w = i} = 
                Subtype.val '' {w : ↑(A \ {v}) | c v w.1 = i} := by
        ext w
        simp
        tauto
      rw [h2]
      apply Set.infinite_image_of_injOn
      · intro x _ y _ hxy
        exact Subtype.ext hxy
      · rwa [Set.infinite_coe_iff] at hi
    rcases this with ⟨i, hi⟩
    exact ⟨v, i, Classical.choice_spec hA_nonempty, hi⟩

  mutual
    def A_seq : ℕ → Set α
      | 0 => Set.univ
      | n+1 => {w ∈ A_seq n | w ≠ v_seq n ∧ c (v_seq n) w = colors_seq n}
    
    noncomputable def v_seq (n : ℕ) : α :=
      (Classical.choose (step (A_seq n) (hA_seq n))).1
    
    noncomputable def colors_seq (n : ℕ) : Fin r :=
      (Classical.choose (step (A_seq n) (hA_seq n))).2
    
    theorem hA_seq (n : ℕ) : (A_seq n).Infinite := by
      cases n with
      | zero => exact Set.infinite_univ
      | succ n => 
        have h := Classical.choose_spec (step (A_seq n) (hA_seq n))
        simp [A_seq, v_seq, colors_seq]
        exact h.2.2
  end

  have hA_mono : ∀ n m, n ≤ m → A_seq m ⊆ A_seq n := by
    intro n m hnm
    induction hnm with
    | refl => exact Set.subset_rfl
    | step k hnk ih =>
      have : A_seq (k+1) ⊆ A_seq k := by
        simp [A_seq]
        intro w hw h1 h2
        exact hw
      exact Set.Subset.trans this ih

  have hv_in : ∀ n, v_seq n ∈ A_seq n := by
    intro n
    have h := Classical.choose_spec (step (A_seq n) (hA_seq n))
    simp [v_seq]
    exact h.1

  have h_color : ∃ i : Fin r, Set.Infinite {n | colors_seq n = i} := by
    have : Infinite ℕ := by infer_instance
    have : Finite (Fin r) := by infer_instance
    obtain ⟨i, hi⟩ := Finite.exists_infinite_fiber colors_seq
    use i
    simp at hi ⊢
    exact hi

  rcases h_color with ⟨i, hi_inf⟩
  use i
  let s := {v_seq n | n ∈ {m | colors_seq m = i}}
  use s
  constructor
  · -- 证明s是无限集
    have h_inj : Function.Injective v_seq := by
      intro n m hnm
      wlog hnm' : n < m
      · have : m < n := by
          by_contra h'
          push_neg at h'
          have : m = n := by linarith
          contradiction
        -- 对称情况
        have h1 : v_seq m ∈ A_seq (n+1) := by
          have h2 : A_seq m ⊆ A_seq (n+1) := hA_mono (n+1) m (by linarith)
          have h3 : v_seq m ∈ A_seq m := hv_in m
          exact h2 h3
        simp [A_seq] at h1
        have : v_seq m ≠ v_seq n := h1.1
        contradiction
      -- n < m
      have h1 : v_seq m ∈ A_seq (n+1) := by
        have h2 : A_seq m ⊆ A_seq (n+1) := hA_mono (n+1) m (by linarith)
        have h3 : v_seq m ∈ A_seq m := hv_in m
        exact h2 h3
      simp [A_seq] at h1
      have : v_seq m ≠ v_seq n := h1.1
      contradiction
    have h_infinite : s.Infinite := by
      have h_bij : s = v_seq '' {n | colors_seq n = i} := by
        ext x
        simp [s]
      rw [h_bij]
      apply Set.infinite_image_of_injOn
      · intro x _ y _ hxy
        exact h_inj hxy
      · exact hi_inf
    exact h_infinite
  · -- 证明单色性
    intro x hx y hy hxy
    simp [s] at hx hy
    rcases hx with ⟨n, hn, rfl⟩
    rcases hy with ⟨m, hm, rfl⟩
    wlog hnm : n < m
    · have : m < n := by
        by_contra h'
        push_neg at h'
        have : m = n := by linarith
        contradiction
      rw [h_symm]
      apply this
    -- n < m
    have h1 : v_seq m ∈ A_seq (n+1) := by
      have h2 : A_seq m ⊆ A_seq (n+1) := hA_mono (n+1) m (by linarith)
      have h3 : v_seq m ∈ A_seq m := hv_in m
      exact h2 h3
    simp [A_seq] at h1
    have : c (v_seq n) (v_seq m) = colors_seq n := h1.2.2
    rw [this]
    exact hn

end RamseyTheory
