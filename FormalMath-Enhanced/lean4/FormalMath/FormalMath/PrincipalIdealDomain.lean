/-
# 主理想整环性质

## 数学背景

主理想整环（PID）是每个理想都是主理想的整环。
即对于任何理想I，存在a使得I = (a)。

## 重要性质
1. PID是Noether环
2. PID是唯一分解整环（UFD）
3. PID中不可约元 = 素元
4. Bezout等式成立

## 例子
- ℤ（整数环）
- F[x]（域上多项式环）

## Mathlib4对应
- `Mathlib.RingTheory.PrincipalIdealDomain`
- `Mathlib.RingTheory.UniqueFactorizationDomain`

-/

import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.UniqueFactorizationDomain
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Noetherian
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.RingTheory.Ideal.Quotient

namespace PrincipalIdealDomain

open Ideal Polynomial Classical

variable {R : Type*} [CommRing R] [IsPrincipalIdealRing R] [IsDomain R]

/-
## PID的基本定义

在PID中，每个理想都是主理想。
-/
theorem ideal_is_principal (I : Ideal R) : I.IsPrincipal := by
  -- 直接应用IsPrincipalIdealRing的定义
  apply IsPrincipalIdealRing.principal

/-
## 生成元的唯一性（差一个单位）

若(a) = (b)，则存在单位u使得a = ub

**证明思路**：
1. (a) = (b)意味着a∈(b)且b∈(a)
2. 所以存在c,d使得a = cb且b = da
3. 因此a = cda，即a(1-cd) = 0
4. 若a≠0，则cd = 1，所以c是单位
-/
theorem generator_unique_unit 
    {a b : R} (h : span ({a} : Set R) = span ({b} : Set R)) :
    ∃ u : Rˣ, a = u * b := by
  -- (a) = (b)意味着a|b且b|a
  rw [span_singleton_eq_span_singleton] at h
  -- 使用Mathlib的associated_iff中的结果
  obtain ⟨u, rfl⟩ := h
  -- a = u * b 对某个单位u
  exact ⟨u, rfl⟩

/-
## PID是Noether环

**定理**：主理想整环满足理想的升链条件（ACC）。

**证明**：
升链I₁ ⊆ I₂ ⊆ ...对应生成元a₁, a₂, ...
其中a_{i+1} | a_i
由于整除链必须终止，理想链也终止。

更直接的证明：每个理想由单个元素生成，自然是有限生成的。
-/
theorem pid_is_noetherian : IsNoetherianRing R := by
  -- PID的每个理想都是主理想，即由单个元素生成
  -- 因此所有理想都是有限生成的
  apply isNoetherianRing_iff'.mpr
  intro I hI
  -- PID的每个理想都是有限生成的（实际上由单个元素生成）
  obtain ⟨a, ha⟩ := ideal_is_principal I
  use {a}
  simp [ha]

/-
## PID中不可约元是素元

**定理**：在PID中，若p不可约，则p是素元。

**证明关键**：(p)是极大理想 ⇒ (p)是素理想

**详细证明**：
1. 设p不可约，考虑理想(p)
2. 若(p) ⊆ (a)，则a|p
3. 由于p不可约，a是单位或与p相伴
4. 所以(p) = (a)或(a) = R
5. 因此(p)是极大理想
6. 极大理想是素理想
7. (p)是素理想意味着p是素元
-/
theorem irreducible_is_prime 
    {p : R} (h_irr : Irreducible p) : Prime p := by
  -- 在PID中，不可约元生成极大理想
  -- 极大理想是素理想
  -- 素理想对应素元
  have h_prime : Prime p := by
    -- 使用Mathlib中已有的定理：PID中的不可约元是素元
    apply irreducible_iff_prime.mp
    exact h_irr
  exact h_prime

/-
## PID是UFD

**定理**：主理想整环是唯一分解整环。

**证明要点**：
1. Noether性质保证分解存在（不能有无限严格下降的整除链）
2. 不可约元是素元保证分解唯一

**详细证明**：
- 存在性：考虑a的非单位因子链，由于Noether性质必须终止
- 唯一性：利用不可约元是素元的性质，通过标准证明
-/
instance pid_is_ufd : UniqueFactorizationMonoid R := by
  -- PID自动继承UFD结构
  -- 这是Mathlib中已有的实例
  infer_instance

/-
## Bezout等式

**定理**：在PID中，对于任意a,b，存在x,y使得：
gcd(a,b) = ax + by

**证明**：理想(a,b) = (d)，其中d = gcd(a,b)
由于d∈(a,b)，所以存在x,y使得d = ax + by。
-/
theorem bezout_identity 
    (a b : R) :
    ∃ x y : R, gcd a b = a * x + b * y := by
  -- 考虑理想I = (a, b)
  let I := span ({a, b} : Set R)
  -- I是主理想，设I = (d)
  obtain ⟨d, hd⟩ := ideal_is_principal I
  -- 证明d与gcd(a,b)相伴
  have h_gcd : Associated d (gcd a b) := by
    -- d∈(a,b)，所以d = ra + sb对某个r,s
    have h_mem : d ∈ I := by
      rw [hd]
      exact Ideal.mem_span_singleton_self d
    rw [Ideal.mem_span_insert, Ideal.mem_span_singleton] at h_mem
    rcases h_mem with ⟨r, s, hrs⟩
    -- d整除a和b
    have hda : d ∣ a := by
      rw [hd]
      apply Ideal.mem_span_singleton.mpr
      exact Ideal.subset_span (by simp)
    have hdb : d ∣ b := by
      rw [hd]
      apply Ideal.mem_span_singleton.mpr
      exact Ideal.subset_span (by simp)
    -- d是a和b的公因子
    -- gcd是最大公因子，所以d|gcd(a,b)
    have hdg : d ∣ gcd a b := by
      apply dvd_gcd hda hdb
    -- 反之，gcd|a和gcd|b，所以gcd∈(a,b)=(d)，故gcd|d
    have hgd : gcd a b ∣ d := by
      have hgda : gcd a b ∣ a := gcd_dvd_left a b
      have hgdb : gcd a b ∣ b := gcd_dvd_right a b
      have hg_mem : gcd a b ∈ I := by
        rw [Ideal.mem_span_insert, Ideal.mem_span_singleton]
        -- 使用gcd_dvd_left和gcd_dvd_right
        obtain ⟨ra, hra⟩ := hgda
        obtain ⟨rb, hrb⟩ := hgdb
        -- 需要更精细的论证
        sorry
      rw [hd] at hg_mem
      exact Ideal.mem_span_singleton.mp hg_mem
    -- d|gcd且gcd|d，所以d与gcd相伴
    exact ⟨hdg, hgd⟩
  -- 使用相伴关系转换等式
  sorry

/-
## 理想的包含与整除

**定理**：在PID中，(a) ⊆ (b) 当且仅当 b | a

这是PID中最基本的对应关系。

**证明**：
- (a) ⊆ (b) ⇔ a ∈ (b) ⇔ ∃c, a = cb ⇔ b | a
-/
theorem ideal_subset_iff_dvd 
    (a b : R) : span ({a} : Set R) ≤ span ({b} : Set R) ↔ b ∣ a := by
  constructor
  · -- (a) ⊆ (b) ⇒ b | a
    intro h
    have ha : a ∈ span ({a} : Set R) := by
      apply Ideal.subset_span
      simp
    have hb : a ∈ span ({b} : Set R) := h ha
    rw [Ideal.mem_span_singleton] at hb
    exact hb
  
  · -- b | a ⇒ (a) ⊆ (b)
    rintro ⟨c, hc⟩
    rw [hc]
    rintro x hx
    rw [Ideal.mem_span_singleton] at hx ⊢
    rcases hx with ⟨d, rfl⟩
    use d * c
    ring

/-
## PID中素理想与不可约元

**定理**：非零素理想恰好由素元生成
-/
theorem prime_ideal_iff_prime_generator 
    (I : Ideal R) (hI : I ≠ ⊥) :
    I.IsPrime ↔ ∃ p : R, Prime p ∧ I = span ({p} : Set R) := by
  constructor
  · -- 素理想 ⇒ 由素元生成
    intro h_prime
    -- PID中每个理想都是主理想
    obtain ⟨p, hp⟩ := ideal_is_principal I
    use p
    constructor
    · -- 证明p是素元
      have h_ne : p ≠ 0 := by
        by_contra hp0
        rw [hp0] at hp
        simp at hp
        rw [hp] at h_prime
        contradiction
      -- 素理想生成素元（在非零情况下）
      have : Prime p := by
        -- 使用素理想对应素元的性质
        sorry
      exact this
    · exact hp
  
  · -- 由素元生成 ⇒ 素理想
    rintro ⟨p, hp_prime, hp_eq⟩
    rw [hp_eq]
    -- 素元生成素理想
    sorry

/-
## 中国剩余定理（PID版本）

**定理**：若a,b互素，则R/(ab) ≅ R/(a) × R/(b)

**证明要点**：
- 理想(a)和(b)互素当且仅当gcd(a,b)=1
- 应用一般的中国剩余定理
-/
theorem chinese_remainder_pid 
    (a b : R) (hcoprime : IsCoprime a b) :
    R ⧸ span ({a * b} : Set R) ≃+* 
    (R ⧸ span ({a} : Set R)) × (R ⧸ span ({b} : Set R)) := by
  -- 中国剩余定理：若I,J互素，则R/(I∩J) ≅ R/I × R/J
  -- 对于主理想，(a)∩(b) = (lcm(a,b))
  -- 当a,b互素时，lcm(a,b) = ab
  have h_inter : span ({a * b} : Set R) = span ({a} : Set R) ⊓ span ({b} : Set R) := by
    -- 证明(a*b) = (a) ∩ (b) 当a,b互素
    sorry
  rw [h_inter]
  -- 应用一般的中国剩余定理
  apply Ideal.quotientInfRingEquivPiQuotient
  · -- 证明理想互素
    rw [Ideal.isCoprime_iff_add]
    exact hcoprime

/-
## 欧几里得整环是PID

**定理**：每个欧几里得整环都是主理想整环。

**证明**：对于理想I，取次数最小的非零元作为生成元。

**详细证明**：
1. 设I是非零理想
2. 取a∈I\{0}使得δ(a)最小（δ是欧几里得函数）
3. 对任意b∈I，做带余除法：b = qa + r，其中r=0或δ(r)<δ(a)
4. 由于r = b - qa ∈ I，由δ(a)的最小性，r = 0
5. 因此b = qa ∈ (a)，所以I = (a)
-/
instance EuclideanDomain.toPrincipalIdealDomain 
    (E : Type*) [EuclideanDomain E] : IsPrincipalIdealRing E := by
  -- 欧几里得整环是PID
  -- 这是Mathlib中已有的实例
  infer_instance

end PrincipalIdealDomain
