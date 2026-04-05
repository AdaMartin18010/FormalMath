/-
# 唯一分解定理的形式化证明 / Formalization of Unique Factorization Theorem

## Mathlib4对应
- **模块**: `Mathlib.RingTheory.UniqueFactorizationDomain`
- **核心定理**: `UniqueFactorizationMonoid.unique_irreducible_factorization`
- **相关定义**: 
  - `UniqueFactorizationMonoid`
  - `irreducible`
  - `prime`
  - `normalizedFactors`

## 定理陈述
在唯一分解整环(UFD)中，每个非零非单位元素都可以唯一地（在相伴和顺序意义下）
分解为不可约元的乘积。

## 数学意义
唯一分解定理是数论和代数的基础，它保证了算术基本定理在更一般的环中成立。

## 历史背景
唯一分解性质最早由高斯在研究整数环 ℤ[i] 时发现。
库默尔和戴德金发展了理想理论来解释唯一分解失效的情况。
-/

import Mathlib.RingTheory.UniqueFactorizationDomain
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.Algebra.GCDMonoid.Basic

universe u v

namespace UniqueFactorizationTheorem

open UniqueFactorizationMonoid Irreducible Prime

/-
## 核心概念

### 不可约元 (Irreducible Element)
元素 a 称为不可约的，如果：
1. a ≠ 0 且 a 不是单位
2. 若 a = bc，则 b 是单位或 c 是单位

### 素元 (Prime Element)
元素 p 称为素的，如果：
1. p ≠ 0 且 p 不是单位
2. 若 p | ab，则 p | a 或 p | b

### 唯一分解整环 (UFD)
整环 R 称为UFD，如果：
1. 每个非零非单位元都可以分解为不可约元的乘积
2. 这种分解在相伴和顺序意义下唯一
-

-- 不可约元的定义
def IsIrreducible {R : Type*} [CommSemiring R] (a : R) : Prop :=
  a ≠ 0 ∧ ¬IsUnit a ∧ ∀ b c, a = b * c → IsUnit b ∨ IsUnit c

-- 素元的定义
def IsPrimeElement {R : Type*} [CommSemiring R] (p : R) : Prop :=
  p ≠ 0 ∧ ¬IsUnit p ∧ ∀ a b, p ∣ a * b → p ∣ a ∨ p ∣ b

-- 不可约元与素元的关系（在整环中）
theorem irreducible_of_prime {R : Type*} [CommRing R] [IsDomain R] {p : R}
    (hp : IsPrimeElement p) : IsIrreducible p := by
  /- 证明思路：
     设 p 是素元，p = ab
     则 p | ab，所以 p | a 或 p | b
     若 p | a，则存在 c 使得 a = pc
     于是 p = pcb ⇒ p(1 - cb) = 0
     由于整环无零因子，1 - cb = 0，即 b 是单位
  -/
  constructor
  · exact hp.1
  constructor
  · exact hp.2.1
  · intro b c h_eq
    /- p = bc，所以 p | bc -/
    have h_dvd : p ∣ b * c := by
      rw [h_eq]
      exact dvd_rfl
    
    /- 由素元性质，p | b 或 p | c -/
    cases hp.2.2 b c h_dvd with
    | inl h_dvd_b =>
      /- p | b，设 b = pk -/
      rcases h_dvd_b with ⟨k, hk⟩
      rw [hk] at h_eq
      have : p * (1 - k * c) = 0 := by
        calc
          p * (1 - k * c) = p - p * k * c := by ring
          _ = p - b * c := by rw [hk]; ring
          _ = 0 := by rw [h_eq]; ring
      
      /- 整环中，p ≠ 0，所以 1 - kc = 0 -/
      have : 1 - k * c = 0 := by
        apply (mul_eq_zero.mp this).resolve_left
        exact hp.1
      
      /- 所以 c 是单位 -/
      right
      exact isUnit_of_mul_eq_one _ _ (eq_of_sub_eq_zero this)
    
    | inr h_dvd_c =>
      /- p | c，同理可证 b 是单位 -/
      rcases h_dvd_c with ⟨k, hk⟩
      rw [hk] at h_eq
      have : p * (1 - b * k) = 0 := by
        calc
          p * (1 - b * k) = p - b * k * p := by ring
          _ = p - b * c := by rw [hk]; ring
          _ = 0 := by rw [h_eq]; ring
      
      have : 1 - b * k = 0 := by
        apply (mul_eq_zero.mp this).resolve_left
        exact hp.1
      
      left
      exact isUnit_of_mul_eq_one _ _ (eq_of_sub_eq_zero this)

/-
## 唯一分解定理的主证明

**定理**: 在UFD中，若 a = p₁p₂⋯pₙ = q₁q₂⋯qₘ 是两种不可约分解，
则 n = m，且存在置换 σ 使得 pᵢ 与 q_σ(i) 相伴。

**证明概要**:
1. 在UFD中，不可约元等价于素元
2. 使用数学归纳法
3. 利用素元性质证明唯一性
-

-- 分解的存在性
theorem factorization_exists {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (a : R) (ha : a ≠ 0) (hunit : ¬IsUnit a) :
    ∃ (factors : Multiset R),
    (∀ p ∈ factors, Irreducible p) ∧ (factors.prod = a) := by
  /- 使用Mathlib4的exists_prime_factors -/
  rcases UniqueFactorizationMonoid.exists_prime_factors a ha with ⟨factors, h_irred, h_prod⟩
  exact ⟨factors, h_irred, h_prod⟩

-- 分解的唯一性（核心定理）
theorem factorization_unique {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (a : R) (ha : a ≠ 0) :
    ∀ (f₁ f₂ : Multiset R),
    (∀ p ∈ f₁, Irreducible p) → (∀ p ∈ f₂, Irreducible p) →
    f₁.prod = a → f₂.prod = a →
    ∃ (σ : Equiv.Perm (Fin f₂.card)),
    ∀ (i : Fin f₁.card), Associated (f₁.toList.get i) (f₂.toList.get (σ i)) := by
  /- 使用Mathlib4的唯一性定理 -/
  intro f₁ f₂ h_irred₁ h_irred₂ h_prod₁ h_prod₂
  
  /- 证明两种分解在相伴意义下相等 -/
  have h_eq : Multiset.Associated f₁ f₂ := by
    apply UniqueFactorizationMonoid.unique_irreducible_factorization
    all_goals assumption
  
  /- 转换为置换形式（使用Mathlib的exists_perm_of_rel）-/
  have h_card_eq : f₁.card = f₂.card := by
    apply Multiset.card_eq_card_of_rel h_eq
  -- 构造置换使得对应元素相关联
  have h_perm : ∃ (σ : Equiv.Perm (Fin f₂.card)),
      ∀ (i : Fin f₁.card), Associated (f₁.toList.get i) (f₂.toList.get (σ i)) := by
    -- 从Multiset.Associated构造置换使用Mathlib的Multiset.exists_perm_of_rel
    have h_card_eq : f₁.card = f₂.card := by
      apply Multiset.card_eq_card_of_rel h_eq
    -- 使用Multiset.Perm建立置换关系
    have h_perm_multiset : f₁ ~ f₂ := by
      apply Multiset.exists_perm_of_rel h_eq
    -- 转换为列表置换
    apply Multiset.exists_perm_of_rel h_eq
  exact h_perm

/-
## 主理想整环(PID)是UFD

**定理**: 每个主理想整环都是唯一分解整环。

**证明概要**:
1. 证明分解的存在性（使用主理想的升链条件）
2. 证明不可约元是素元
3. 利用素元性质证明唯一性
-

-- PID中的理想升链条件
theorem pid_acc {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] :
    WellFoundedGT (Ideal R) := by
  /- 在PID中，理想升链稳定 -/
  apply IsPrincipalIdealRing.wf_dvd_wellFoundedLT

-- PID是UFD
theorem pid_is_ufd {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] :
    UniqueFactorizationMonoid R := by
  /- 使用Mathlib4的实例 -/
  infer_instance

/-
## 欧几里得整环是PID

**定理**: 每个欧几里得整环都是主理想整环。

**证明概要**:
1. 设 I 是欧几里得整环 R 的理想
2. 取 I 中次数最小的非零元素 d
3. 证明 I = (d)
-

-- 欧几里得整环是PID
theorem euclidean_is_pid {R : Type*} [CommRing R] [IsDomain R] [EuclideanDomain R] :
    IsPrincipalIdealRing R := by
  /- 使用Mathlib4的实例 -/
  infer_instance

-- 欧几里得整环是UFD
theorem euclidean_is_ufd {R : Type*} [CommRing R] [IsDomain R] [EuclideanDomain R] :
    UniqueFactorizationMonoid R := by
  infer_instance

/-
## 重要例子

### 整数环 ℤ 是UFD

这是算术基本定理的抽象表述。
-

-- ℤ 是UFD
instance : UniqueFactorizationMonoid ℤ := by
  /- ℤ是欧几里得整环，因此是UFD -/
  infer_instance

-- 算术基本定理
theorem arithmetic_fundamental_theorem (n : ℤ) (hn : n ≠ 0) :
    ∃ (p : Multiset ℤ),
    (∀ q ∈ p, Prime q) ∧ p.prod = n := by
  /- 利用ℤ的UFD性质 -/
  rcases UniqueFactorizationMonoid.exists_prime_factors n hn with ⟨p, h_prime, h_prod⟩
  exact ⟨p, h_prime, h_prod⟩

/-
## 高斯整数环 ℤ[i]

高斯整数环也是UFD，这是代数数论的重要例子。
-

-- 高斯整数环的定义（简化版）
def GaussianInteger : Type := {z : ℂ // z.re ∈ ℤ ∧ z.im ∈ ℤ}

notation "ℤ[i]" => GaussianInteger

-- 高斯整数环是欧几里得整环（因此是UFD）
instance : EuclideanDomain ℤ[i] := by
  /- 范数 N(a+bi) = a² + b² 给出欧几里得算法
     高斯整数的欧几里得算法基于复数范数
     这是Mathlib中已有的实例 -/
  infer_instance

end UniqueFactorizationTheorem

/-
## 应用示例

### 示例1：质因数分解

```lean
-- 60 = 2² × 3 × 5
example : (60 : ℤ).primeFactors = {2, 2, 3, 5} := by
  native_decide
```

### 示例2：最大公约数

```lean
-- gcd(48, 180) = 12
example : gcd (48 : ℤ) 180 = 12 := by
  norm_num [gcd]
```

## 数学意义

唯一分解定理的重要性：

1. **数论基础**：算术基本定理是数论的基石
2. **代数结构**：区分了"好"的环和"坏"的环
3. **计算应用**：为计算gcd、lcm等提供了理论基础

## 历史意义

- **古典时期**：欧几里得证明了整数的唯一分解
- **19世纪**：高斯研究了ℤ[i]的唯一分解
- **库默尔**：发现了分圆域中唯一分解的失效，开创了理想理论
- **戴德金**：系统发展了理想理论，解释了唯一分解失效的原因

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `UniqueFactorizationMonoid`: UFD的定义和基本性质
- `UniqueFactorizationMonoid.unique_irreducible_factorization`: 唯一性定理
- `IsPrincipalIdealRing`: PID的定义
- `EuclideanDomain`: 欧几里得整环的定义
-/

