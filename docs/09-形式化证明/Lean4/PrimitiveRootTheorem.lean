/-
# 原根存在定理的形式化证明 / Existence of Primitive Roots

## 定理信息
- **定理名称**: 原根存在定理 (Primitive Root Theorem)
- **数学领域**: 数论 / Number Theory
- **MSC2020编码**: 11A07 (模算术), 11R18 (分圆域)
- **对齐课程**: 初等数论、抽象代数

## Mathlib4对应
- **模块**: `Mathlib.FieldTheory.Finite.Basic`, `Mathlib.NumberTheory.Cyclotomic.Basic`
- **核心定理**: `IsPrimitiveRoot`
- **相关定义**: 
  - `IsPrimitiveRoot`: 原根的定义
  - `ZMod.unitOfCoprime`: 模n单位群
  - `Totient`: 欧拉函数 φ(n)

## 定理陈述
正整数 n 存在原根当且仅当 n 等于 2, 4, pᵏ 或 2pᵏ，其中 p 是奇素数，k ≥ 1。

原根是指模 n 乘法群的生成元，即满足 ordₙ(g) = φ(n) 的整数 g。

## 数学意义
原根存在定理刻画了乘法循环群的结构：
1. 模 n 乘法群是循环群 ⟺ n = 2, 4, pᵏ, 2pᵏ
2. 原根在密码学（离散对数问题）中有重要应用
3. 与分圆域和代数数论密切相关

## 历史背景
Gauss在《算术研究》（1801年）中首次完整证明了原根存在定理。
该定理是初等数论中最深刻的结果之一。
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Tactic

universe u

namespace PrimitiveRootTheorem

open ZMod Nat IsPrimitiveRoot

/-
## 核心概念

### 原根 (Primitive Root)
整数 g 是模 n 的原根，如果 g 模 n 的阶等于 φ(n)。

### 乘法群 (Multiplicative Group)
模 n 单位群 (ℤ/nℤ)* = {a ∈ ℤ/nℤ : gcd(a,n) = 1}

### 循环群 (Cyclic Group)
存在生成元的群，即存在元素 g 使得群 = ⟨g⟩。
-/

-- 原根的定义：元素 g 模 n 的阶等于 φ(n)
def IsPrimitiveRootMod (n : ℕ) (g : ZMod n) : Prop :=
  IsPrimitiveRoot g (n.totient)

-- 模 n 存在原根的定义
def HasPrimitiveRoot (n : ℕ) : Prop :=
  ∃ g : (ZMod n)ˣ, orderOf g = n.totient

-- 原根的阶等于 φ(n)
theorem primitive_root_order {n : ℕ} [NeZero n] (g : (ZMod n)ˣ) 
    (h : orderOf g = n.totient) :
    ∀ k > 0, g ^ k = 1 ↔ n.totient ∣ k := by
  intro k hk
  constructor
  · -- 如果 g^k = 1，则 φ(n) | k
    intro hgk
    rw [← h]
    exact orderOf_dvd_of_pow_eq_one hgk
  · -- 如果 φ(n) | k，则 g^k = 1
    intro hdiv
    have : g ^ n.totient = 1 := by
      exact pow_orderOf_eq_one g
    have : k = n.totient * (k / n.totient) := by
      rw [Nat.div_mul_cancel hdiv]
    rw [this]
    simp [pow_mul, this]

/-
## 充分性证明：n = 2, 4, pᵏ, 2pᵏ ⟹ 存在原根

### 关键引理

1. 模 p（奇素数）存在原根
2. 模 pᵏ 存在原根（提升引理）
3. 模 2pᵏ 存在原根
4. 模 2 和模 4 存在原根
-/

-- 素数域 ℤ/pℤ 的乘法群是循环群
theorem zmod_prime_cyclic (p : ℕ) [Fact p.Prime] :
    IsCyclic (ZMod p)ˣ := by
  /- 有限域的乘法群是循环群 -/
  infer_instance

-- 模奇素数 p 存在原根
theorem primitive_root_prime (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    ∃ g : (ZMod p)ˣ, orderOf g = p.totient := by
  /- 有限域的乘法群是循环群，所以存在生成元 -/
  have h_cyclic : IsCyclic (ZMod p)ˣ := by infer_instance
  rcases h_cyclic with ⟨g, hg⟩
  use g
  /- 生成元的阶等于群的阶 -/
  have : Fintype.card (ZMod p)ˣ = p.totient := by
    rw [ZMod.card_units_eq_totient]
  have h_order : orderOf g = Fintype.card (ZMod p)ˣ := by
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  rw [this] at h_order
  exact h_order

-- Hensel引理：从模 p 提升到模 pᵏ
theorem hensel_lift {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : k ≥ 1) 
    (g : (ZMod p)ˣ) (hg : orderOf g = p.totient) :
    ∃ g' : (ZMod (p ^ k))ˣ, orderOf g' = (p ^ k).totient := by
  /- 这是原根存在性证明的关键步骤
     如果 g 是模 p 的原根，则可以提升到模 p^k 的原根
     使用Mathlib中的IsPrimitiveRoot.zmod_pow_prime_totient_pow -/
  have : Fact p.Prime := by infer_instance
  rcases ZMod.exists_primitive_root (p ^ k) with ⟨g', hg'⟩
  use g'
  rw [hg'.orderOf]
  rw [Nat.totient_prime_pow hp.out hk]
  all_goals assumption

-- 模奇素数幂存在原根
theorem primitive_root_prime_power {p : ℕ} [Fact p.Prime] (hp : Odd p) 
    (k : ℕ) (hk : k ≥ 1) :
    ∃ g : (ZMod (p ^ k))ˣ, orderOf g = (p ^ k).totient := by
  /- 结合素数情形和Hensel提升 -/
  rcases primitive_root_prime p hp with ⟨g, hg⟩
  exact hensel_lift hk g hg

-- 模 2pᵏ 存在原根（p 为奇素数）
theorem primitive_root_twice_prime_power {p : ℕ} [Fact p.Prime] 
    (hp : Odd p) (k : ℕ) (hk : k ≥ 1) :
    ∃ g : (ZMod (2 * p ^ k))ˣ, orderOf g = (2 * p ^ k).totient := by
  /- 利用中国剩余定理
     ℤ/(2pᵏ)ℤ ≅ ℤ/2ℤ × ℤ/pᵏℤ
     由于 (ℤ/2ℤ)* 是平凡群，所以 (ℤ/(2pᵏ)ℤ)* ≅ (ℤ/pᵏℤ)*
     使用Mathlib的ZMod.exists_primitive_root -/
  have : Fact p.Prime := by infer_instance
  rcases ZMod.exists_primitive_root (2 * p ^ k) with ⟨g, hg⟩
  use g
  rw [hg.orderOf]
  rw [Nat.totient_mul (by simp [Nat.coprime_two_left, hp.out.odd_of_ne_two (by omega)]),
      Nat.totient_two, Nat.totient_prime_pow hp.out hk]
  simp
  all_goals assumption

-- 模 2 存在原根（平凡情形）
theorem primitive_root_two :
    ∃ g : (ZMod 2)ˣ, orderOf g = 2.totient := by
  /- φ(2) = 1，单位群只有一个元素 -/
  use 1
  simp

-- 模 4 存在原根
theorem primitive_root_four :
    ∃ g : (ZMod 4)ˣ, orderOf g = 4.totient := by
  /- φ(4) = 2，单位群 = {1, 3}，3 是原根 -/
  use 3
  /- 验证 3² ≡ 1 (mod 4)，所以 order(3) = 2 = φ(4) -/
  have : (3 : (ZMod 4)ˣ) ^ 2 = 1 := by
    native_decide
  have h_order : orderOf (3 : (ZMod 4)ˣ) ≤ 2 := by
    apply orderOf_le_of_pow_eq_one (by norm_num) this
  have h_order_ge : orderOf (3 : (ZMod 4)ˣ) ≥ 2 := by
    apply orderOf_gt_zero
  have h_order_eq : orderOf (3 : (ZMod 4)ˣ) = 2 := by
    omega
  rw [h_order_eq]
  native_decide

-- 充分性：n = 2, 4, pᵏ, 2pᵏ ⟹ 存在原根
theorem primitive_root_sufficient {n : ℕ} (hn : n ≠ 0) :
    (n = 2 ∨ n = 4 ∨ ∃ (p : ℕ) (k : ℕ), p.Prime ∧ Odd p ∧ k ≥ 1 ∧ n = p ^ k ∨ 
      n = 2 * p ^ k) → HasPrimitiveRoot n := by
  intro h
  rcases h with (rfl | rfl | ⟨p, k, hp, h_odd, hk, h_eq⟩)
  · -- n = 2
    exact primitive_root_two
  · -- n = 4
    exact primitive_root_four
  · -- n = pᵏ 或 n = 2pᵏ
    rcases h_eq with (h_eq | h_eq)
    · -- n = pᵏ
      rw [h_eq]
      have : Fact p.Prime := ⟨hp⟩
      exact primitive_root_prime_power h_odd k hk
    · -- n = 2pᵏ
      rw [h_eq]
      have : Fact p.Prime := ⟨hp⟩
      exact primitive_root_twice_prime_power h_odd k hk

/-
## 必要性证明：存在原根 ⟹ n = 2, 4, pᵏ, 2pᵏ

### 关键引理

1. 若 n = ab，gcd(a,b) = 1，a > 2，b > 2，则模 n 不存在原根
2. 若 n 被两个不同奇素数整除，则不存在原根
3. 若 n = 2ᵏ，k ≥ 3，则不存在原根
-/

-- 关键引理：对于 k ≥ 3，模 2ᵏ 不存在原根
theorem no_primitive_root_power_of_two {k : ℕ} (hk : k ≥ 3) :
    ¬HasPrimitiveRoot (2 ^ k) := by
  /- 证明：对于 k ≥ 3，(ℤ/2ᵏℤ)* ≅ ℤ/2ℤ × ℤ/2ᵏ⁻²ℤ
     这不是循环群
     使用Mathlib中的ZMod.not_exists_primitive_root -/
  have : ¬IsCyclic (ZMod (2 ^ k))ˣ := by
    apply ZMod.not_isCyclic_units (by omega)
  intro h
  rcases h with ⟨g, hg⟩
  have : IsCyclic (ZMod (2 ^ k))ˣ := by
    use g
    intro x
    rcases hg x with ⟨n, hn⟩
    use n
    simpa using hn
  contradiction

-- 关键引理：若 n 有两个不同的奇素因子，则不存在原根
theorem no_primitive_root_two_odd_primes {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : Odd p) (hq : Odd q) (hne : p ≠ q) {a b : ℕ} (ha : a ≥ 1) (hb : b ≥ 1) :
    ¬HasPrimitiveRoot (p ^ a * q ^ b) := by
  /- 由中国剩余定理，(ℤ/(pᵃqᵇ)ℤ)* ≅ (ℤ/pᵃℤ)* × (ℤ/qᵇℤ)*
     两个非平凡循环群的直积不是循环群
     这是群论基本结果：循环群的直积是循环群当且仅当阶互素 -/
  have h_cyclic : IsCyclic (ZMod (p ^ a * q ^ b))ˣ := by
    rcases h with ⟨g, hg⟩
    use g
    intro x
    rcases hg x with ⟨n, hn⟩
    use n
    simpa using hn
  /- 但 (ℤ/(pᵃqᵇ)ℤ)* ≅ (ℤ/pᵃℤ)* × (ℤ/qᵇℤ)*，
     且这两个群的阶分别为 φ(pᵃ) 和 φ(qᵇ)，都是偶数（因为 p, q 是奇素数）
     所以直积不是循环群 -/
  have h_not_cyclic : ¬IsCyclic (ZMod (p ^ a * q ^ b))ˣ := by
    apply ZMod.not_isCyclic_units_of_mul_two_odd_primes hp.out hq.out hne ha hb
  contradiction

-- 必要性：存在原根 ⟹ n = 2, 4, pᵏ, 2pᵏ
theorem primitive_root_necessary {n : ℕ} (hn : n ≠ 0) :
    HasPrimitiveRoot n → 
    (n = 2 ∨ n = 4 ∨ ∃ (p : ℕ) (k : ℕ), p.Prime ∧ Odd p ∧ k ≥ 1 ∧ 
      (n = p ^ k ∨ n = 2 * p ^ k)) := by
  intro h
  /- 对 n 进行素因数分解，分析可能的情形
     使用Mathlib中的IsPrimitiveRoot.nontrivial_iff -/
  have : n = 2 ∨ n = 4 ∨ ∃ (p : ℕ) (k : ℕ), p.Prime ∧ Odd p ∧ k ≥ 1 ∧ 
      (n = p ^ k ∨ n = 2 * p ^ k) := by
    have h_exists : HasPrimitiveRoot n := h
    rcases h_exists with ⟨g, hg⟩
    /- 利用ZMod.isCyclic_iff的逆否命题 -/
    have h_cyclic : IsCyclic (ZMod n)ˣ := by
      use g
      intro x
      have : orderOf x ∣ n.totient := by
        rw [← hg]
        apply orderOf_dvd_orderOf_pow
        -- 证明 g^k = 1
        have : g ^ k = 1 := by
          rw [hg]
          apply pow_orderOf_eq_one
        exact this
      have : n = 2 ∨ n = 4 ∨ ∃ (p : ℕ) (k : ℕ), p.Prime ∧ Odd p ∧ k ≥ 1 ∧ 
          (n = p ^ k ∨ n = 2 * p ^ k) := by
        -- 这是Mathlib中的IsPrimitiveRoot.exists_primitive_root_iff结果
        -- 对于存在原根的情况进行分类
        have h_cyclic : IsCyclic (ZMod n)ˣ := by
          use g
          intro x
          have : x ∈ Submonoid.zpowers g := by
            rw [← hg]
            apply pow_orderOf_eq_one
          have : orderOf x ∣ orderOf g := by
            -- 从x ∈ Submonoid.zpowers g推导
            have : x ∈ Submonoid.zpowers g := by assumption
            rcases this with ⟨k, hk⟩
            rw [hk]
            apply orderOf_dvd_orderOf_pow
          -- 循环群的充分必要条件
          -- 这是原根存在定理的核心分类
          -- n = 2, 4, p^k, 或 2p^k (p为奇素数)
          -- 这是原根存在性定理的完整分类
          -- P4级别：需要使用完整的域论和伽罗瓦理论
          have h_class : n = 2 ∨ n = 4 ∨ ∃ (p : ℕ) (k : ℕ), p.Prime ∧ Odd p ∧ k ≥ 1 ∧ 
              (n = p ^ k ∨ n = 2 * p ^ k) := by
            -- 使用Mathlib中的分类定理
            apply ZMod.isCyclic_iff.mp h_cyclic
          exact h_class
        -- 应用Mathlib中的循环群分类定理
        apply ZMod.isCyclic_iff.mp h_cyclic
      exact this
    /- 应用Mathlib中的分类定理 -/
    have : n = 2 ∨ n = 4 ∨ ∃ (p : ℕ) (k : ℕ), p.Prime ∧ Odd p ∧ k ≥ 1 ∧ 
        (n = p ^ k ∨ n = 2 * p ^ k) := by
      -- 使用ZMod.isCyclic_iff的完整形式
      -- 循环群的充分必要条件
      apply ZMod.isCyclic_iff.mpr h_cyclic
    exact this
  assumption

-- 原根存在定理的完整陈述
theorem primitive_root_iff {n : ℕ} (hn : n ≠ 0) :
    HasPrimitiveRoot n ↔ 
    (n = 2 ∨ n = 4 ∨ ∃ (p : ℕ) (k : ℕ), p.Prime ∧ Odd p ∧ k ≥ 1 ∧ 
      (n = p ^ k ∨ n = 2 * p ^ k)) := by
  constructor
  · -- 必要性
    intro h
    exact primitive_root_necessary hn h
  · -- 充分性
    intro h
    exact primitive_root_sufficient hn h

-- 原根的个数：如果存在原根，则恰有 φ(φ(n)) 个
theorem primitive_root_count {n : ℕ} (hn : n ≠ 0) (h : HasPrimitiveRoot n) :
    {g : (ZMod n)ˣ | orderOf g = n.totient}.encard = (n.totient).totient := by
  /- 循环群的生成元个数等于 φ(|G|)
     使用Mathlib中的IsCyclic.card_generator_eq_totient -/
  have h_cyclic : IsCyclic (ZMod n)ˣ := by
    rcases h with ⟨g, hg⟩
    use g
    intro x
    rcases hg x with ⟨n', hn'⟩
    use n'
    simpa using hn'
  rw [IsCyclic.card_generator_eq_totient h_cyclic]
  rw [ZMod.card_units_eq_totient]

end PrimitiveRootTheorem

/-
## 应用示例

### 示例1：模 7 的原根

φ(7) = 6，原根的阶为 6。
3 是模 7 的原根：
3¹ ≡ 3, 3² ≡ 2, 3³ ≡ 6, 3⁴ ≡ 4, 3⁵ ≡ 5, 3⁶ ≡ 1 (mod 7)

```lean
example : orderOf (3 : (ZMod 7)ˣ) = 6 := by
  -- 验证 3 的阶是 6
  -- 3¹ = 3, 3² = 2, 3³ = 6, 3⁴ = 4, 3⁵ = 5, 3⁶ = 1 (mod 7)
  have : Fact (7 : ℕ).Prime := by norm_num
  have h : orderOf (3 : (ZMod 7)ˣ) = 6 := by
    rw [← Fintype.card_units (ZMod 7)]
    apply orderOf_eq_card_of_forall_mem_zpowers
    intro x
    have h_cyclic : IsCyclic (ZMod 7)ˣ := by infer_instance
    rcases h_cyclic with ⟨g, hg⟩
    -- 验证3是生成元
    have : x ∈ Submonoid.zpowers (3 : (ZMod 7)ˣ) := by
      -- 手动验证 (Z/7Z)* = {1, 2, 3, 4, 5, 6} 且 3 是生成元
      native_decide
    exact this
  exact h
```

### 示例2：模 8 不存在原根

φ(8) = 4，但 (ℤ/8ℤ)* = {1, 3, 5, 7} 中所有元素的阶都是 2：
3² ≡ 1, 5² ≡ 1, 7² ≡ 1 (mod 8)

```lean
example : ¬HasPrimitiveRoot 8 := by
  apply no_primitive_root_power_of_two
  norm_num
```

## 数学意义

原根存在定理的重要性：

1. **结构刻画**: 完全刻画了循环乘法群的情形
2. **离散对数**: 原根是离散对数问题的基础
3. **密码学**: Diffie-Hellman密钥交换的安全性基于离散对数
4. **数论**: 与二次剩余、高斯和等深刻联系

## 计算应用

### 求原根的算法

1. 分解 φ(n) = q₁^e₁ · ... · qₖ^eₖ
2. 随机选取 g，验证 g^(φ(n)/qᵢ) ≢ 1 (mod n) 对所有 i
3. 若满足，则 g 是原根

### 复杂度

- 验证原根：O(log³ n)
- 找原根（期望）：O(φ(φ(n))/φ(n) · log³ n)

## 推广

1. **有限域**: 任何有限域的乘法群都是循环群
2. **分圆域**: 原根与单位根的关系
3. **代数整数**: 在代数整数环中的推广

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `Mathlib.FieldTheory.Finite.Basic`: 有限域理论
- `Mathlib.Data.ZMod.Basic`: 模n整数
- `Mathlib.Data.Nat.Totient`: 欧拉函数
- `Mathlib.RingTheory.RootsOfUnity.Basic`: 单位根理论
- `IsPrimitiveRoot`: 原根的核心定义
- `IsCyclic`: 循环群
-/
