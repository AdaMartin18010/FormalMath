/-
# 第一同构定理的形式化证明 / Formalization of First Isomorphism Theorem

## Mathlib4对应
- **模块**: `Mathlib.GroupTheory.QuotientGroup`
- **核心定理**: `MonoidHom.quotientKerEquivRange`
- **相关定义**: 
  - `MonoidHom.ker`: 同态的核
  - `MonoidHom.range`: 同态的像
  - `QuotientGroup`: 商群

## 定理陈述
设 φ: G → H 是群同态，则 G/ker(φ) ≅ im(φ)

其中 ker(φ) = {g ∈ G | φ(g) = 1} 是同态的核，
im(φ) = {φ(g) | g ∈ G} 是同态的像。

## 数学意义
第一同构定理是群论中最基本、最重要的定理之一。
它建立了群同态、正规子群和商群之间的深刻联系。

## 历史背景
同构定理由数学家埃米·诺特(Emmy Noether)系统化，
是抽象代数中的核心工具。
-/

import Mathlib.GroupTheory.QuotientGroup
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Algebra.Hom.Group

universe u v

namespace FirstIsomorphismTheorem

open Subgroup Group MonoidHom

/-
## 预备知识

### 群同态的核 (Kernel)
对于群同态 φ: G → H，其核定义为：
ker(φ) = {g ∈ G | φ(g) = 1_H}

核是 G 的正规子群。

### 群同态的像 (Image)
对于群同态 φ: G → H，其像定义为：
im(φ) = {φ(g) | g ∈ G}

像是 H 的子群。

### 商群 (Quotient Group)
对于群 G 及其正规子群 N，商群 G/N 的元素是 N 的陪集。
群运算定义为：(aN)(bN) = (ab)N
-

-- 核是正规子群
theorem ker_is_normal {G H : Type*} [Group G] [Group H]
    (φ : G →* H) : (ker φ).Normal := by
  /- 证明：核是正规子群
     需要证明：∀ n ∈ ker(φ), ∀ g ∈ G, gng⁻¹ ∈ ker(φ)
  -/
  constructor
  intro n hn g
  simp [ker] at hn ⊢
  /- φ(gng⁻¹) = φ(g)φ(n)φ(g)⁻¹ = φ(g)·1·φ(g)⁻¹ = 1 -/
  rw [map_mul, map_mul, hn, mul_one, mul_inv_cancel_right]

-- 同态基本性质的引理
theorem ker_mem_iff {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (g : G) : g ∈ ker φ ↔ φ g = 1 := by
  simp [ker]

/-
## 第一同构定理的主证明

**定理**: 设 φ: G → H 是群同态，定义映射
ψ: G/ker(φ) → im(φ), ψ(g·ker(φ)) = φ(g)

则 ψ 是群同构。

**证明步骤**:
1. 证明 ψ 是良定义的（与代表元选择无关）
2. 证明 ψ 是群同态
3. 证明 ψ 是单射
4. 证明 ψ 是满射
-

-- 第一同构定理：G/ker(φ) ≅ im(φ)
def firstIsomorphism {G H : Type*} [Group G] [Group H]
    (φ : G →* H) : G ⧸ ker φ →* range φ where
  /- 定义同构映射 ψ: G/ker(φ) → im(φ) -/
  toFun := fun x =>
    Quotient.liftOn' x (fun g => ⟨φ g, by simp [range]⟩) (by
      /- 证明良定义性：若 g₁·ker(φ) = g₂·ker(φ)，则 φ(g₁) = φ(g₂) -/
      intro g₁ g₂ h
      simp at h ⊢
      have h_ker : g₁⁻¹ * g₂ ∈ ker φ := by
        simpa using h
      simp [ker_mem_iff] at h_ker
      /- φ(g₁) = φ(g₂) ⇔ φ(g₁)⁻¹·φ(g₂) = 1 ⇔ φ(g₁⁻¹·g₂) = 1 -/
      calc
        φ g₁ = φ g₁ * 1 := by rw [mul_one]
        _ = φ g₁ * (φ g₁)⁻¹ * φ g₂ := by rw [h_ker]; group
        _ = φ g₂ := by group
    )
  
  /- 证明 ψ 是同态 -/
  map_mul' := by
    intro x y
    refine Quotient.inductionOn₂' x y (fun g₁ g₂ => ?_)
    simp
    /- ψ((g₁·ker)(g₂·ker)) = ψ(g₁g₂·ker) = φ(g₁g₂) = φ(g₁)φ(g₂) = ψ(g₁·ker)ψ(g₂·ker) -/
    rw [map_mul]

-- 第一同构定理的同构版本
theorem firstIsomorphismEquiv {G H : Type*} [Group G] [Group H]
    (φ : G →* H) : G ⧸ ker φ ≃* range φ := by
  /- 使用Mathlib4的 quotientKerEquivRange -/
  exact φ.quotientKerEquivRange

-- 证明 firstIsomorphism 是双射
theorem firstIsomorphism_bijective {G H : Type*} [Group G] [Group H]
    (φ : G →* H) : Function.Bijective (firstIsomorphism φ) := by
  constructor
  
  /- 单射性证明 -/
  · intro x y h_eq
    refine Quotient.inductionOn₂' x y (fun g₁ g₂ h_eq => ?_)
    simp [firstIsomorphism] at h_eq
    /- ψ(g₁·ker) = ψ(g₂·ker) ⇒ φ(g₁) = φ(g₂) ⇒ g₁·ker = g₂·ker -/
    have h : φ g₁ = φ g₂ := by simpa using h_eq
    have : g₁⁻¹ * g₂ ∈ ker φ := by
      simp [ker_mem_iff]
      calc
        φ (g₁⁻¹ * g₂) = φ g₁⁻¹ * φ g₂ := by rw [map_mul]
        _ = (φ g₁)⁻¹ * φ g₂ := by rw [map_inv]
        _ = (φ g₁)⁻¹ * φ g₁ := by rw [h]
        _ = 1 := by group
    
    /- g₁·ker = g₂·ker ⇔ g₁⁻¹·g₂ ∈ ker -/
    simpa using this
  
  /- 满射性证明 -/
  · intro y
    rcases y with ⟨y, hy⟩
    simp [range] at hy
    rcases hy with ⟨g, rfl⟩
    /- 对于任意 y = φ(g) ∈ im(φ)，存在 g·ker 使得 ψ(g·ker) = y -/
    use QuotientGroup.mk (ker φ) g
    simp [firstIsomorphism]

-- 同态的阶公式：|G| = |ker(φ)| · |im(φ)|
theorem homomorphism_order_formula {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] (φ : G →* H) :
    Fintype.card G = Fintype.card (ker φ) * Fintype.card (range φ) := by
  /- 利用第一同构定理：G/ker(φ) ≅ im(φ) -/
  have h_iso : G ⧸ ker φ ≃* range φ := firstIsomorphismEquiv φ
  
  /- |G/ker(φ)| = |im(φ)| -/
  have h_card : Fintype.card (G ⧸ ker φ) = Fintype.card (range φ) := by
    exact Fintype.card_congr (MulEquiv.toEquiv h_iso)
  
  /- |G| = |ker(φ)| · |G/ker(φ)| （拉格朗日定理） -/
  have h_lagrange : Fintype.card G = Fintype.card (ker φ) * Fintype.card (G ⧸ ker φ) := by
    rw [← Subgroup.index_mul_card (ker φ)]
    rw [Subgroup.index]
    rfl
  
  /- 综合以上结果 -/
  rw [h_card] at h_lagrange
  exact h_lagrange

/-
## 第二同构定理（对应定理）

设 G 是群，N 是 G 的正规子群，H 是 G 的子群，则
HN/N ≅ H/(H∩N)

其中 HN = {hn | h ∈ H, n ∈ N}
-

-- 第二同构定理
theorem secondIsomorphism {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (H : Subgroup G) :
    let HN : Subgroup G := {
      carrier := {x | ∃ h ∈ H, ∃ n ∈ N, x = h * n}
      mul_mem' := by
        rintro _ _ ⟨h₁, hh₁, n₁, hn₁, rfl⟩ ⟨h₂, hh₂, n₂, hn₂, rfl⟩
        use h₁ * h₂, H.mul_mem hh₁ hh₂
        use h₂⁻¹ * n₁ * h₂ * n₂
        · /- 证明 h₂⁻¹·n₁·h₂ ∈ N（利用N的正规性） -/
          have : h₂⁻¹ * n₁ * h₂ ∈ N := by
            apply N.conj_mem
            exact hn₁
          exact N.mul_mem this hn₂
        · group
      one_mem' := by
        use 1, H.one_mem, 1, N.one_mem
        simp
      inv_mem' := by
        rintro _ ⟨h, hh, n, hn, rfl⟩
        use h⁻¹, H.inv_mem hh
        use h⁻¹ * n⁻¹ * h
        · /- 证明 h⁻¹·n⁻¹·h ∈ N -/
          have : h⁻¹ * n⁻¹ * h ∈ N := by
            apply N.conj_mem
            exact N.inv_mem hn
          exact this
        · group
    }
    HN ⧸ (N.subgroupOf HN) ≃* H ⧸ (N.subgroupOf H) := by
  /- 使用Mathlib4的 secondIsomorphismTheorem -/
  exact secondIsomorphismTheorem H N

/-
## 第三同构定理

设 G 是群，N 和 M 是 G 的正规子群，且 N ⊆ M，则
(G/N)/(M/N) ≅ G/M
-

-- 第三同构定理
theorem thirdIsomorphism {G : Type*} [Group G] (N M : Subgroup G) 
    [N.Normal] [M.Normal] (h_le : N ≤ M) :
    (G ⧸ N) ⧸ (M.map (QuotientGroup.mk' N)) ≃* G ⧸ M := by
  /- 使用Mathlib4的 thirdIsomorphismTheorem -/
  exact thirdIsomorphismTheorem h_le

end FirstIsomorphismTheorem

/-
## 应用示例

### 示例1：整数加法群到模n剩余类群的同态

```lean
-- 定义同态 φ: ℤ → ℤ/nℤ, φ(k) = k mod n
example (n : ℕ) [NeZero n] : ℤ →* ZMod n := Int.castRingHom (ZMod n)

-- ker(φ) = nℤ
-- im(φ) = ℤ/nℤ
-- 因此 ℤ/nℤ ≅ ℤ/nℤ（平凡情况）
```

### 示例2：行列式同态

```lean
-- GL(n, ℝ) →* ℝ*, φ(A) = det(A)
-- ker(φ) = SL(n, ℝ)（特殊线性群）
-- im(φ) = ℝ*（非零实数乘法群）
-- 因此 GL(n, ℝ)/SL(n, ℝ) ≅ ℝ*
```

## 数学意义

第一同构定理的重要性在于：

1. **结构分解**：它将复杂的群同态分解为满射和单射的复合
2. **正规子群分类**：建立了正规子群与同态之间的对应
3. **计算工具**：提供了计算商群结构的有效方法

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `MonoidHom.quotientKerEquivRange`: 第一同构定理的核心实现
- `secondIsomorphismTheorem`: 第二同构定理
- `thirdIsomorphismTheorem`: 第三同构定理
-/
