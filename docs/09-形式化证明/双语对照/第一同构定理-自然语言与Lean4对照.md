---
title: "第一同构定理 自然语言与 Lean4 对照"
level: "silver"
target_courses:
  - "MIT 18.701"
---

## 定理陈述

**自然语言**：设 \(\varphi: G \to H\) 是群同态，则商群 \(G / \ker(\varphi)\) 与同态的像 \(\operatorname{im}(\varphi)\) 同构，即
\[
G / \ker(\varphi) \cong \operatorname{im}(\varphi).
\]

**Lean4**：

```lean
import Mathlib.GroupTheory.QuotientGroup
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Algebra.Hom.Group

universe u v
namespace FirstIsomorphismTheorem
open Subgroup Group MonoidHom

-- 第一同构定理的同构版本
theorem firstIsomorphismEquiv {G H : Type*} [Group G] [Group H]
    (φ : G →* H) : G ⧸ ker φ ≃* range φ := by
  exact φ.quotientKerEquivRange
end FirstIsomorphismTheorem
```

## 证明思路

**自然语言**：第一同构定理的证明关键在于构造从商群到像集的自然映射，并验证它是群同构。
1. **构造映射**：定义 \(\psi: G/\ker(\varphi) \to \operatorname{im}(\varphi)\) 为 \(\psi(g \cdot \ker(\varphi)) = \varphi(g)\)。
2. **良定义性**：若 \(g_1 \cdot \ker(\varphi) = g_2 \cdot \ker(\varphi)\)，则 \(g_1^{-1} g_2 \in \ker(\varphi)\)，从而 \(\varphi(g_1) = \varphi(g_2)\)。
3. **同态性**：\(\psi((g_1 \ker)(g_2 \ker)) = \psi(g_1 g_2 \ker) = \varphi(g_1 g_2) = \varphi(g_1)\varphi(g_2) = \psi(g_1 \ker)\psi(g_2 \ker)\)。
4. **单射性**：若 \(\psi(g_1 \ker) = \psi(g_2 \ker)\)，则 \(\varphi(g_1) = \varphi(g_2)\)，于是 \(g_1^{-1} g_2 \in \ker(\varphi)\)，故 \(g_1 \ker = g_2 \ker\)。
5. **满射性**：对任意 \(y = \varphi(g) \in \operatorname{im}(\varphi)\)，取陪集 \(g \ker\) 即可。

**Lean4**：以下展示在 Lean4 中如何手工构造该同构映射并验证双射性。

```lean
def firstIsomorphism {G H : Type*} [Group G] [Group H]
    (φ : G →* H) : G ⧸ ker φ →* range φ where
  toFun := fun x =>
    Quotient.liftOn' x (fun g => ⟨φ g, by simp [range]⟩) (by
      intro g₁ g₂ h
      simp at h ⊢
      have h_ker : g₁⁻¹ * g₂ ∈ ker φ := by simpa using h
      simp at h_ker
      calc
        φ g₁ = φ g₁ * 1 := by rw [mul_one]
        _ = φ g₁ * (φ g₁)⁻¹ * φ g₂ := by rw [h_ker]; group
        _ = φ g₂ := by group)
  map_mul' := by
    intro x y
    refine Quotient.inductionOn₂' x y (fun g₁ g₂ => ?_)
    simp
    rw [map_mul]

theorem firstIsomorphism_bijective {G H : Type*} [Group G] [Group H]
    (φ : G →* H) : Function.Bijective (firstIsomorphism φ) := by
  constructor
  · -- 单射
    intro x y h_eq
    refine Quotient.inductionOn₂' x y (fun g₁ g₂ h_eq => ?_)
    simp [firstIsomorphism] at h_eq
    have h : φ g₁ = φ g₂ := by simpa using h_eq
    have : g₁⁻¹ * g₂ ∈ ker φ := by
      simp
      calc
        φ (g₁⁻¹ * g₂) = φ g₁⁻¹ * φ g₂ := by rw [map_mul]
        _ = (φ g₁)⁻¹ * φ g₂ := by rw [map_inv]
        _ = (φ g₁)⁻¹ * φ g₁ := by rw [h]
        _ = 1 := by group
    simpa using this
  · -- 满射
    intro y
    rcases y with ⟨y, hy⟩
    simp [range] at hy
    rcases hy with ⟨g, rfl⟩
    use QuotientGroup.mk (ker φ) g
    simp [firstIsomorphism]
```

## 关键 tactic/概念 教学

- `Quotient.liftOn'`：在商群上定义函数时，必须证明该定义与代表元的选择无关（良定义性）。
- `Quotient.inductionOn₂'`：对商群中的两个元素进行归纳，将问题约化到代表元层面。
- `Function.Bijective`：在 Lean 中构造同构时，需要分别证明 `Injective` 和 `Surjective`。

## 练习

1. 利用第一同构定理证明：\(|G| = |\ker(\varphi)| \cdot |\operatorname{im}(\varphi)|\)。
2. 证明第二同构定理（对应定理）：若 \(N \trianglelefteq G\)，\(H \leq G\)，则 \(HN/N \cong H/(H \cap N)\)。
3. 在 Lean4 中，验证同态 \(\det: GL_n(\mathbb{R}) \to \mathbb{R}^*\) 的核为 \(SL_n(\mathbb{R})\)，并由此得到 \(GL_n(\mathbb{R})/SL_n(\mathbb{R}) \cong \mathbb{R}^*\)。
