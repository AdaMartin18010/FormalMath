---
title: "Cayley 定理 自然语言与 Lean4 对照"
msc_primary: 68V20
level: "silver"
target_courses:
  - "MIT 18.701"
---

## 定理陈述

**自然语言**：每个群 \(G\) 都同构于某个置换群的子群。更精确地说，\(G\) 同构于对称群 \(S_G\)（\(G\) 上所有置换构成的群）的子群。

**Lean4**：

```lean
import Mathlib.GroupTheory.Cayley
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.GroupAction.Basic

universe u
namespace CayleyTheorem
open MulAction Perm Equiv

-- 左乘作用诱导的置换表示
def leftRegularRepresentation {G : Type u} [Group G] : G →* Perm G where
  toFun := fun g =>
    ⟨fun x => g * x,
     fun x => g⁻¹ * x,
     by intro x; simp [mul_assoc],
     by intro x; simp [mul_assoc]⟩
  map_one' := by ext x; simp
  map_mul' := by intro g h; ext x; simp [mul_assoc]

-- Cayley 定理：G 嵌入到 S_G 中
theorem cayley_embedding {G : Type u} [Group G] :
    ∃ (H : Subgroup (Perm G)), Nonempty (G ≃* H) := by
  use leftRegularRepresentation.range
  have h_iso : G ≃* leftRegularRepresentation.range := by
    apply MulEquiv.ofBijective
      (leftRegularRepresentation.codRestrict leftRegularRepresentation.range (fun g => by simp))
    constructor
    · -- 单射
      intro g₁ g₂ h_eq
      simp [leftRegularRepresentation] at h_eq
      have h : g₁ * 1 = g₂ * 1 := by
        simpa using congrFun (congrArg (↑) h_eq) 1
      simp at h
      exact h
    · -- 满射
      intro p
      rcases p with ⟨p, hp⟩
      simp at hp
      rcases hp with ⟨g, rfl⟩
      use g
      simp
  exact Nonempty.intro h_iso
end CayleyTheorem
```

## 证明思路

**自然语言**：Cayley 定理的证明利用了群在自身上的左乘作用。
1. 考虑群 \(G\) 在集合 \(G\) 上的左乘作用：\((g, x) \mapsto gx\)。
2. 这个作用诱导了一个群同态 \(\varphi: G \to S_G\)，将每个 \(g \in G\) 映射为左乘置换 \(L_g: x \mapsto gx\)。
3. 证明 \(\varphi\) 是单射：若 \(L_{g_1} = L_{g_2}\)，则对单位元 \(1\) 作用得 \(g_1 \cdot 1 = g_2 \cdot 1\)，即 \(g_1 = g_2\)。
4. 由第一同构定理，\(G \cong \operatorname{im}(\varphi)\)，而 \(\operatorname{im}(\varphi)\) 是 \(S_G\) 的子群。

**Lean4**：代码中 `leftRegularRepresentation` 显式构造了左乘作用诱导的置换同态。通过验证其单射性（核心观察是令 \(x=1\)），即可得到 \(G\) 与 \(S_G\) 的某个子群同构。

## 关键 tactic/概念 教学

- `ext x`：对置换（函数）证明相等时，逐点验证。
- `congrFun (congrArg (↑) h_eq) 1`：利用函数外延性，将“两个置换相等”转化为“在单位元处的像相等”。
- `MulEquiv.ofBijective`：从双射群同态构造群同构。
- `codRestrict`：将同态的值域限制到子群中。

## 练习

1. 证明：若 \(|G| = n\)，则 \(G\) 同构于 \(S_n\) 的某个子群，并且 \(n \mid n!\)。
2. 将 Klein 四元群 \(V_4\) 具体实现为 \(S_4\) 的子群。
3. 在 Lean4 中验证：循环群 \(C_n\) 可以由 \(n\)-轮换 \((1\,2\,\dots\,n)\) 实现。
