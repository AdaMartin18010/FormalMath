/-
# 轨道-稳定子定理 / Orbit-Stabilizer Theorem

## Mathlib4 对应
- **模块**: `Mathlib.GroupTheory.GroupAction.Basic`, `Mathlib.GroupTheory.Coset`
- **核心定理**: `MulAction.orbitEquivQuotientStabilizer`

## 定理陈述
设群 $G$ 作用于集合 $X$，则对任意 $x \in X$，轨道 $G \cdot x$ 与陪集空间 $G / G_x$ 之间存在双射，
从而 $|G \cdot x| = [G : G_x] = |G| / |G_x|$（当 $G$ 有限时）。
-/

import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Coset
import Mathlib.SetTheory.Cardinal.Finite

namespace OrbitStabilizerTheorem

open MulAction Subgroup

variable {G X : Type*} [Group G] [MulAction G X]

-- 轨道的定义（已内建于 Mathlib4）
def Orbit' (x : X) : Set X := orbit G x

-- 稳定子群的定义（已内建于 Mathlib4）
def Stabilizer' (x : X) : Subgroup G := stabilizer G x

-- 轨道-稳定子定理：轨道与 G/stabilizer 双射
theorem orbit_stabilizer (x : X) :
    Nonempty (orbit G x ≃ G ⧸ stabilizer G x) := by
  /- Mathlib4 中的标准结论 -/
  use orbitEquivQuotientStabilizer G x

-- 有限群版本：|轨道| = |G| / |稳定子|
theorem orbit_stabilizer_card [Fintype G] [Fintype X] [DecidableEq X] (x : X) :
    Fintype.card (orbit G x) = Fintype.card G / Fintype.card (stabilizer G x) := by
  /- 利用拉格朗日定理：|G| = |轨道| · |稳定子| -/
  have h := Fintype.card_congr (orbitEquivQuotientStabilizer G x)
  rw [h]
  rw [Subgroup.index_eq_card (stabilizer G x)]
  symm
  exact Eq.symm (Lagrange.index_mul_card (stabilizer G x))

end OrbitStabilizerTheorem
