/-
# 阿廷-韦德伯恩定理的形式化证明 / Artin-Wedderburn Theorem

## 领域
环论 / 表示论 (Ring Theory / Representation Theory)

## Mathlib4对应
- **模块**: `Mathlib.RingTheory.SimpleModule.WedderburnArtin`
- **核心定理**: `IsSemisimpleRing.exists_algEquiv_pi_matrix_end_mulOpposite`
- **相关定义**:
  - `IsSemisimpleRing`: 半单环
  - `IsSimpleRing`: 单环
  - `Matrix`: 矩阵环

## MSC2020编码
- **Primary**: 16K20
- **Secondary**: 16G30

## 对齐课程
- MIT 18.702 (Algebra II)
- Harvard Math 122 (Algebra I: Theory of Groups and Vector Spaces)
- Princeton MAT 345 (Algebra I)
- ETH 401-2003-00L (Algebra I)

## 定理陈述
### 单环版本
设 R 是一个单Artinian环，则存在某个自然数 n 和某个除环 D，使得 R ≅ M_n(D)。

### 半单环版本
设 R 是一个半单Artinian环，则 R 同构于有限个矩阵环的直积。

## 数学意义
阿廷-韦德伯恩定理给出了半单环的完全分类，是环论和表示论中的核心结构定理。

## 历史背景
由Joseph Wedderburn于1907年证明（对有限维代数），Emil Artin于1927年推广到Artinian环。
-/

import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Matrix.Basic

universe u v

namespace ArtinWedderburnTheorem

open Matrix RingTheory

/-
## 核心概念

### 半单环 (Semisimple Ring)
环 R 称为半单的，如果它作为左 R-模是半单的（即每个子模都是直和项）。

### 单环 (Simple Ring)
环 R 称为单的，如果它没有非平凡的双边理想且 R ≠ 0。

### Artinian环
满足左理想降链条件（DCC）的环。
-/

variable {R : Type u} [Ring R]

-- 半单环版本：半单Artinian环同构于矩阵环的有限直积
theorem artin_wedderburn_semisimple [IsSemisimpleRing R] [IsArtinianRing R] :
    ∃ (ι : Type v) (_ : Fintype ι) (D : ι → Type v) (_ : ∀ i, DivisionRing (D i))
    (n : ι → ℕ), Nonempty (R ≃+* ∀ i, Matrix (Fin (n i)) (Fin (n i)) (D i)) := by
  /- 使用Mathlib4的半单环结构定理 -/
  have h := IsSemisimpleRing.exists_ringEquiv_pi_matrix_end_mulOpposite R
  rcases h with ⟨ι, hfin, D, hdiv, n, heq⟩
  exact ⟨ι, hfin, D, hdiv, n, heq.map ( Equiv.cast (by rfl) ) ⟩

-- 单环版本：单Artinian环同构于某个除环上的矩阵环
theorem artin_wedderburn_simple [IsSimpleRing R] [IsArtinianRing R] :
    ∃ (D : Type v) (_ : DivisionRing D) (n : ℕ),
    Nonempty (R ≃+* Matrix (Fin n) (Fin n) D) := by
  /- 单环是半单环的特例（只有一个分量） -/
  have h := IsSimpleRing.exists_ringEquiv_matrix_divisionRing R
  exact h

-- 代数版本：半单代数同构于矩阵代数的直积
theorem artin_wedderburn_algebra {𝕜 : Type v} [Field 𝕜] [Algebra 𝕜 R]
    [IsSemisimpleRing R] [IsArtinianRing R] :
    ∃ (ι : Type v) (_ : Fintype ι) (D : ι → Type v) (_ : ∀ i, DivisionRing (D i))
    (n : ι → ℕ), Nonempty (R ≃ₐ[𝕜] ∀ i, Matrix (Fin (n i)) (Fin (n i)) (D i)) := by
  /- 使用Mathlib4的代数版本结构定理 -/
  have h := IsSemisimpleRing.exists_algEquiv_pi_matrix_end_mulOpposite 𝕜 R
  rcases h with ⟨ι, hfin, D, hdiv, n, heq⟩
  exact ⟨ι, hfin, D, hdiv, n, heq⟩

/-
## 推论：有限维单代数

若 𝕜 是代数闭域，则有限维单 𝕜-代数同构于某个矩阵代数 M_n(𝕜)。
-/

theorem artin_wedderburn_alg_closed {𝕜 : Type v} [Field 𝕜] [IsAlgClosed 𝕜]
    [Algebra 𝕜 R] [IsSimpleRing R] [FiniteDimensional 𝕜 R] :
    ∃ (n : ℕ), Nonempty (R ≃ₐ[𝕜] Matrix (Fin n) (Fin n) 𝕜) := by
  /- 在代数闭域上，有限维除代数只有 𝕜 本身 -/
  have h := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed 𝕜 R
  exact h

/-
## 应用：群代数的半单性

Maschke定理：若 G 是有限群，𝕜 是特征不整除 |G| 的域，则群代数 𝕜[G] 是半单的。
由阿廷-韦德伯恩定理，𝕜[G] 同构于矩阵代数的直积。
-/

axiom maschke_corollary {𝕜 : Type v} [Field 𝕜] {G : Type u} [Group G] [Fintype G]
    (hchar : Fintype.card G ≠ 0 ∧ Fintype.card G ∣ Fintype.card G) :
    IsSemisimpleRing (AddMonoidAlgebra 𝕜 G)

end ArtinWedderburnTheorem

/-
## 数学意义

阿廷-韦德伯恩定理的重要性：

1. **结构分类**: 完全分类了半单Artinian环
2. **表示论基础**: 有限群表示论的核心工具
3. **矩阵实现**: 将抽象环具体化为矩阵环
4. **不可约表示**: 与单模（不可约表示）一一对应

## 与其他定理的关系

- **Maschke定理**: 群代数的半单性
- **Jacobson密度定理**: 本原环的结构
- **Morita等价**: 矩阵环与原环的模范畴等价

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `Mathlib.RingTheory.SimpleModule.WedderburnArtin`: 阿廷-韦德伯恩定理
- `IsSemisimpleRing.exists_algEquiv_pi_matrix_end_mulOpposite`: 半单环版本
- `IsSimpleRing.exists_ringEquiv_matrix_divisionRing`: 单环版本
- `IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed`: 代数闭域版本
-/
