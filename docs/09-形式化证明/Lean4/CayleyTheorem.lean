/-
# Cayley定理的形式化证明 / Formalization of Cayley's Theorem

## Mathlib4对应
- **模块**: `Mathlib.GroupTheory.Cayley`
- **核心定理**: `Cayley.embedding`, `Cayley.induction`
- **相关定义**: 
  - `MulAction`: 群作用
  - `Perm`: 置换群
  - `MonoidHom`: 幺半群同态

## 定理陈述
每个群 G 都同构于某个置换群的子群。

更精确地说，每个群 G 都同构于对称群 S_G（G 上所有置换构成的群）的子群。

## 数学意义
Cayley定理是群论中最基本的定理之一，它表明：
1. 任何抽象群都可以实现为具体的置换群
2. 置换群是"通用"的群结构
3. 为研究群提供了具体表示

## 历史背景
该定理由亚瑟·凯莱(Arthur Cayley)在1854年提出，
是群论从具体（置换群）走向抽象（公理化群）的桥梁。
-/

import Mathlib.GroupTheory.Cayley
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Logic.Equiv.Basic

universe u v

namespace CayleyTheorem

open MulAction Perm Equiv

/-
## 核心概念

### 群作用 (Group Action)
群 G 在集合 X 上的作用是一个映射 G × X → X，记为 (g, x) ↦ g · x，满足：
1. 1 · x = x （单位元作用平凡）
2. (gh) · x = g · (h · x) （作用的结合性）

### 正则作用 (Regular Action)
群 G 在自身上的左乘作用：g · x = gx
这是一个传递的自由作用。

### 置换表示 (Permutation Representation)
群作用诱导同态 G → S_X，将群元素映射为集合上的置换。
-/

-- 群在自身上的左乘作用是自由的
theorem leftMulAction_free {G : Type u} [Group G] :
    ∀ (g : G), (∀ (x : G), g • x = x) → g = 1 := by
  /- 证明思路：若对所有 x，gx = x，则特别地，g·1 = 1，所以 g = 1 -/
  intro g h
  have h1 : g * 1 = 1 := by
    simpa [SMul.smul, HSMul.hSMul, MulAction.toSMul, Mul.smul_def] using h 1
  simp at h1
  exact h1

-- 群在自身上的左乘作用是传递的
theorem leftMulAction_transitive {G : Type u} [Group G] :
    ∀ (x y : G), ∃ (g : G), g • x = y := by
  /- 证明思路：对于任意 x, y ∈ G，取 g = yx⁻¹，则 g·x = yx⁻¹·x = y -/
  intro x y
  use y * x⁻¹
  simp [SMul.smul, HSMul.hSMul, MulAction.toSMul, Mul.smul_def]
  group

/-
## Cayley定理的主证明

**定理**: 每个群 G 都同构于对称群 S_G 的子群。

**证明步骤**:
1. 考虑 G 在自身上的左乘作用
2. 这个作用诱导同态 φ: G → S_G
3. 证明 φ 是单射（作用的核是平凡的）
4. 因此 G ≅ im(φ) ≤ S_G
-/

-- 左乘作用诱导的置换表示
def leftRegularRepresentation {G : Type u} [Group G] : G →* Perm G where
  /- 定义：将 g ∈ G 映射为左乘置换 L_g: x ↦ gx -/
  toFun := fun g => 
    ⟨fun x => g * x, 
     fun x => g⁻¹ * x,
     by intro x; simp [mul_assoc],
     by intro x; simp [mul_assoc]⟩
  
  /- 证明这是同态 -/
  map_one' := by
    ext x
    simp
  
  map_mul' := by
    intro g h
    ext x
    simp [mul_assoc]

-- Cayley定理：G 嵌入到 S_G 中
theorem cayley_embedding {G : Type u} [Group G] :
    ∃ (H : Subgroup (Perm G)), Nonempty (G ≃* H) := by
  /- 证明思路：
     1. 使用左乘作用诱导的置换表示 φ: G → S_G
     2. 证明 φ 是单射
     3. 因此 G ≅ im(φ)，而 im(φ) ≤ S_G
  -/
  use leftRegularRepresentation.range
  
  /- 构造 G 与 im(φ) 的同构 -/
  have h_iso : G ≃* leftRegularRepresentation.range := by
    apply MulEquiv.ofBijective 
      (leftRegularRepresentation.codRestrict leftRegularRepresentation.range (fun g => by simp))
    constructor
    
    /- 单射性证明 -/
    · intro g₁ g₂ h_eq
      simp [leftRegularRepresentation] at h_eq
      /- 若 L_{g₁} = L_{g₂}，则 g₁·1 = g₂·1，所以 g₁ = g₂ -/
      have h : g₁ * 1 = g₂ * 1 := by
        simpa using congrFun (congrArg (↑) h_eq) 1
      simp at h
      exact h
    
    /- 满射性证明 -/
    · intro p
      rcases p with ⟨p, hp⟩
      simp at hp
      rcases hp with ⟨g, rfl⟩
      use g
      simp
  
  exact Nonempty.intro h_iso

-- 置换表示是单射的
theorem leftRegularRepresentation_injective {G : Type u} [Group G] :
    Function.Injective (leftRegularRepresentation : G → Perm G) := by
  intro g₁ g₂ h_eq
  /- 若 φ(g₁) = φ(g₂)，则对所有 x，g₁x = g₂x -/
  have h : ∀ (x : G), g₁ * x = g₂ * x := by
    intro x
    simpa using congrFun (congrArg (↑) h_eq) x
  /- 特别地，g₁·1 = g₂·1 -/
  specialize h 1
  simp at h
  exact h

-- Cayley定理的显式同构版本
theorem cayley_theorem {G : Type u} [Group G] :
    G ≃* leftRegularRepresentation.range := by
  /- 直接构造同构 -/
  apply MulEquiv.ofBijective 
    (leftRegularRepresentation.codRestrict leftRegularRepresentation.range (fun g => by simp))
  constructor
  · exact leftRegularRepresentation_injective
  · intro p
    rcases p with ⟨p, hp⟩
    simp at hp
    rcases hp with ⟨g, rfl⟩
    use g
    simp

/-
## 推广：一般群作用的Cayley型定理

**定理**: 若群 G 忠实地作用在集合 X 上，则 G 同构于 S_X 的子群。
-/

-- 忠实作用的单射性
theorem faithful_action_injective {G : Type u} [Group G] {X : Type v} 
    [MulAction G X] (h_faithful : FaithfulSMul G X) :
    Function.Injective (MulAction.toPermHom G X) := by
  /- 由忠实作用的定义直接得到 -/
  intro g₁ g₂ h_eq
  apply h_faithful.eq_of_smul_eq_smul
  intro x
  simpa using congrFun (congrArg (↑) h_eq) x

-- 忠实作用的Cayley型定理
theorem cayley_for_faithful_action {G : Type u} [Group G] {X : Type v} 
    [MulAction G X] [FaithfulSMul G X] :
    ∃ (H : Subgroup (Perm X)), Nonempty (G ≃* H) := by
  use (MulAction.toPermHom G X).range
  have h_iso : G ≃* (MulAction.toPermHom G X).range := by
    apply MulEquiv.ofBijective 
      ((MulAction.toPermHom G X).codRestrict (MulAction.toPermHom G X).range (fun g => by simp))
    constructor
    · exact faithful_action_injective ‹FaithfulSMul G X›
    · intro p
      rcases p with ⟨p, hp⟩
      simp at hp
      rcases hp with ⟨g, rfl⟩
      use g
      simp
  exact Nonempty.intro h_iso

/-
## 有限群的应用

对于有限群 G，Cayley定理意味着：
- 若 |G| = n，则 G 同构于 S_n 的子群
- 这是研究有限群分类的重要工具
-/

-- 有限群的Cayley嵌入
theorem finite_cayley {G : Type u} [Group G] [Fintype G] :
    ∃ (H : Subgroup (Equiv.Perm G)), Nonempty (G ≃* H) := by
  exact cayley_embedding

-- 有限群的阶的界
theorem cayley_order_bound {G : Type u} [Group G] [Fintype G] :
    Fintype.card G ∣ Nat.factorial (Fintype.card G) := by
  /- 由Cayley定理，G 同构于 S_n 的子群，其中 n = |G| -/
  rcases cayley_embedding with ⟨H, ⟨iso⟩⟩
  /- |G| = |H|，而 |H| 整除 |S_n| = n! -/
  have h_order_eq : Fintype.card G = Fintype.card H := by
    exact Fintype.card_congr (MulEquiv.toEquiv iso)
  rw [h_order_eq]
  /- 由拉格朗日定理，子群的阶整除群的阶 -/
  apply Subgroup.card_subgroup_dvd_card

/-
## 右正则表示

类似地，可以定义右乘作用（需要调整以成为左作用）。
-/

-- 右乘作用（通过逆元转换为左作用）
def rightRegularRepresentation {G : Type u} [Group G] : G →* Perm G where
  toFun := fun g => 
    ⟨fun x => x * g⁻¹,
     fun x => x * g,
     by intro x; simp [mul_assoc],
     by intro x; simp [mul_assoc]⟩
  map_one' := by
    ext x
    simp
  map_mul' := by
    intro g h
    ext x
    simp [mul_assoc, mul_inv_cancel_right]

-- 左右正则表示的关系
theorem left_right_relation {G : Type u} [Group G] (g : G) :
    ∀ (x : G), leftRegularRepresentation g x = (rightRegularRepresentation g⁻¹ x)⁻¹ := by
  intro x
  simp [leftRegularRepresentation, rightRegularRepresentation]
  group

end CayleyTheorem

/-
## 应用示例

### 示例1：Klein四元群作为置换群

Klein四元群 V₄ = {e, a, b, c}，其中 a² = b² = c² = e，ab = c。
V₄ 同构于 S₄ 的子群 {id, (12)(34), (13)(24), (14)(23)}。

### 示例2：循环群作为置换群

循环群 Cₙ = ⟨g | gⁿ = 1⟩ 同构于 Sₙ 中由 n-轮换 (12...n) 生成的子群。

```lean
-- Cₙ 的置换表示：将生成元映射为 n-轮换 (0 1 2 ... n-1)
example (n : ℕ) : CyclicGroup n →* Perm (Fin n) where
  toFun g := {
    toFun := fun i => ⟨ (i.val + g.val) % n, Nat.mod_lt _ n.pos⟩,
    invFun := fun i => ⟨ (i.val + (n - g.val % n)) % n, Nat.mod_lt _ n.pos⟩,
    left_inv := by intro i; simp; omega,
    right_inv := by intro i; simp; omega
  }
  map_one' := by 
    ext i 
    simp
  map_mul' := by 
    intro g h 
    ext i 
    simp [add_assoc]
    omega
```

## 数学意义

Cayley定理的重要性：

1. **具体表示**：任何抽象群都可以实现为置换群
2. **存在性证明**：证明了置换群的"丰富性"
3. **计算工具**：提供了计算群论的具体方法
4. **理论统一**：连接了抽象群论和置换群论

## 与其他定理的关系

| 定理 | 关系 |
|------|------|
| Cayley定理 | 群的置换表示 |
| 拉格朗日定理 | 结合Cayley定理可得群的阶的界 |
| 第一同构定理 | Cayley嵌入的同构证明使用同构定理 |
| Sylow定理 | 用于分类给定阶的群 |

## 历史发展

- **1854**: Cayley引入群的抽象概念
- **1854**: 提出Cayley定理
- **现代**: 成为群论教学的标准内容

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `Mathlib.GroupTheory.Cayley`: Cayley定理的核心实现
- `Mathlib.GroupTheory.Perm`: 置换群的基础理论
- `Mathlib.GroupTheory.GroupAction`: 群作用的理论
- `leftRegularRepresentation`: 左正则表示
- `MulAction.toPermHom`: 群作用诱导的置换同态
-/
