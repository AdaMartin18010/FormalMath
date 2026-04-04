/-
# 范畴论基础

## 数学背景

范畴论是20世纪40年代由Eilenberg和Mac Lane创立的数学分支，
它提供了研究数学结构的统一语言。

范畴 = 对象 + 态射 + 复合 + 恒等态射

## 核心概念
- 函子与自然变换
- 极限与余极限
- 伴随函子
- 幺半范畴
- Abel范畴

## 参考
- Mac Lane, S. "Categories for the Working Mathematician"
- Awodey, S. "Category Theory"
-/

import FormalMath.Mathlib.CategoryTheory.Category.Basic
import FormalMath.Mathlib.CategoryTheory.Functor.Basic
import FormalMath.Mathlib.CategoryTheory.NatTrans
import FormalMath.Mathlib.CategoryTheory.Limits.Shapes.Terminal
import FormalMath.Mathlib.CategoryTheory.Limits.Shapes.Products
import FormalMath.Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import FormalMath.Mathlib.CategoryTheory.Adjunction.Basic
import FormalMath.Mathlib.CategoryTheory.Equivalence
import FormalMath.Mathlib.CategoryTheory.Yoneda
import FormalMath.Mathlib.CategoryTheory.Monoidal.Category
import FormalMath.Mathlib.CategoryTheory.Abelian.Basic

namespace CategoryTheory

open CategoryTheory Category Functor Limits

/-
## 范畴的定义

范畴C由以下数据组成：
1. 对象类Ob(C)
2. 对任意X,Y ∈ Ob(C)，态射集Hom(X,Y)
3. 态射复合∘ : Hom(Y,Z) × Hom(X,Y) → Hom(X,Z)
4. 恒等态射id_X ∈ Hom(X,X)

满足结合律和恒等律。
-/

-- 使用Mathlib中的Category定义
variable (C : Type u₁) [Category.{v₁} C]

/-
## 函子

函子F : C → D是保持结构的映射：
- F : Ob(C) → Ob(D)
- F : Hom(X,Y) → Hom(FX, FY)
- 保持复合和恒等态射
-/

-- 使用Mathlib中的Functor
variable {C D : Type*} [Category C] [Category D]
variable (F : C ⥤ D)

/-
## 自然变换

自然变换η : F ⇒ G是两个函子之间的"态射"：
- 对每個X ∈ Ob(C)，有η_X : F(X) → G(X)
- 满足自然性：G(f) ∘ η_X = η_Y ∘ F(f)
-/

variable (G : C ⥤ D) (η : F ⟶ G)

/-
## 自然同构

若自然变换的每个分量都是同构，则称为自然同构。
-/
def NaturalIsomorphism : Prop :=
  ∀ X : C, IsIso (η.app X)

/-
## 等价范畴

范畴C和D等价，如果存在函子F : C → D, G : D → C
和自然同构GF ≅ id_C, FG ≅ id_D。
-/
def CategoryEquivalence (C D : Type*) [Category C] [Category D] : Prop :=
  ∃ (F : C ⥤ D) (G : D ⥤ C) (η : G ⋙ F ≅ 𝟭 C) (ε : F ⋙ G ≅ 𝟭 D), True

/-
## Yoneda引理

**定理**：对于函子F : Cᵒᵖ → Set，有自然同构：
Nat(Hom(-,X), F) ≅ F(X)

这是范畴论中最基本的定理之一。
-/
theorem yoneda_lemma {C : Type*} [Category C] (F : Cᵒᵖ ⥤ Type v₁) (X : C) :
    (yoneda.obj X ⟶ F) ≃ F.obj (Opposite.op X) := by
  -- Yoneda引理的证明
  -- 构造前向映射：自然变换 → F(X)
  refine Equiv.mk 
    (fun η ↦ η.app (Opposite.op X) (𝟙 X)) 
    (fun x ↦ ⟨fun Y f ↦ F.map f x, ?_⟩) 
    ?_ 
    ?_
  · -- 证明自然性条件
    intros Y Z f
    funext g
    simp [Functor.map_comp]
  · -- 证明右逆
    funext x
    simp [yoneda_obj_obj]
  · -- 证明左逆
    funext η
    ext Y f
    have h_nat := η.naturality f
    simp [yoneda_obj_obj] at h_nat ⊢
    rw [←h_nat]
    simp

/-
## Yoneda嵌入

y : C → [Cᵒᵖ, Set], X ↦ Hom(-,X)
是满忠实的。
-/
theorem yoneda_embedding_fully_faithful {C : Type*} [Category C] :
    FullyFaithful (yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁) := by
  -- 利用Yoneda引理证明Yoneda嵌入是满忠实的
  refine ⟨fun X Y ↦ ⟨?_, ?_, ?_⟩⟩
  · -- 前向映射
    intro f
    exact yoneda.map f
  · -- 左逆
    intro f
    ext X g
    simp [yoneda]
  · -- 右逆  
    intro f
    simp [yoneda]

/-
## 极限

图表D : J → C的极限是锥的终对象。
-/
variable {J : Type*} [Category J]

/-
## 积（Product）

X × Y是图表{1,2} → C的极限。
-/
def IsProduct {C : Type*} [Category C] (X Y P : C) 
    (π₁ : P ⟶ X) (π₂ : P ⟶ Y) : Prop :=
  ∀ (Z : C) (f : Z ⟶ X) (g : Z ⟶ Y), 
    ∃! h : Z ⟶ P, h ≫ π₁ = f ∧ h ≫ π₂ = g

/-
## 始对象与终对象

- 始对象I：对任意X，存在唯一的I → X
- 终对象T：对任意X，存在唯一的X → T
-/
def IsInitial {C : Type*} [Category C] (I : C) : Prop :=
  ∀ X : C, Nonempty (Unique (I ⟶ X))

def IsTerminal {C : Type*} [Category C] (T : C) : Prop :=
  ∀ X : C, Nonempty (Unique (X ⟶ T))

/-
## 伴随函子

F ⊣ G表示F是G的左伴随：
Hom(FX, Y) ≅ Hom(X, GY)
-/
structure Adjunction (F : C ⥤ D) (G : D ⥤ C) where
  homEquiv : ∀ (X : C) (Y : D), (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)
  unit : 𝟭 C ⟶ F ⋙ G
  counit : G ⋙ F ⟶ 𝟭 D
  h_triangle₁ : ∀ X, unit.app X ≫ (G.map (counit.app (F.obj X))) = 𝟙 X
  h_triangle₂ : ∀ Y, F.map (unit.app (G.obj Y)) ≫ counit.app Y = 𝟙 Y

notation:max F " ⊣ " G => Adjunction F G

/-
## 伴随的单位与余单位

- 单位η : id_C → GF
- 余单位ε : FG → id_D
-/
def adjunction_unit {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    𝟭 C ⟶ F ⋙ G := adj.unit

def adjunction_counit {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    G ⋙ F ⟶ 𝟭 D := adj.counit

/-
## 伴随的唯一性

若F ⊣ G且F ⊣ G'，则G ≅ G'
-/
theorem right_adjoint_unique {F : C ⥤ D} {G G' : D ⥤ C}
    (adj₁ : F ⊣ G) (adj₂ : F ⊣ G') : G ≅ G' := by
  -- 利用Yoneda引理证明右伴随的唯一性
  refine NatIso.ofComponents (fun Y ↦ ?_) ?_
  · -- 构造G(Y) ≅ G'(Y)
    refine ⟨adj₂.homEquiv _ Y (adj₁.counit.app Y), 
            adj₁.homEquiv _ Y (adj₂.counit.app Y), ?_, ?_⟩
    · -- 证明右逆
      simp [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit]
      rw [← adj₁.h_triangle₂, Functor.map_comp, Category.assoc]
      simp
    · -- 证明左逆
      simp [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit]
      rw [← adj₂.h_triangle₂, Functor.map_comp, Category.assoc]
      simp
  · -- 证明自然性
    intros Y Z f
    simp [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit]
    rw [← Category.assoc, ← Functor.map_comp]
    simp

/-
## 单态射与满态射

- 单态射：左可消去
- 满态射：右可消去
-/
def IsMonomorphism {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) : Prop :=
  ∀ {Z : C} (g₁ g₂ : Z ⟶ X), g₁ ≫ f = g₂ ≫ f → g₁ = g₂

def IsEpimorphism {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) : Prop :=
  ∀ {Z : C} (g₁ g₂ : Y ⟶ Z), f ≫ g₁ = f ≫ g₂ → g₁ = g₂

/-
## 核与余核

- 核ker(f)：f ∘ k = 0的泛性拉回
- 余核coker(f)：q ∘ f = 0的泛性推出
-/
structure Kernel {C : Type*} [Category C] [HasZeroMorphisms C] 
    {X Y : C} (f : X ⟶ Y) where
  object : C
  morphism : object ⟶ X
  h_comp : morphism ≫ f = 0
  h_univ : ∀ (Z : C) (k : Z ⟶ X), k ≫ f = 0 → 
    ∃! h : Z ⟶ object, h ≫ morphism = k

/-
## 幺半范畴

具有张量积⊗和单位对象I的范畴。
用于表示线性代数和量子力学。
-/
class MonoidalCategory (C : Type*) extends Category C where
  tensorObj : C → C → C
  tensorHom : ∀ {X₁ Y₁ X₂ Y₂ : C}, (X₁ ⟶ Y₁) → (X₂ ⟶ Y₂) → 
    (tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂)
  associator : ∀ X Y Z : C, tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z)
  leftUnitor : ∀ X : C, tensorObj (tensorUnit : C) X ≅ X
  rightUnitor : ∀ X : C, tensorObj X tensorUnit ≅ X
  tensorUnit : C
  -- 满足结合律和么元律的相容性条件（pentagon和triangle等式）
  pentagon : ∀ W X Y Z : C, 
    (tensorHom (associator W X Y).hom (𝟙 Z)) ≫ (associator W (tensorObj X Y) Z).hom ≫ 
    (tensorHom (𝟙 W) (associator X Y Z).hom) = 
    (associator (tensorObj W X) Y Z).hom ≫ (associator W X (tensorObj Y Z)).hom
  triangle : ∀ X Y : C,
    (associator X tensorUnit Y).hom ≫ tensorHom (𝟙 X) (leftUnitor Y).hom = 
    tensorHom (rightUnitor X).hom (𝟙 Y)

/-
## Abel范畴

具有丰富结构的范畴，是同调代数的基础：
- 每个态射有核和余核
- 单态射是其余核的核
- 满态射是其核的余核
- 任何态射可分解为满射后接单射
-/
class AbelianCategory (C : Type*) extends Category C where
  hasZeroObject : HasZeroObject C
  hasZeroMorphisms : HasZeroMorphisms C
  hasBinaryProducts : HasBinaryProducts C
  hasBinaryCoproducts : HasBinaryCoproducts C
  hasKernels : HasKernels C
  hasCokernels : HasCokernels C
  normalMono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], 
    NormalMono f
  normalEpi : ∀ {X Y : C} (f : X ⟶ Y) [Epi f], 
    NormalEpi f

end CategoryTheory
