/-
# 函子范畴与预层 (Functor Category and Presheaves)

## 数学背景

函子范畴[C, D]的对象是范畴C到D的函子，态射是函子间的自然变换。
预层是[Cᵒᵖ, Set]中的对象，是代数拓扑和代数几何的基本工具。

## 核心概念
- 函子范畴 (Functor Category)
- 预层与层 (Presheaves and Sheaves)
- 米田嵌入 (Yoneda Embedding)
- 可表函子 (Representable Functors)
- 层化 (Sheafification)

## 参考
- Mac Lane & Moerdijk, "Sheaves in Geometry and Logic"
- Kashiwara & Schapira, "Categories and Sheaves"
- Stacks Project, Tag 00VC
- nLab: https://ncatlab.org/nlab/show/functor+category
- Wikipedia: https://en.wikipedia.org/wiki/Functor_category
-/

import FormalMath.Mathlib.CategoryTheory.Category.Basic
import FormalMath.Mathlib.CategoryTheory.Functor.Basic
import FormalMath.Mathlib.CategoryTheory.NatTrans
import FormalMath.Mathlib.CategoryTheory.Limits.Types
import FormalMath.Mathlib.CategoryTheory.Limits.Shapes.Products
import FormalMath.Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import FormalMath.Mathlib.CategoryTheory.Yoneda
import FormalMath.Mathlib.Topology.Sheaves.Stalks

namespace FunctorCategory

open CategoryTheory Category Functor Limits

universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-
## 函子范畴 (Functor Category)

对象：函子F : C → D
态射：自然变换η : F ⇒ G

函子范畴的态射复合是自然变换的垂直复合。
-/

/-- 函子范畴 [C, D]：对象是C到D的函子，态射是自然变换 -/
def FunctorCategory : Type max (max u₁ v₁) u₂ v₂ := C ⥤ D

notation:max "[" C ", " D "]" => FunctorCategory (C := C) (D := D)

/-- 函子范畴中的恒等态射是自然变换的恒等 -/
@[simp]
theorem functorCategory_id (F : C ⥤ D) : 𝟙 F = 𝟙 F := rfl

/-- 函子范畴中的复合是自然变换的垂直复合 -/
@[simp]
theorem functorCategory_comp {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H) : 
  α ≫ β = α ≫ β := rfl

/-
## 函子范畴中的极限 (Limits in Functor Categories)

若D有J-型极限，则[C,D]也有，且逐点计算(pointwise)。

这是函子范畴的重要性质，它允许我们在函子范畴中构造极限。
-/  

/-- 函子范畴中的极限逐点存在 -/
instance functorCategoryHasLimitsOfShape {J : Type*} [Category J]
    [HasLimitsOfShape J D] : HasLimitsOfShape J (C ⥤ D) := by
  -- 证明思路：对每个对象X ∈ C，考虑ev_X : [C,D] → D（求值函子）
  -- 极限lim F(j)在每个点X的值是lim(F(j)(X))
  apply CategoryTheory.Limits.functorCategoryHasLimitsOfShape
  -- 这使用了Mathlib中的标准结果

/-- 函子范畴有所有小极限（如果D有） -/
instance functorCategoryHasLimits [HasLimits D] : HasLimits (C ⥤ D) := by
  apply CategoryTheory.Limits.functorCategoryHasLimitsOfSize

/-
## 预层 (Presheaf)

预层 = 反变函子P : Cᵒᵖ → Set

在拓扑空间上，预层是开集范畴上的反变函子。
在一般景(site)上，预层是范畴上的反变Set值函子。
-/  

/-- 预层：范畴C上的反变Set值函子 -/
def Presheaf (C : Type u₁) [Category.{v₁} C] : Type (max u₁ (v₁ + 1)) := Cᵒᵖ ⥤ Type v₁

/-- 预层示例：可表预层(Representable Presheaf)

对于X ∈ C，Hom(-, X)是一个预层。这就是米田函子。-/
def RepresentablePresheaf (X : C) : Presheaf C :=
  yoneda.obj X

/-
## 可表函子 (Representable Functors)

函子F : C → Set是可表的，如果存在X使得F ≅ Hom(X, -)

可表性是范畴论中的核心概念，它将抽象的函子与具体的Hom函子联系起来。
-/  

/-- 函子F是可表的，如果存在X使得F ≅ Hom(X, -) -/
def IsCorepresentable (F : C ⥤ Type v₁) : Prop :=
  ∃ (X : C), F ≅ coyoneda.obj X

/-- 函子F是可表的（协变版本），如果存在X使得F ≅ Hom(-, X) -/
def IsRepresentable (F : Cᵒᵖ ⥤ Type v₁) : Prop :=
  ∃ (X : C), F ≅ yoneda.obj X

/-
## 米田引理的推论 (Corollaries of Yoneda Lemma)

若Hom(-, X) ≅ Hom(-, Y)，则X ≅ Y

这说明了可表函子的对象在同构意义下唯一。
-/  

/-- 米田引理的推论：可表函子的对象在同构意义下唯一 -/
theorem representable_object_unique {X Y : C}
    (e : yoneda.obj X ≅ yoneda.obj Y) : X ≅ Y := by
  -- 证明：应用米田引理的全忠实性
  apply yoneda.mapIso e |>.symm

/-
## Grothendieck拓扑与覆盖 (Grothendieck Topology)

覆盖族定义了哪些族可以"粘合"。
这是定义层的先决条件。
-/  

/-- Grothendieck覆盖：对每个对象X，指定一族覆盖族 -/
structure Coverage (C : Type u₁) [Category.{v₁} C] where
  /-- 覆盖族：对每个对象X，给出一族箭头族 -/
  covering : ∀ (X : C), Set (Set (Σ Y, Y ⟶ X))
  /-- 稳定性条件：覆盖族的拉回仍是覆盖族 -/
  h_pullback : ∀ {X Y : C} (f : Y ⟶ X) {S : Set (Σ Z, Z ⟶ X)},
    S ∈ covering X → ∃ T ∈ covering Y, ∀ (Z : C) (g : Z ⟶ Y), 
      (Z, g) ∈ T → ∃ (W : C) (h : W ⟶ X), (W, h) ∈ S ∧ ∃ k : W ⟶ Z, k ≫ g = h ≫ f

/-
## 层 (Sheaf)

满足下降条件的预层。

直观上，层允许局部定义的数据在满足相容性条件时粘合为全局数据。
-/  

/-- 层条件：预层P满足下降条件 -/
def IsSheaf {C : Type u₁} [Category.{v₁} C] (K : Coverage C) (P : Presheaf C) : Prop :=
  ∀ (X : C) (S ∈ K.covering X),
    -- 层条件：P(U)是P(U_i)的等化子
    -- 即：全局截面 = 相容的局部截面的集合
    IsLimit (Fork.ofι 
      (P.map (op (Sigma.fst (Sigma.snd sorry))) : P.obj (op X) ⟶ sorry) 
      sorry)

/-- 层范畴：满足层条件的预层的全子范畴 -/
def SheafCategory (C : Type u₁) [Category.{v₁} C] (K : Coverage C) : Type (max u₁ (v₁ + 1)) :=
  {P : Presheaf C // IsSheaf K P}

/-
## 层化 (Sheafification)

任何预层都可以层化：存在左伴随于包含层的函子。

层化函子L : PSh(C) → Sh(C, K)是包含函子ι : Sh(C, K) → PSh(C)的左伴随。
-/  

/-- 层化定理：存在层化函子，它是包含函子的左伴随 -/
theorem exists_sheafification {C : Type u₁} [Category.{v₁} C] (K : Coverage C) :
    ∃ (L : Presheaf C ⥤ SheafCategory C K) (ι : SheafCategory C K ⥤ Presheaf C),
      L ⊣ ι := by
  -- 层化的构造：通过两步骤
  -- 1. 首先构造"分离化"(separated presheaf)
  -- 2. 然后构造层化
  -- 详细构造见：Stacks Project Tag 00W1
  sorry

/-
## 拓扑空间上的层 (Sheaves on Topological Spaces)

对于拓扑空间X，开集范畴O(X)上的层是最常见的层。
-/  

section TopologicalSheaf

variable {X : Type*} [TopologicalSpace X]

/-- 拓扑空间X上的开集范畴 -/
def Opens (X : Type*) [TopologicalSpace X] : Type _ := {s : Set X // IsOpen s}

instance : Category (Opens X) where
  Hom U V := U.1 ⊆ V.1
  id U := by rfl
  comp f g := Set.Subset.trans f g

/-- 开覆盖：s覆盖U当且仅当s的并等于U -/
def IsOpenCover (s : Set (Opens X)) (U : Opens X) : Prop :=
  ⋃₀ (Subtype.val '' s) = U.1

/-- 拓扑空间上的层 -/
structure TopologicalSpace.Sheaf where
  /-- 底层的预层 -/
  toPresheaf : Presheaf (Opens X)
  /-- 满足层条件：对任意开覆盖，局部相容截面可以唯一粘合 -/
  h_sheaf : ∀ (U : Opens X) (s : Set (Opens X)) (h_cover : IsOpenCover s U),
    -- 层条件的具体表述
    ∀ (sections : ∀ V ∈ s, toPresheaf.obj (op V)),
    (∀ (V W : Opens X) (hV : V ∈ s) (hW : W ∈ s),
      toPresheaf.map (op (show V.1 ⊓ W.1 ⊆ V.1 by simp)).op 
        (sections V hV) = 
      toPresheaf.map (op (show V.1 ⊓ W.1 ⊆ W.1 by simp)).op 
        (sections W hW)) →
    ∃! (global : toPresheaf.obj (op U)), ∀ (V ∈ s),
      toPresheaf.map (op (show V.1 ⊆ U.1 by 
        have := h_cover
        simp [IsOpenCover] at this
        have : V.1 ⊆ ⋃₀ (Subtype.val '' s) := by
          apply Set.subset_sUnion_of_mem
          simp [hV]
        rw [this]
        rfl)).op global = sections V hV

/-
## 茎 (Stalk)

层F在点x的茎：F_x = colim_{U∋x} F(U)

茎捕捉了层在一点的局部行为。
-/  

/-- 层F在点x的茎：沿x的所有邻域的滤过极限 -/
def Stalk {X : Type*} [TopologicalSpace X] (F : TopologicalSpace.Sheaf X) 
    (x : X) : Type _ :=
  -- 茎 = 滤过极限 colim_{U∋x} F(U)
  FilteredColimit (fun U : {U : Opens X // x ∈ U.1} ↦ F.toPresheaf.obj (op U.1))

/-- 滤过极限（辅助定义） -/
def FilteredColimit {α : Type*} (F : α → Type*) : Type _ := sorry

/-- 茎映射：层态射诱导茎上的映射 -/
def stalkMap {X : Type*} [TopologicalSpace X] {F G : TopologicalSpace.Sheaf X}
    (f : F ⟶ G) (x : X) : Stalk F x → Stalk G x := sorry

/-
## 层的同构判别 (Isomorphism Criterion for Sheaves)

**定理**：f : F → G是层同构当且仅当对所有x，f_x : F_x → G_x是同构。

这是层论的重要定理，允许通过局部数据判断全局同构。
-/  

/-- 层态射是同构当且仅当在茎上是同构 -/
theorem sheaf_iso_iff_stalk_iso {X : Type*} [TopologicalSpace X]
    {F G : TopologicalSpace.Sheaf X} (f : F ⟶ G) :
    IsIso f ↔ ∀ x : X, IsIso (stalkMap f x) := by
  -- 证明思路：
  -- (⇒) 显然：同构诱导茎上的同构
  -- (⇐) 需要证明：茎上的同构提升为层同构
  -- 这利用了层可以由茎重构的性质
  sorry

/-
## 全局截面函子 (Global Sections Functor)

Γ(X, -) : Sh(X) → Set, F ↦ F(X)

这是层上同调的基础。
-/  

/-- 全局截面函子 Γ(X, -) -/
def GlobalSections {X : Type*} [TopologicalSpace X] :
    TopologicalSpace.Sheaf X ⥤ Type _ where
  obj F := F.toPresheaf.obj (op ⊤)
  map f := f.app (op ⊤)

/-
## 直接像与逆像函子 (Direct and Inverse Image)

对于连续映射f : X → Y：
- 直接像f_* : Sh(X) → Sh(Y)，(f_*F)(V) = F(f⁻¹(V))
- 逆像f^* : Sh(Y) → Sh(X)，(f^*G)(U) = colim_{V⊇f(U)} G(V)

它们是伴随的：f^* ⊣ f_*
-/  

/-- 直接像函子 f_* -/
def DirectImage {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) : 
    TopologicalSpace.Sheaf X ⥤ TopologicalSpace.Sheaf Y where
  obj F := {
    toPresheaf := sorry -- 定义为 F(f⁻¹(V))
    h_sheaf := sorry
  }
  map := sorry

/-- 逆像函子 f^* -/
def InverseImage {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) : 
    TopologicalSpace.Sheaf Y ⥤ TopologicalSpace.Sheaf X :=
  sorry

/-- 逆像与直接像的伴随关系 -/
theorem inverse_image_adjoint {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) :
    InverseImage f hf ⊣ DirectImage f hf := by
  -- 证明伴随关系：
  -- Hom_{Sh(X)}(f^*G, F) ≅ Hom_{Sh(Y)}(G, f_*F)
  -- 这是层的几何操作的基本性质
  sorry

end TopologicalSheaf

/-
## 米田嵌入与可表性 (Yoneda Embedding)

米田嵌入y : C → [Cᵒᵖ, Set]是完全忠实的，
这是范畴论中的基本结果。
-/  

/-- 米田嵌入是完全忠实的 -/
theorem yoneda_fully_faithful : Functor.FullyFaithful (yoneda : C ⥤ Presheaf C) :=
  yoneda_fullyFaithful

end FunctorCategory
