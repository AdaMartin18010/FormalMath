import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Basic

/-! 
# 代数几何示例

对应的FormalMath文档：
- docs/13-代数几何/03-代数几何深度扩展版.md
- docs/04-几何学/05-代数几何.md

对应的Mathlib4模块：
- Mathlib.AlgebraicGeometry.Scheme
- Mathlib.AlgebraicGeometry.Spec
- Mathlib.AlgebraicGeometry.StructureSheaf
- Mathlib.AlgebraicGeometry.AffineScheme
- Mathlib.RingTheory.Ideal.Basic

## 核心定义

代数几何将交换代数与几何直观结合。
-/ 

/-! 
## 概形（Scheme）

概形是代数几何的基本对象，由局部仿射概形粘合而成。
-/

section Scheme

-- 概形定义
#check Scheme

-- 概形的结构层
example (X : Scheme) : TopCat.Sheaf CommRingCat X.carrier := X.sheaf

-- 仿射概形
#check AffineScheme

-- Spec构造：从环构造仿射概形
example (R : CommRingCat) : AffineScheme := 
  AffineScheme.Spec R

-- 概形的态射
example (X Y : Scheme) : Type _ := X ⟶ Y

end Scheme

/-! 
## 素谱（Spec）

环的素谱是其素理想集，带有Zariski拓扑。
-/

section Spec

-- 素谱
example (R : CommRingCat) : Type _ := PrimeSpectrum R

-- 素谱上的Zariski拓扑
example (R : CommRingCat) : TopologicalSpace (PrimeSpectrum R) := by
  infer_instance

-- 闭集：V(I) = {P ⊇ I}
example (R : CommRingCat) (I : Ideal R) : Set (PrimeSpectrum R) := 
  PrimeSpectrum.zeroLocus I

-- 结构层：在素理想处的茎是局部环
example (R : CommRingCat) (P : PrimeSpectrum R) : 
    CommRingCat := CommRingCat.of (Localization.AtPrime P.asIdeal)

-- 全局截面环
example (R : CommRingCat) : 
    Γ(AffineScheme.Spec R, ⊤) ≅ R := by
  -- 这是Spec的基本性质
  exact Scheme.Γ_Spec_iso R

end Spec

/-! 
## 层与茎

概形配备结构层，局部信息决定整体。
-/

section Sheaves

-- 预层
example (X : Type*) [TopologicalSpace X] (C : Type*) [Category C] : 
    Type _ := TopCat.Presheaf C X

-- 层
example (X : Type*) [TopologicalSpace X] (C : Type*) [Category C] : 
    Type _ := TopCat.Sheaf C X

-- 茎（stalk）
example {X : Type*} [TopologicalSpace X] {C : Type*} [Category C] 
    (F : TopCat.Presheaf C X) (x : X) : C := F.stalk x

-- 截面（section）
example {X : Type*} [TopologicalSpace X] {C : Type*} [Category C] 
    (F : TopCat.Presheaf C X) (U : Opens X) : C := F.obj (op U)

-- 限制映射
example {X : Type*} [TopologicalSpace X] {C : Type*} [Category C] 
    (F : TopCat.Presheaf C X) {U V : Opens X} (h : V ≤ U) : 
    F.obj (op U) ⟶ F.obj (op V) := F.map (homOfLE h).op

end Sheaves

/-! 
## 环的局部化

局部化是代数几何的核心操作。
-/

section Localization

-- 乘法子集
example {R : Type*} [CommRing R] : Type _ := Submonoid R

-- 局部化
example {R : Type*} [CommRing R] (S : Submonoid R) : CommRing _ := 
  Localization S

-- 素理想的局部化（局部环）
example {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] : 
    CommRing _ := Localization.AtPrime P

-- 局部环
example {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] : 
    LocalRing (Localization.AtPrime P) := by
  infer_instance

-- 最大理想是P的扩展
example {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] : 
    Ideal (Localization.AtPrime P) := 
  IsLocalization.AtPrime.localRing P

end Localization

/-! 
## 模与层

模的层化是代数几何中的重要构造。
-/

section Modules

-- 模范畴
example (R : Type*) [Ring R] : Type _ := ModuleCat R

-- 模的层
example {X : Scheme} : Type _ := QCohModule X

-- 拟凝聚层
example (X : Scheme) : Type _ := Scheme.QuasiCoherentSheaf X

-- 结构层是拟凝聚的
example (X : Scheme) : Scheme.QuasiCoherentSheaf X := 
  { val := X.sheaf
    -- 满足拟凝聚条件
    property := sorry }

end Modules

/-! 
## 射影概形

Proj构造，从分次环构造射影概形。
-/

section ProjectiveSchemes

-- 分次环
example (R : Type*) [CommRing R] : Type _ := GradedRing R

-- 齐次理想
example {R : Type*} [CommRing R] [GradedRing R] : Type _ := 
  HomogeneousIdeal (fun i => GradedRing.proj R i)

-- Proj构造
-- example {R : Type*} [CommRing R] [GradedRing R] : Scheme := 
--   ProjectiveSpectrum R

-- 射影空间
example (n : ℕ) (R : CommRingCat) : Scheme := 
  ProjectiveSpace n R

end ProjectiveSchemes

/-! 
## 概形的性质

各种几何性质的代数刻画。
-/

section Properties

-- 分离概形
example (X : Scheme) : Prop := 
  SeparatedScheme X

-- 真概形（proper）
example (X : Scheme) : Prop := 
  ProperScheme X

-- 光滑概形
example (X : Scheme) : Prop := 
  SmoothScheme X

-- 有限型
example (X : Scheme) : Prop := 
  LocallyOfFiniteType X

-- 仿射概形的判定
example (X : Scheme) : Prop := 
  IsAffine X

end Properties

/-! 
## 示例：仿射概形 Spec ℤ

整数环的素谱是最简单的概形之一。
-/

section ExampleSpecZ

-- Spec ℤ
example : Scheme := AffineScheme.SchemeSpec (CommRingCat.of ℤ)

-- Spec ℤ的点对应于素数
example : PrimeSpectrum (CommRingCat.of ℤ) ≃ {p : ℕ // p.Prime} ⊕ {⊥} := by
  -- 非零素理想对应素数，零理想对应泛点
  sorry

-- Zariski拓扑：闭集是有限个点
example : TopologicalSpace (PrimeSpectrum (CommRingCat.of ℤ)) := by
  infer_instance

end ExampleSpecZ

/-! 
## 示例：仿射概形 Spec k[X]

多项式环的素谱。
-/

section ExampleSpecKX

variable (k : Type*) [Field k]

-- Spec k[X]
example : Scheme := 
  AffineScheme.SchemeSpec (CommRingCat.of (Polynomial k))

-- Spec k[X]的点：
-- 1. 闭点：最大理想 (X - a)，对应于 a ∈ k
-- 2. 泛点：零理想 (0)

-- 如果k是代数闭域，闭点与k的元素一一对应
example [IsAlgClosed k] : 
    {P : PrimeSpectrum (CommRingCat.of (Polynomial k)) // P.asIdeal.IsMaximal} 
      ≃ k := by
  sorry

end ExampleSpecKX

/-! 
## 层上同调

层上同调是代数几何的重要工具。
-/

section SheafCohomology

-- 整体截面函子
example (X : Scheme) : Functor (TopCat.Sheaf Ab X) Ab := 
  (TopCat.Presheaf.evaluation (X := X) ⊤).rightOp ⋙ forget _

-- 层上同调（导出函子）
-- example (X : Scheme) (n : ℕ) : Functor (TopCat.Sheaf Ab X) Ab := 
--   Sheaf.cohomology n

-- Čech上同调
-- example (X : Scheme) (U : OpenCover X) (n : ℕ) : 
--     TopCat.Sheaf Ab X → Ab := 
--   Cech.cohomology U n

end SheafCohomology

/-! 
## 练习

1. 证明：对于交换环R，Spec R是拟紧的（quasi-compact）。

2. 描述Spec ℝ[X]/(X²)的几何（包括幂零元）。

3. 证明：概形态射 f: X → Y 是仿射的当且仅当对于Y的任意仿射开集U，
   f⁻¹(U)也是仿射的。

4. 设k是代数闭域，描述射影直线 ℙ¹_k 的开覆盖。

5. 证明：如果X是整概形（integral scheme），那么结构层是常值层（在泛点处）。

-/ 

section Exercises

-- 练习1的提示：使用Zariski拓扑的定义和素理想的性质
example (R : CommRingCat) : CompactSpace (PrimeSpectrum R) := by
  infer_instance

-- 练习4的框架：射影直线的标准覆盖
example (k : Type*) [Field k] : 
    (ProjectiveSpace 1 (CommRingCat.of k)).toScheme.OpenCover := by
  sorry

end Exercises
