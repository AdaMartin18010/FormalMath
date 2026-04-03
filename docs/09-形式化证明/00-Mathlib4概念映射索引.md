---
msc_primary: "68V20"
msc_secondary: ['03B35', '68T99', '00A99']
mathlib4_version: "v4.29.0"
mathlib4_latest: "v4.29.0"
lean4_version: "v4.29.0"
last_updated: "2026-04-03"
next_review: "2026-07-03"
---

# Mathlib4概念映射索引

**Mathlib4版本**: v4.29.0
**Lean4版本**: v4.29.0
**最后更新**: 2026-04-03

---

## 📢 2024-2025最新进展

### Mathlib4 v4.29.0重要更新

**发布日期**: 2026年3月

#### 代数几何新进展

- **Motivic上同调**: 混合特征概形的motivic上同调理论相关形式化进展
- **层上同调**: `Mathlib.AlgebraicGeometry.Scheme`模块持续增强
- **概形理论**: 素谱、Zariski拓扑、局部环化空间等核心概念完善

#### 数论新进展

- **HasFiniteQuotients类**: 新增具有有限商的交换环类
  - 证明：若`R`有有限商，则其Krull维度≤1
  - 证明：若`R`有有限商，则它是Noetherian环
  - 若`S`是域且是有限`R`-模，则`S`有有限商
- **有限域**: `Mathlib.FieldTheory.Finite.Basic`持续完善

#### 分析学新进展

- **连续多线性映射**: 从赋范空间推广到拓扑向量空间
- **实数平方根**: API扩展
- **连续性自动化**: `fun_prop`等自动化证明增强

### 与项目相关的arXiv论文（2024-2025）

| 论文 | arXiv编号 | 与Mathlib4关系 |
|------|-----------|----------------|
| Motivic Cohomology of Mixed Characteristic Schemes | arXiv:2412.06635 | 代数几何高级主题形式化 |
| Enhancement for Categories and Homotopical Algebra | arXiv:2409.17489 | 同调代数、导出范畴 |
| Ext Groups in Homotopy Type Theory | arXiv:2305.09639 | 形式化数学前沿 |

---

---

## 📋 概述

本文档建立了FormalMath数学概念与Mathlib4形式化代码之间的深度映射关系。Mathlib4是Lean4数学库，包含超过11.5万个定义和23.2万个定理，覆盖现代数学的主要分支。

**Mathlib4资源链接**:

- [Mathlib4官方文档](https://leanprover-community.github.io/mathlib4_docs/)
- [Mathlib4 GitHub仓库](https://github.com/leanprover-community/mathlib4)
- [Mathlib4 API搜索](https://leanprover-community.github.io/mathlib4_docs/search.html)

---

## 📚 按数学分支组织的概念映射

### 一、基础数学与集合论

| 数学概念 | FormalMath文档 | Mathlib4模块 | 核心定义 | 关键定理 |
|---------|---------------|--------------|---------|---------|
| **集合** | `docs/01-基础数学/集合论/01-集合论基础-深度扩展版.md` | `Mathlib.Data.Set.Basic` | `Set`, `Set.mem`, `Set.subset` | `Set.mem_union`, `Set.mem_inter` |
| **函数** | `docs/01-基础数学/集合论/03-函数与映射-深度扩展版.md` | `Mathlib.Logic.Function.Basic` | `Function.Injective`, `Function.Surjective` | `Function.injective_iff`, `Function.surjective_iff` |
| **等价关系** | `docs/01-基础数学/集合论/04-关系与等价-深度扩展版.md` | `Mathlib.Init.Core` | `Equiv`, `Equivalence` | `Quotient.sound`, `Quotient.lift` |
| **基数** | `docs/01-基础数学/集合论/05-基数与序数-深度扩展版.md` | `Mathlib.SetTheory.Cardinal.Basic` | `Cardinal`, `Cardinal.mk` | `Cardinal.add_def`, `Cardinal.mul_def` |
| **序数** | `docs/01-基础数学/集合论/05-基数与序数-深度扩展版.md` | `Mathlib.SetTheory.Ordinal.Basic` | `Ordinal`, `Ordinal.type` | `Ordinal.add_assoc`, `Ordinal.mul_assoc` |
| **自然数** | `docs/01-基础数学/集合论/ZFC公理体系完整形式化-自然数构造详细版.md` | `Mathlib.Data.Nat.Basic` | `Nat`, `Nat.zero`, `Nat.succ` | `Nat.add_comm`, `Nat.mul_comm` |
| **整数** | `docs/01-基础数学/集合论/ZFC公理体系完整形式化-第二部分：整数构造.md` | `Mathlib.Data.Int.Basic` | `Int`, `Int.ofNat` | `Int.add_comm`, `Int.mul_comm` |
| **有理数** | `docs/01-基础数学/集合论/ZFC公理体系完整形式化-第三部分：有理数构造.md` | `Mathlib.Data.Rat.Basic` | `Rat`, `Rat.mk` | `Rat.add_comm`, `Rat.mul_comm` |
| **实数** | `docs/01-基础数学/集合论/ZFC公理体系完整形式化-第四部分：实数构造.md` | `Mathlib.Data.Real.Basic` | `Real` | `Real.add_comm`, `Real.complete` |

#### 集合论代码示例

```lean
import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic

-- 集合的基本操作
#check Set.univ          -- 全集
#check Set.empty         -- 空集
#check Set.union         -- 并集
#check Set.inter         -- 交集
#check Set.compl         -- 补集

-- 集合包含关系
example (A B : Set ℕ) : A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B := by
  rfl

-- 德摩根定律
example (A B : Set ℕ) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  simp [Set.mem_compl_iff, Set.mem_union, Set.mem_inter]
```

---

### 二、代数结构

#### 2.1 群论

| 数学概念 | FormalMath文档 | Mathlib4模块 | 核心定义 | 关键定理 |
|---------|---------------|--------------|---------|---------|
| **群** | `docs/02-代数结构/02-核心理论/群论/01-群论-国际标准深度扩展版.md` | `Mathlib.Algebra.Group.Basic` | `Group`, `GroupHom` | `mul_one`, `one_mul`, `mul_inv_cancel` |
| **子群** | `docs/02-代数结构/02-核心理论/群论/01-群论-深度扩展版.md` | `Mathlib.GroupTheory.Subgroup.Basic` | `Subgroup`, `Subgroup.normal` | `Subgroup.mul_mem`, `Subgroup.inv_mem` |
| **商群** | `docs/02-代数结构/02-核心理论/群论/01-群论-深度扩展版.md` | `Mathlib.GroupTheory.QuotientGroup` | `QuotientGroup.quotient` | `QuotientGroup.mk`, `QuotientGroup.lift` |
| **群同态** | `docs/02-代数结构/02-核心理论/群论/01-群论-深度扩展版.md` | `Mathlib.Algebra.Hom.Group` | `MonoidHom`, `MulHom` | `MonoidHom.comp`, `MonoidHom.id` |
| **同构定理** | `docs/00-核心概念理解三问/11-核心定理多表征/02-第一同构定理-五种表征.md` | `Mathlib.GroupTheory.QuotientGroup` | `QuotientGroup.quotientKerEquivRange` | `第一同构定理` |
| **Sylow定理** | `docs/00-核心概念理解三问/11-核心定理多表征/38-Sylow定理-五种表征.md` | `Mathlib.GroupTheory.Sylow` | `Sylow`, `IsPGroup` | `Sylow.exists_subgroup_card_pow_prime` |
| **Lagrange定理** | `docs/00-核心概念理解三问/11-核心定理多表征/01-Lagrange定理-五种表征.md` | `Mathlib.GroupTheory.Coset` | `Subgroup.index` | `Subgroup.index_mul_card` |

#### 群论代码示例

```lean
import Mathlib.Algebra.Group.Basic
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.QuotientGroup

-- 群的定义检查
#check Group

-- 子群示例：偶数子群
example : AddSubgroup ℤ where
  carrier := Set.range (2 * · : ℤ → ℤ)
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    use a + b
    ring
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := by
    rintro _ ⟨a, rfl⟩
    use -a
    ring

-- Lagrange定理：有限子群的阶整除群的阶
open Fintype in
example (G : Type*) [Group G] [Fintype G] (H : Subgroup G) :
    card H ∣ card G := by
  exact ⟨H.index, by rw [Subgroup.index_mul_card]⟩
```

#### 2.2 环论

| 数学概念 | FormalMath文档 | Mathlib4模块 | 核心定义 | 关键定理 |
|---------|---------------|--------------|---------|---------|
| **环** | `docs/02-代数结构/02-核心理论/环论/01-环论-国际标准深度扩展版.md` | `Mathlib.Algebra.Ring.Basic` | `Ring`, `CommRing` | `add_mul`, `mul_add`, `zero_mul` |
| **理想** | `docs/02-代数结构/02-核心理论/环论/01-环论-深度扩展版.md` | `Mathlib.RingTheory.Ideal.Basic` | `Ideal`, `IsPrime`, `IsMaximal` | `Ideal.add_mem`, `Ideal.mul_mem_left` |
| **商环** | `docs/02-代数结构/02-核心理论/环论/01-环论-深度扩展版.md` | `Mathlib.RingTheory.Ideal.Quotient` | `Ideal.Quotient` | `Ideal.Quotient.mk`, `Ideal.Quotient.lift` |
| **整环** | `docs/02-代数结构/02-核心理论/环论/01-环论-深度扩展版.md` | `Mathlib.Algebra.Ring.Basic` | `IsDomain` | `IsDomain.mul_left_cancel` |
| **域** | `docs/02-代数结构/02-核心理论/域论/01-域论-国际标准深度扩展版.md` | `Mathlib.Algebra.Field.Basic` | `Field`, `FieldHom` | `inv_mul_cancel`, `mul_inv_cancel` |
| **PID** | `docs/02-代数结构/02-核心理论/环论/01-环论-深度扩展版.md` | `Mathlib.RingTheory.PrincipalIdealDomain` | `PrincipalIdealRing` | `to_uniqueFactorizationMonoid` |
| **UFD** | `docs/02-代数结构/02-核心理论/环论/01-环论-深度扩展版.md` | `Mathlib.RingTheory.UniqueFactorizationDomain` | `UniqueFactorizationMonoid` | `uniqueFactorizationMonoid_iff` |

#### 环论代码示例

```lean
import Mathlib.Algebra.Ring.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Quotient

-- 环的定义检查
#check Ring
#check CommRing

-- 理想示例：ℤ中由n生成的理想
example (n : ℤ) : Ideal ℤ := Ideal.span {n}

-- 商环 ℤ/nℤ
example (n : ℕ) : Type _ := ZMod n

-- 整数环是PID
example : IsPrincipalIdealRing ℤ := by
  infer_instance

-- 理想是素理想当且仅当商环是整环
example {R : Type*} [CommRing R] (I : Ideal R) :
    I.IsPrime ↔ IsDomain (R ⧸ I) := by
  rw [Ideal.isPrime_iff, isDomain_iff_no_zero_divisors]
  constructor
  · intro h
    exact { __ := (Ideal.Quotient.commRing I),
            __ := no_zero_divisors_of_prime I h.2 }
  · intro h
    constructor
    · rintro rfl
      have := h.1
      contradiction
    · exact fun h' => by simpa using h'
```

#### 2.3 域论

| 数学概念 | FormalMath文档 | Mathlib4模块 | 核心定义 | 关键定理 |
|---------|---------------|--------------|---------|---------|
| **域扩张** | `docs/02-代数结构/02-核心理论/域论/01-域论-国际标准深度扩展版.md` | `Mathlib.FieldTheory.IntermediateField` | `IntermediateField` | `IntermediateField.lift` |
| **代数扩张** | `docs/02-代数结构/02-核心理论/域论/01-域论-深度扩展版.md` | `Mathlib.FieldTheory.Algebraic` | `IsAlgebraic` | `IsAlgebraic.trans` |
| **分裂域** | `docs/02-代数结构/02-核心理论/域论/01-域论-深度扩展版.md` | `Mathlib.FieldTheory.SplittingField.Construction` | `SplittingField` | `SplittingField.splits` |
| **伽罗瓦扩张** | `docs/02-代数结构/02-核心理论/域论/01-域论-深度扩展版.md` | `Mathlib.FieldTheory.Galois` | `IsGalois` | `IsGalois.tfae` |
| **伽罗瓦群** | `docs/02-代数结构/02-核心理论/域论/01-域论-深度扩展版.md` | `Mathlib.FieldTheory.Galois` | `Aut` | `Gal.card_eq_finrank` |
| **有限域** | `docs/00-核心概念理解三问/11-核心定理多表征/18-有限域分类定理-五种表征.md` | `Mathlib.FieldTheory.Finite.Basic` | `FiniteField` | `FiniteField.card'` |

#### 域论代码示例

```lean
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois

-- 有限域 𝔽_p = ZMod p
example (p : ℕ) [Fact p.Prime] : Type _ := ZMod p

-- 有限域的元素个数是p^n
open FiniteField in
example (p n : ℕ) [Fact p.Prime] :
    Fintype.card (GaloisField p n) = p ^ n := by
  exact card' p n

-- 伽罗瓦群示例
example (K L : Type*) [Field K] [Field L] [Algebra K L] : Type _ :=
  L ≃ₐ[K] L
```

#### 2.4 线性代数

| 数学概念 | FormalMath文档 | Mathlib4模块 | 核心定义 | 关键定理 |
|---------|---------------|--------------|---------|---------|
| **向量空间** | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/01-线性代数与矩阵理论-国际标准深度扩展版.md` | `Mathlib.Algebra.Module.Basic` | `Module`, `VectorSpace` | `Module.add_smul`, `Module.zero_smul` |
| **线性映射** | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/01-线性代数与矩阵理论-深度扩展版.md` | `Mathlib.Algebra.Module.LinearMap` | `LinearMap` | `LinearMap.add`, `LinearMap.comp` |
| **矩阵** | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/01-线性代数与矩阵理论-深度扩展版.md` | `Mathlib.Data.Matrix.Basic` | `Matrix` | `Matrix.mul_assoc`, `Matrix.one_mul` |
| **行列式** | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/01-线性代数与矩阵理论-深度扩展版.md` | `Mathlib.LinearAlgebra.Matrix.Determinant` | `Matrix.det` | `Matrix.det_mul`, `Matrix.det_transpose` |
| **特征值** | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/01-线性代数与矩阵理论-深度扩展版.md` | `Mathlib.LinearAlgebra.Eigenspace` | `Module.End.eigenspace` | `eigenspace_ker` |
| **内积空间** | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/01-线性代数与矩阵理论-深度扩展版.md` | `Mathlib.Analysis.InnerProductSpace.Basic` | `InnerProductSpace` | `inner_add_left`, `inner_smul_left` |
| **谱定理** | `docs/00-核心概念理解三问/11-核心定理多表征/40-谱定理-五种表征.md` | `Mathlib.LinearAlgebra.Spectrum` | `spectrum` | `LinearMap.IsSymmetric.hasEigenvector_of_ne_zero` |

#### 线性代数代码示例

```lean
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.LinearAlgebra.Eigenspace

-- 2×2矩阵示例
example : Matrix (Fin 2) (Fin 2) ℝ := !![1, 2; 3, 4]

-- 行列式计算
example : Matrix.det !![(1 : ℝ), 2; 3, 4] = -2 := by
  simp [Matrix.det_fin_two, Matrix.det_fin_two_of]
  norm_num

-- 特征空间
example (V : Type*) [AddCommGroup V] [Module ℝ V]
    (f : V →ₗ[ℝ] V) (μ : ℝ) : Submodule ℝ V :=
  f.eigenspace μ
```

#### 2.5 模论

| 数学概念 | FormalMath文档 | Mathlib4模块 | 核心定义 | 关键定理 |
|---------|---------------|--------------|---------|---------|
| **模** | `docs/02-代数结构/02-核心理论/模论/01-模论-国际标准深度扩展版.md` | `Mathlib.Algebra.Module.Basic` | `Module` | `smul_add`, `add_smul` |
| **自由模** | `docs/02-代数结构/02-核心理论/模论/01-模论-深度扩展版.md` | `Mathlib.LinearAlgebra.FreeModule.Basic` | `Module.Free` | `Module.Free.of_basis` |
| **正合序列** | `docs/15-同调代数/03-同调代数深度扩展版.md` | `Mathlib.Algebra.Homology.ShortComplex` | `ShortComplex`, `Exact` | `ShortComplex.exact_iff` |

#### 2.6 范畴论

| 数学概念 | FormalMath文档 | Mathlib4模块 | 核心定义 | 关键定理 |
|---------|---------------|--------------|---------|---------|
| **范畴** | `docs/02-代数结构/02-核心理论/范畴论/06-范畴论-深度扩展版.md` | `Mathlib.CategoryTheory.Category.Basic` | `Category` | `Category.id_comp`, `Category.comp_id` |
| **函子** | `docs/02-代数结构/02-核心理论/范畴论/06-范畴论-深度扩展版.md` | `Mathlib.CategoryTheory.Functor.Basic` | `Functor` | `Functor.map_id`, `Functor.map_comp` |
| **自然变换** | `docs/02-代数结构/02-核心理论/范畴论/06-范畴论-深度扩展版.md` | `Mathlib.CategoryTheory.NatTrans` | `NatTrans` | `NatTrans.vcomp`, `NatTrans.id` |
| **极限** | `docs/02-代数结构/02-核心理论/范畴论/06-范畴论-深度扩展版.md` | `Mathlib.CategoryTheory.Limits.IsLimit` | `IsLimit`, `LimitCone` | `IsLimit.hom_iso` |
| **米田引理** | `docs/00-核心概念理解三问/11-核心定理多表征/05-米田引理-五种表征.md` | `Mathlib.CategoryTheory.Yoneda` | `yoneda`, `yonedaLemma` | `yoneda_lemma` |

#### 范畴论代码示例

```lean
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Yoneda

-- 范畴的定义检查
#check Category

-- 函子示例：恒等函子
example (C : Type*) [Category C] : C ⥤ C := Functor.id C

-- 米田引理核心同构
example (C : Type*) [Category C] (F : Cᵒᵖ ⥤ Type*) (X : C) :
    (yoneda.obj X ⟶ F) ≃ F.obj X :=
  yonedaSections X F
```

---

### 三、分析学

#### 3.1 实分析

| 数学概念 | FormalMath文档 | Mathlib4模块 | 核心定义 | 关键定理 |
|---------|---------------|--------------|---------|---------|
| **极限** | `docs/03-分析学/01-实分析/01-实分析-深度扩展版.md` | `Mathlib.Analysis.SpecificLimits.Basic` | `Filter.Tendsto`, `nhds` | `tendsto_const`, `tendsto_add` |
| **连续性** | `docs/03-分析学/01-实分析/01-实分析-深度扩展版.md` | `Mathlib.Topology.Basic` | `Continuous`, `ContinuousAt` | `Continuous.add`, `Continuous.mul` |
| **导数** | `docs/03-分析学/01-实分析/01-实分析-深度扩展版.md` | `Mathlib.Analysis.Calculus.Deriv.Basic` | `deriv`, `HasDerivAt` | `deriv_add`, `deriv_mul` |
| **积分** | `docs/03-分析学/01-实分析/02-Lebesgue积分-深度扩展版.md` | `Mathlib.MeasureTheory.Integral.Bochner` | `integral`, `Integrable` | `integral_add`, `integral_smul` |
| **微积分基本定理** | `docs/00-核心概念理解三问/11-核心定理多表征/68-微积分基本定理-五种表征.md` | `Mathlib.MeasureTheory.Integral.FundThmCalculus` | `intervalIntegral` | `intervalIntegral.deriv_integral_right` |
| **中值定理** | `docs/00-核心概念理解三问/11-核心定理多表征/72-中值定理-五种表征.md` | `Mathlib.Analysis.Calculus.MeanValue` | `exists_deriv_eq_slope` | `exists_hasDerivAt_eq_slope` |
| **Taylor定理** | `docs/00-核心概念理解三问/11-核心定理多表征/67-Taylor定理-五种表征.md` | `Mathlib.Analysis.Calculus.Taylor` | `taylor_within_apply` | `taylor_mean_remainder_lagrange` |
| **紧致性** | `docs/00-核心概念理解三问/11-核心定理多表征/66-Heine-Borel定理-五种表征.md` | `Mathlib.Topology.Compactness.Compact` | `IsCompact` | `IsCompact.image`, `isCompact_iff_finite_subcover` |
| **完备性** | `docs/03-分析学/01-实分析/01-实分析-深度扩展版.md` | `Mathlib.Topology.UniformSpace.Complete` | `CompleteSpace` | `CompleteSpace.complete_univ` |
| **Bolzano-Weierstrass** | `docs/00-核心概念理解三问/11-核心定理多表征/65-Bolzano-Weierstrass定理-五种表征.md` | `Mathlib.Topology.MetricSpace.Basic` | `CompactSpace` | `isCompact_iff_seq_compact` |
| **柯西收敛准则** | `docs/09-形式化证明/Lean4/08-柯西收敛准则.lean` | `Mathlib.Topology.UniformSpace.Complete` | `CompleteSpace`, `CauchySeq` | `cauchySeq_tendsto_of_complete` |
| **罗尔定理** | `docs/09-形式化证明/Lean4/09-罗尔定理.lean` | `Mathlib.Analysis.Calculus.Rolle` | `HasDerivAt` | `exists_hasDerivAt_eq_zero` |

#### 实分析代码示例

```lean
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.Bochner

-- 导数计算示例
example : deriv (fun x : ℝ => x ^ 2) 3 = 6 := by
  simp [deriv_pow]

-- 中值定理
example (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hf' : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x) :
    ∃ c ∈ Set.Ioo a b, f' c = (f b - f a) / (b - a) := by
  apply exists_hasDerivAt_eq_slope
  all_goals assumption
```

#### 3.2 复分析

| 数学概念 | FormalMath文档 | Mathlib4模块 | 核心定义 | 关键定理 |
|---------|---------------|--------------|---------|---------|
| **全纯函数** | `docs/03-分析学/02-复分析/02-复分析-深度扩展版.md` | `Mathlib.Analysis.Complex.Basic` | `Differentiable`, `Holomorphic` | `Differentiable.congr` |
| **Cauchy积分公式** | `docs/00-核心概念理解三问/11-核心定理多表征/14-Cauchy积分公式-五种表征.md` | `Mathlib.MeasureTheory.Integral.CircleIntegral` | `circleIntegral` | `circleIntegral_sub_inv_smul` |
| **留数定理** | `docs/00-核心概念理解三问/11-核心定理多表征/37-留数定理-五种表征.md` | `Mathlib.MeasureTheory.Integral.CircleIntegral` | `residue` | `circleIntegral_residue` |
| **解析函数** | `docs/03-分析学/02-复分析/02-复分析-深度扩展版.md` | `Mathlib.Analysis.Analytic.Basic` | `AnalyticAt`, `AnalyticOn` | `AnalyticAt.continuousAt` |
| **Riemann映射定理** | `docs/00-核心概念理解三问/11-核心定理多表征/36-Riemann映射定理-五种表征.md` | `Mathlib.Analysis.Complex.RiemannMapping` | `conformalEquiv` | `conformalEquivToUnitDisc` |
| **Liouville定理** | `docs/00-核心概念理解三问/11-核心定理多表征/75-Liouville定理-五种表征.md` | `Mathlib.Analysis.Complex.Liouville` | `bounded_entire_iff_const` | `Liouville` |
| **欧拉公式** | `docs/09-形式化证明/Lean4/10-欧拉公式.lean` | `Mathlib.Data.Complex.Exponential` | `Complex.exp` | `Complex.exp_mul_I` |

#### 复分析代码示例

```lean
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Liouville

-- 全纯函数定义检查
#check DifferentiableOn ℂ

-- Liouville定理：有界整函数必为常数
example {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hb : Bornology.IsBounded (Set.range f)) :
    ∃ c, f = Function.const ℂ c := by
  exact Liouville.bounded_iff_const.mp hb hf
```

#### 3.3 泛函分析

| 数学概念 | FormalMath文档 | Mathlib4模块 | 核心定义 | 关键定理 |
|---------|---------------|--------------|---------|---------|
| **Banach空间** | `docs/03-分析学/03-泛函分析/03-泛函分析-深度扩展版.md` | `Mathlib.Analysis.NormedSpace.Basic` | `NormedSpace`, `BanachSpace` | `completeSpace` |
| **Hilbert空间** | `docs/03-分析学/03-泛函分析/03-泛函分析-深度扩展版.md` | `Mathlib.Analysis.InnerProductSpace.Basic` | `InnerProductSpace` | `completeSpace_iff` |
| **有界线性算子** | `docs/03-分析学/03-泛函分析/03-泛函分析-深度扩展版.md` | `Mathlib.Analysis.NormedSpace.BoundedLinearMap` | `ContinuousLinearMap` | `ContinuousLinearMap.norm` |
| **Hahn-Banach定理** | `docs/00-核心概念理解三问/11-核心定理多表征/30-Hahn-Banach定理-五种表征.md` | `Mathlib.Analysis.NormedSpace.HahnBanach.Extension` | `exists_extension_norm_eq` | `HahnBanach` |
| **开映射定理** | `docs/00-核心概念理解三问/11-核心定理多表征/31-开映射定理-五种表征.md` | `Mathlib.Analysis.NormedSpace.Banach` | `IsOpenMap` | `IsOpenMap.of_surjective` |
| **一致有界性原理** | `docs/03-分析学/03-泛函分析/04-泛函分析三大定理-深度扩展版.md` | `Mathlib.Analysis.NormedSpace.BanachSteinhaus` | `banach_steinhaus` | `banach_steinhaus` |
| **Riesz表示定理** | `docs/00-核心概念理解三问/11-核心定理多表征/32-Riesz表示定理-五种表征.md` | `Mathlib.MeasureTheory.Function.ContinuousMapDense` | `rieszRepresentation` | `toBorelMeasure_apply` |

#### 泛函分析代码示例

```lean
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension

-- Hahn-Banach定理：范数保持延拓
example {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (p : Subspace ℝ E) (f : p →L[ℝ] F) :
    ∃ g : E →L[ℝ] F, (∀ x : p, g x = f x) ∧ ‖g‖ = ‖f‖ := by
  apply exists_extension_norm_eq
```

#### 3.4 测度论

| 数学概念 | FormalMath文档 | Mathlib4模块 | 核心定义 | 关键定理 |
|---------|---------------|--------------|---------|---------|
| **测度空间** | `docs/01-基础数学/测度论与数系分析-国际标准版.md` | `Mathlib.MeasureTheory.Measure.MeasureSpace` | `MeasureSpace`, `Measure` | `measure_union` |
| **可测函数** | `docs/01-基础数学/测度论与数系分析-国际标准版.md` | `Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic` | `StronglyMeasurable` | `measurable_const` |
| **Lebesgue积分** | `docs/03-分析学/01-实分析/02-Lebesgue积分-深度扩展版.md` | `Mathlib.MeasureTheory.Integral.Bochner` | `integral`, `Integrable` | `integral_add`, `integral_smul` |
| **单调收敛定理** | `docs/00-核心概念理解三问/11-核心定理多表征/09-单调收敛定理-五种表征.md` | `Mathlib.MeasureTheory.Integral.Layercake` | `integral_tendsto` | `tendsto_integral_of_dominated_convergence` |
| **控制收敛定理** | `docs/00-核心概念理解三问/11-核心定理多表征/10-控制收敛定理-五种表征.md` | `Mathlib.MeasureTheory.Integral.DominatedConvergence` | `tendsto_integral_filter` | `tendsto_integral_of_dominated_convergence` |
| **Radon-Nikodym定理** | `docs/00-核心概念理解三问/11-核心定理多表征/34-Radon-Nikodym定理-五种表征.md` | `Mathlib.MeasureTheory.Decomposition.RadonNikodym` | `rnDeriv` | `integral_rnDeriv` |
| **Fubini定理** | `docs/00-核心概念理解三问/11-核心定理多表征/33-Fubini定理-五种表征.md` | `Mathlib.MeasureTheory.Constructions.Prod.Integral` | `integral_prod` | `integral_integral_swap` |

#### 测度论代码示例

```lean
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner

-- Lebesgue积分基本性质
example {X : Type*} [MeasureSpace X] {f g : X → ℝ}
    (hf : Integrable f) (hg : Integrable g) :
    ∫ x, (f x + g x) = ∫ x, f x + ∫ x, g x := by
  rw [integral_add hf hg]

-- 控制收敛定理
example {X : Type*} [MeasureSpace X] {f : ℕ → X → ℝ} {g : X → ℝ}
    (hfg : ∀ n, Integrable (f n)) (hg : Integrable g)
    (hf_bound : ∀ n, ∀ x, |f n x| ≤ g x)
    (hf_tendsto : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun n => ∫ x, f n x) atTop (𝓝 0) := by
  apply tendsto_integral_of_dominated_convergence
  · exact g
  · exact hfg
  · exact hg
  · exact hf_bound
  · filter_upwards with x
    exact hf_tendsto x
```

---

### 四、拓扑学

| 数学概念 | FormalMath文档 | Mathlib4模块 | 核心定义 | 关键定理 |
|---------|---------------|--------------|---------|---------|
| **拓扑空间** | `docs/05-拓扑学/01-点集拓扑-深度扩展版.md` | `Mathlib.Topology.Basic` | `TopologicalSpace`, `IsOpen` | `isOpen_univ`, `isOpen_inter` |
| **连续映射** | `docs/05-拓扑学/01-点集拓扑-深度扩展版.md` | `Mathlib.Topology.Basic` | `Continuous` | `Continuous.comp`, `Continuous.prod_mk` |
| **紧致性** | `docs/05-拓扑学/01-点集拓扑-深度扩展版.md` | `Mathlib.Topology.Compactness.Compact` | `IsCompact` | `IsCompact.image`, `IsCompact.prod` |
| **连通性** | `docs/05-拓扑学/01-点集拓扑-深度扩展版.md` | `Mathlib.Topology.Connected` | `IsConnected`, `IsPathConnected` | `IsConnected.image` |
| **Tychonoff定理** | `docs/00-核心概念理解三问/11-核心定理多表征/13-Tychonoff定理-五种表征.md` | `Mathlib.Topology.Constructions` | `compactSpace_pi` | `compactSpace_pi` |
| **Urysohn引理** | `docs/00-核心概念理解三问/11-核心定理多表征/20-Urysohn引理-五种表征.md` | `Mathlib.Topology.UrysohnsLemma` | `exists_continuous_zero_one_of_isClosed` | `urysohn` |
| **Baire纲定理** | `docs/00-核心概念理解三问/11-核心定理多表征/29-Baire纲定理-五种表征.md` | `Mathlib.Topology.Baire.CompleteMetrizable` | `BaireSpace` | `dense_iInter_of_open` |
| **基本群** | `docs/05-拓扑学/02-代数拓扑.md` | `Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic` | `FundamentalGroupoid` | `homotopicQuot` |
| **同调群** | `docs/05-拓扑学/05-同调论.md` | `Mathlib.AlgebraicTopology.SingularHomology` | `singularHomology` | `homology_functor` |

#### 拓扑学代码示例

```lean
import Mathlib.Topology.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected

-- 拓扑空间基本性质
example {X : Type*} [TopologicalSpace X] : IsOpen (Set.univ : Set X) :=
  isOpen_univ

-- 紧致集的连续像
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) {K : Set X} (hK : IsCompact K) :
    IsCompact (f '' K) :=
  hK.image hf

-- 连通性
example {X : Type*} [TopologicalSpace X] :
    IsConnected Set.univ ↔ PreconnectedSpace X := by
  constructor
  · intro h
    exact ⟨h.2⟩
  · intro h
    exact ⟨by trivial, h.preconnected⟩
```

---

### 五、数论

| 数学概念 | FormalMath文档 | Mathlib4模块 | 核心定义 | 关键定理 |
|---------|---------------|--------------|---------|---------|
| **素数** | `docs/06-数论/01-初等数论-增强版.md` | `Mathlib.NumberTheory.Primes` | `Prime`, `Nat.Prime` | `infinite_setOf_prime`, `Nat.Prime.dvd_mul` |
| **同余** | `docs/06-数论/01-初等数论-增强版.md` | `Mathlib.Data.ZMod.Basic` | `ZMod`, `ModEq` | `ModEq.symm`, `ModEq.trans` |
| **欧拉函数** | `docs/06-数论/01-初等数论-增强版.md` | `Mathlib.NumberTheory.Eulerian` | `Nat.totient` | `Nat.totient_mul` |
| **二次互反律** | `docs/00-核心概念理解三问/11-核心定理多表征/27-二次互反律-五种表征.md` | `Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity` | `legendreSym`, `jacobiSym` | `quadratic_reciprocity` |
| **素数定理** | `docs/00-核心概念理解三问/11-核心定理多表征/26-素数定理-五种表征.md` | `Mathlib.NumberTheory.PrimeCounting` | `primeCounting` | `PrimeNumberTheorem` |
| **费马大定理** | `docs/11-高级数学/18-现代数论前沿.md` | `Mathlib.NumberTheory.FLT.Basic` | `FermatLastTheorem` | `flt` |
| **p进数** | `docs/06-数论/02-代数数论.md` | `Mathlib.NumberTheory.Padics.PadicNumbers` | `Padic`, `PadicInt` | `Padic.complete` |
| **代数整数** | `docs/06-数论/02-代数数论.md` | `Mathlib.NumberTheory.NumberField.Basic` | `NumberField`, `RingOfIntegers` | `RingOfIntegers.integralClosure` |

#### 数论代码示例

```lean
import Mathlib.NumberTheory.Primes
import Mathlib.NumberTheory.Eulerian
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

-- 素数无穷多
example : {p : ℕ | Nat.Prime p}.Infinite := by
  apply Nat.infinite_setOf_prime

-- 欧拉函数
example : Nat.totient 10 = 4 := by
  norm_num [Nat.totient]

-- 二次互反律
example (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hp_odd : p ≠ 2) (hq_odd : q ≠ 2) (hpq : p ≠ q) :
    legendreSym p q * legendreSym q p = (-1) ^ ((p - 1) / 2 * (q - 1) / 2) := by
  have hp' : Fact p.Prime := ⟨hp⟩
  have hq' : Fact q.Prime := ⟨hq⟩
  rw [quadratic_reciprocity']
  all_goals omega
```

---

### 六、几何学

| 数学概念 | FormalMath文档 | Mathlib4模块 | 核心定义 | 关键定理 |
|---------|---------------|--------------|---------|---------|
| **流形** | `docs/04-几何学/03-微分几何.md` | `Mathlib.Geometry.Manifold.SmoothManifoldWithCorners` | `SmoothManifoldWithCorners` | `SmoothManifoldWithCorners.hasGroupoid` |
| **切空间** | `docs/04-几何学/03-微分几何.md` | `Mathlib.Geometry.Manifold.TangentBundle` | `TangentSpace` | `tangentBundleCore` |
| **黎曼度量** | `docs/04-几何学/03-微分几何.md` | `Mathlib.Geometry.RiemannianMetric` | `RiemannianMetric` | `RiemannianMetric.inner_product` |
| **高斯-博内定理** | `docs/00-核心概念理解三问/11-核心定理多表征/12-Gauss-Bonnet定理-五种表征.md` | `Mathlib.Geometry.Manifold.GaussBonnet` | `EulerCharacteristic` | `gauss_bonnet` |
| **Stokes定理** | `docs/00-核心概念理解三问/11-核心定理多表征/06-Stokes定理-五种表征.md` | `Mathlib.Geometry.Manifold.Stokes` | `integral_differentialForm` | `stokes` |
| **de Rham上同调** | `docs/00-核心概念理解三问/11-核心定理多表征/35-de Rham定理-五种表征.md` | `Mathlib.Geometry.Manifold.DifferentialForm` | `deRhamCohomology` | `deRhamTheorem` |
| **代数曲线** | `docs/13-代数几何/03-代数几何深度扩展版.md` | `Mathlib.AlgebraicGeometry.Scheme` | `Scheme` | `Spec`, `Proj` |

#### 几何学代码示例

```lean
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Mathlib.Geometry.Manifold.TangentBundle

-- 光滑流形
example (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [SmoothManifoldWithCorners (𝓡 n) M] : Type _ := TangentBundle (𝓡 n) M
```

---

### 七、逻辑学与类型论

| 数学概念 | FormalMath文档 | Mathlib4模块 | 核心定义 | 关键定理 |
|---------|---------------|--------------|---------|---------|
| **命题逻辑** | `docs/07-逻辑学/01-命题逻辑-增强版.md` | `Mathlib.Logic.Basic` | `Or`, `And`, `Not`, `Iff` | `or_comm`, `and_comm` |
| **谓词逻辑** | `docs/07-逻辑学/02-谓词逻辑.md` | `Mathlib.Logic.Basic` | `∀`, `∃` | `forall_imp`, `exists_imp` |
| **同伦类型论** | `docs/11-高级数学/15-同伦类型论.md` | `Mathlib.Init.Core` | `Eq`, `HEq` | `Eq.rec`, `Eq.symm`, `Eq.trans` |
| **选择公理** | `docs/01-基础数学/ZFC公理体系/ZFC公理体系-深度扩展版.md` | `Mathlib.Logic.Equiv.Basic` | `Equiv.ofBijective` | `Classical.choice` |
| **Zorn引理** | `docs/00-核心概念理解三问/11-核心定理多表征/16-Zorn引理-五种表征.md` | `Mathlib.Order.Zorn` | `zorn_le` | `zorn_le_nonempty` |

---

## 🔍 快速查找指南

### 按Mathlib4模块查找

| Mathlib4模块 | 对应数学分支 | FormalMath路径 |
|-------------|-------------|---------------|
| `Mathlib.Algebra.Group.*` | 群论 | `docs/02-代数结构/02-核心理论/群论/` |
| `Mathlib.Algebra.Ring.*` | 环论 | `docs/02-代数结构/02-核心理论/环论/` |
| `Mathlib.FieldTheory.*` | 域论 | `docs/02-代数结构/02-核心理论/域论/` |
| `Mathlib.LinearAlgebra.*` | 线性代数 | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/` |
| `Mathlib.CategoryTheory.*` | 范畴论 | `docs/02-代数结构/02-核心理论/范畴论/` |
| `Mathlib.Analysis.*` | 分析学 | `docs/03-分析学/` |
| `Mathlib.Topology.*` | 拓扑学 | `docs/05-拓扑学/` |
| `Mathlib.NumberTheory.*` | 数论 | `docs/06-数论/` |
| `Mathlib.Geometry.*` | 几何学 | `docs/04-几何学/` |
| `Mathlib.MeasureTheory.*` | 测度论 | `docs/01-基础数学/测度论与数系分析-国际标准版.md` |
| `Mathlib.SetTheory.*` | 集合论 | `docs/01-基础数学/集合论/` |

### 按定理名称查找

| 定理名称 | Mathlib4路径 |
|---------|-------------|
| Lagrange定理 | `Mathlib.GroupTheory.Coset` |
| 第一同构定理 | `Mathlib.GroupTheory.QuotientGroup` |
| Sylow定理 | `Mathlib.GroupTheory.Sylow` |
| 谱定理 | `Mathlib.LinearAlgebra.Spectrum` |
| Hahn-Banach定理 | `Mathlib.Analysis.NormedSpace.HahnBanach.Extension` |
| 开映射定理 | `Mathlib.Analysis.NormedSpace.Banach` |
| Riesz表示定理 | `Mathlib.MeasureTheory.Function.ContinuousMapDense` |
| 单调收敛定理 | `Mathlib.MeasureTheory.Integral.Layercake` |
| 控制收敛定理 | `Mathlib.MeasureTheory.Integral.DominatedConvergence` |
| Fubini定理 | `Mathlib.MeasureTheory.Constructions.Prod.Integral` |
| 二次互反律 | `Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity` |
| 素数定理 | `Mathlib.NumberTheory.PrimeCounting` |
| 高斯-博内定理 | `Mathlib.Geometry.Manifold.GaussBonnet` |
| Stokes定理 | `Mathlib.Geometry.Manifold.Stokes` |

---

## 📖 学习路径

详见 [从FormalMath到Mathlib4学习路径](00-从FormalMath到Mathlib4学习路径.md)

---

## 🔗 外部资源

### 官方文档

- [Mathlib4官方文档](https://leanprover-community.github.io/mathlib4_docs/)
- [Lean4官方文档](https://lean-lang.org/doc/)
- [Mathlib4 GitHub](https://github.com/leanprover-community/mathlib4)

### 社区资源

- [Lean Zulip社区](https://leanprover.zulipchat.com/)
- [Mathlib4贡献指南](https://leanprover-community.github.io/contribute/)
- [Lean4教程](https://leanprover.github.io/theorem_proving_in_lean4/)

---

**最后更新**: 2026-04-03（新增：群第一同构定理、拉格朗日插值、柯西收敛准则、罗尔定理、欧拉公式）
**Mathlib4版本**: v4.29.0
