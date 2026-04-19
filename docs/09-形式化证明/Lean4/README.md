---
msc_primary: 68

  - 68V20
  - 03B35
  - 03B70
title: FormalMath - Mathlib4对齐形式化证明库
processed_at: '2026-04-05'
---
msc_primary: "68V20"
msc_secondary: ["03B35", "03B70"]
---

# FormalMath - Mathlib4对齐形式化证明库

## 项目定位声明

> **重要说明**：本项目的Lean4代码定位为**"示例与概念解释"**，而非一个完整的数学形式化库。
> 我们采取"战略性放弃"策略：保留少量完整证明作为学习示例，其余高级定理转为引用Mathlib4现有定理的中文解释。
> 如果您需要可直接编译的完整形式化库，请参考 [Mathlib4 官方文档](https://leanprover-community.github.io/mathlib4_docs/)。

## 概述

本目录包含FormalMath项目与Mathlib4对齐的核心定理形式化证明（及概念解释）。
所有代码使用Lean 4编写，与Mathlib 4.19.0版本对齐。

## Lean4文件形式化状态总览

| 文件名 | 领域 | 定理数 | sorry数 | 分类 | 状态说明 | Mathlib4对应/搜索关键词 |
|--------|------|--------|---------|------|----------|------------------------|
| `AlgebraicTopology.lean` | Algebra | 11 | 0 | A | ✅ 完整形式化示例 | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib AlgebraicTopology`) |
| `CoveringSpace.lean` | Algebra | 10 | 0 | A | ✅ 完整形式化示例 | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Topology.Covering.Basic, Mathlib.Topology.Homotopy.Basic`) |
| `FundamentalGroup.lean` | Algebra | 8 | 0 | A | ✅ 完整形式化示例 | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Topology.Homotopy.Basic, Mathlib.Topology.Covering.Basic`) |
| `HomologicalAlgebra.lean` | Algebra | 6 | 0 | A | ✅ 完整形式化示例 | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Algebra.Homology, Mathlib.CategoryTheory.Abelian, Mathlib.CategoryTheory.Preadditive.Projective, Mathlib.CategoryTheory.Preadditive.Injective`) |
| `Basic.lean` | 其他 | 0 | 0 | A | ✅ 完整形式化示例 | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib Basic`) |
| `ModEq.lean` | 其他 | 2 | 0 | A | ✅ 完整形式化示例 | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib ModEq`) |
| `TaylorTheorem.lean` | 分析 | 3 | 0 | A | ✅ 完整形式化示例 | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Analysis.Calculus.Taylor, Mathlib.Analysis.Calculus.Deriv, Mathlib.Analysis.Calculus.ContDiff`) |
| `CurvatureTensor.lean` | 微分几何 | 9 | 0 | A | ✅ 完整形式化示例 | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Geometry.Manifold.IntegralCurve, Mathlib.Geometry.RiemannianMetric`) |
| `MirrorSymmetry.lean` | 微分几何 | 8 | 0 | A | ✅ 完整形式化示例 | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib MirrorSymmetry`) |
| `HomotopyTheory.lean` | 拓扑 | 4 | 0 | A | ✅ 完整形式化示例 | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib HomotopyTheory`) |
| `CategoryTheory.lean` | 范畴论/高级结构 | 3 | 0 | A | ✅ 完整形式化示例 | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib CategoryTheory`) |
| `ModuleTheory.lean` | Algebra | 10 | 1 | B | ⚠️ 部分证明（含 sorry） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Algebra.Module.LinearMap, Mathlib.Algebra.Module.Submodule`) |
| `ComplexExponential.lean` | 分析 | 12 | 3 | B | ⚠️ 部分证明（含 sorry） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Data.Complex.Exponential, Mathlib.Analysis.SpecialFunctions.ExpDeriv`) |
| `RadonNikodym.lean` | 分析 | 9 | 2 | B | ⚠️ 部分证明（含 sorry） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib RadonNikodym`) |
| `YoungInequality.lean` | 分析 | 7 | 3 | B | ⚠️ 部分证明（含 sorry） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Analysis.MeanInequalities, Mathlib.Data.Real.ConjExponents`) |
| `DynamicalSystems.lean` | 动力系统/遍历论 | 11 | 5 | B | ⚠️ 部分证明（含 sorry） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib DynamicalSystems`) |
| `SetTheory.lean` | 逻辑与基础 | 11 | 2 | B | ⚠️ 部分证明（含 sorry） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.SetTheory.Ordinal.Basic, Mathlib.SetTheory.Cardinal.Basic, Mathlib.SetTheory.ZFC.Basic, Mathlib.Data.Set.Basic`) |
| `TypeTheory.lean` | 逻辑与基础 | 9 | 3 | B | ⚠️ 部分证明（含 sorry） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Logic.Function.Basic, Mathlib.Data.Sigma.Basic, Mathlib.Data.Sum.Basic, Mathlib.Data.Prod.Basic`) |
| `AlgebraicGeometry.lean` | Algebra | 5 | 7 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib AlgebraicGeometry`) |
| `AlgebraicNumberTheory.lean` | Algebra | 12 | 17 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib AlgebraicNumberTheory`) |
| `CharacterTheory.lean` | Algebra | 10 | 23 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib CharacterTheory`) |
| `CharacteristicClass.lean` | Algebra | 17 | 52 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib CharacteristicClass`) |
| `ClassFieldTheory.lean` | Algebra | 8 | 8 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib ClassFieldTheory`) |
| `CommutativeAlgebra.lean` | Algebra | 8 | 11 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib CommutativeAlgebra`) |
| `DerivedAlgebraicGeometry.lean` | Algebra | 5 | 53 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib DerivedAlgebraicGeometry`) |
| `FieldExtension.lean` | Algebra | 8 | 7 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.FieldTheory.Extension, Mathlib.FieldTheory.Minpoly, Mathlib.FieldTheory.Adjoin`) |
| `GaloisGroup.lean` | Algebra | 9 | 13 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib GaloisGroup`) |
| `GeometricRepresentationTheory.lean` | Algebra | 6 | 35 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib GeometricRepresentationTheory`) |
| `LieAlgebra.lean` | Algebra | 10 | 14 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib LieAlgebra`) |
| `NoetherianRing.lean` | Algebra | 15 | 11 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib NoetherianRing`) |
| `PrincipalIdealDomain.lean` | Algebra | 11 | 6 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.RingTheory.PrincipalIdealDomain, Mathlib.RingTheory.UniqueFactorizationDomain`) |
| `QuantumFieldTheory.lean` | Algebra | 8 | 5 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib QuantumFieldTheory`) |
| `RepresentationTheory.lean` | Algebra | 9 | 22 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib RepresentationTheory`) |
| `RieszRepresentation.lean` | Algebra | 9 | 8 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib RieszRepresentation`) |
| `StringTheory.lean` | Algebra | 8 | 6 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib StringTheory`) |
| `UniversalEnvelopingAlgebra.lean` | Algebra | 10 | 31 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib UniversalEnvelopingAlgebra`) |
| `VertexOperatorAlgebras.lean` | Algebra | 6 | 28 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib VertexOperatorAlgebras`) |
| `ArithmeticGeometry.lean` | 代数几何 | 8 | 7 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib ArithmeticGeometry`) |
| `ChernClass.lean` | 代数几何 | 9 | 43 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib ChernClass`) |
| `CohomologyTheory.lean` | 代数几何 | 9 | 40 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.AlgebraicTopology, Mathlib.Algebra.Homology, Mathlib.Topology.Sheaves`) |
| `DeRhamCohomology.lean` | 代数几何 | 17 | 35 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Geometry.Manifold, Mathlib.Analysis.DifferentialForm`) |
| `EllipticCurve.lean` | 代数几何 | 8 | 12 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib EllipticCurve`) |
| `EllipticPDE.lean` | 代数几何 | 10 | 15 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib EllipticPDE`) |
| `FaltingsTheorem.lean` | 代数几何 | 12 | 46 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib FaltingsTheorem`) |
| `ModuliSpaces.lean` | 代数几何 | 6 | 59 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib ModuliSpaces`) |
| `MordellWeil.lean` | 代数几何 | 8 | 16 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib MordellWeil`) |
| `MotiveTheory.lean` | 代数几何 | 3 | 19 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib MotiveTheory`) |
| `PerfectoidSpaces.lean` | 代数几何 | 5 | 16 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib PerfectoidSpaces`) |
| `Basic.lean` | 其他 | 8 | 15 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib Basic`) |
| `Basic.lean` | 其他 | 0 | 1 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib Basic`) |
| `Basic.lean` | 其他 | 8 | 20 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib Basic`) |
| `BorelCantelli.lean` | 其他 | 7 | 14 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Probability.Independence, Mathlib.MeasureTheory.Measure.Limsup, Mathlib.Probability.StrongLaw`) |
| `Finite.lean` | 其他 | 1 | 1 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib Finite`) |
| `FloerTheory.lean` | 其他 | 6 | 21 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib FloerTheory`) |
| `GammaFunction.lean` | 其他 | 8 | 14 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Analysis.SpecialFunctions.Gamma.Basic, Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup`) |
| `IndexTheory.lean` | 其他 | 13 | 76 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib IndexTheory`) |
| `KTheory.lean` | 其他 | 10 | 56 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib KTheory`) |
| `LanglandsProgram.lean` | 其他 | 9 | 41 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib LanglandsProgram`) |
| `PercolationTheory.lean` | 其他 | 9 | 20 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib PercolationTheory`) |
| `SpectralTheory.lean` | 其他 | 11 | 13 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib SpectralTheory`) |
| `SylowTheorems.lean` | 其他 | 8 | 11 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.GroupTheory.Sylow, Mathlib.GroupTheory.PGroup`) |
| `AM_GM_Inequality.lean` | 分析 | 9 | 12 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Analysis.MeanInequalities, Mathlib.Analysis.Convex.SpecificFunctions.Basic`) |
| `AlgorithmAnalysis.lean` | 分析 | 16 | 17 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib AlgorithmAnalysis`) |
| `CalculusOfVariations.lean` | 分析 | 5 | 16 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib CalculusOfVariations`) |
| `CauchySchwarz.lean` | 分析 | 12 | 10 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Analysis.InnerProductSpace.Basic, Mathlib.LinearAlgebra.Matrix.PosDef`) |
| `ComplexAnalysis.lean` | 分析 | 11 | 14 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib ComplexAnalysis`) |
| `ComputationalComplexity.lean` | 分析 | 8 | 10 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib ComputationalComplexity`) |
| `DistributionTheory.lean` | 分析 | 10 | 45 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib DistributionTheory`) |
| `FejersTheorem.lean` | 分析 | 11 | 9 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib FejersTheorem`) |
| `FourierSeries.lean` | 分析 | 8 | 7 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Analysis.Fourier, Mathlib.MeasureTheory.Function.L2Space`) |
| `FourierTransform.lean` | 分析 | 17 | 20 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib FourierTransform`) |
| `FunctionalAnalysis.lean` | 分析 | 17 | 19 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib FunctionalAnalysis`) |
| `HahnBanachTheorem.lean` | 分析 | 11 | 18 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib HahnBanachTheorem`) |
| `HarmonicAnalysis.lean` | 分析 | 10 | 14 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib HarmonicAnalysis`) |
| `HolderInequality.lean` | 分析 | 7 | 18 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.MeasureTheory.Function.LpSpace, Mathlib.Analysis.MeanInequalities`) |
| `ImproperIntegral.lean` | 分析 | 6 | 6 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib ImproperIntegral`) |
| `LaxMilgram.lean` | 分析 | 11 | 14 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib LaxMilgram`) |
| `LebesgueDifferentiation.lean` | 分析 | 11 | 9 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib LebesgueDifferentiation`) |
| `MeasureTheory.lean` | 分析 | 10 | 13 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib MeasureTheory`) |
| `MinkowskiInequality.lean` | 分析 | 7 | 13 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.MeasureTheory.Function.LpSpace, Mathlib.Analysis.NormedSpace.Basic`) |
| `NavierStokes.lean` | 分析 | 10 | 22 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib NavierStokes`) |
| `NumericalAnalysis.lean` | 分析 | 7 | 8 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib NumericalAnalysis`) |
| `PlancherelTheorem.lean` | 分析 | 11 | 11 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib PlancherelTheorem`) |
| `SobolevSpace.lean` | 分析 | 12 | 20 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib SobolevSpace`) |
| `StokesTheorem.lean` | 分析 | 13 | 7 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib StokesTheorem`) |
| `UniformConvergence.lean` | 分析 | 5 | 13 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Topology.UniformSpace.Basic, Mathlib.Topology.UniformSpace.UniformConvergence, Mathlib.Analysis.NormedSpace.Basic`) |
| `ErgodicTheory.lean` | 动力系统/遍历论 | 9 | 8 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib ErgodicTheory`) |
| `ConnectionTheory.lean` | 微分几何 | 5 | 24 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib ConnectionTheory`) |
| `GeodesicEquation.lean` | 微分几何 | 10 | 18 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Geometry.RiemannianMetric.Geodesic`) |
| `HodgeConjecture.lean` | 微分几何 | 12 | 45 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib HodgeConjecture`) |
| `HodgeTheory.lean` | 微分几何 | 22 | 32 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib HodgeTheory`) |
| `IndexTheorem.lean` | 微分几何 | 10 | 30 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib IndexTheorem`) |
| `ManifoldDefinition.lean` | 微分几何 | 6 | 24 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Geometry.Manifold.ChartedSpace, Mathlib.Geometry.Manifold.SmoothManifold`) |
| `PrincipalBundle.lean` | 微分几何 | 8 | 42 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib PrincipalBundle`) |
| `RiemannHypothesis.lean` | 微分几何 | 14 | 28 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib RiemannHypothesis`) |
| `SymplecticGeometry.lean` | 微分几何 | 7 | 32 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib SymplecticGeometry`) |
| `SymplecticGeometry_advanced.lean` | 微分几何 | 6 | 25 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib SymplecticGeometry_advanced`) |
| `HeatEquation.lean` | 微分方程 | 10 | 12 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib HeatEquation`) |
| `PDETheory.lean` | 微分方程 | 7 | 7 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib PDETheory`) |
| `WaveEquation.lean` | 微分方程 | 8 | 13 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib WaveEquation`) |
| `WeakSolution.lean` | 微分方程 | 8 | 10 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib WeakSolution`) |
| `BrouwerFixedPoint.lean` | 拓扑 | 6 | 8 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Topology.BrouwerFixedPoint`) |
| `DifferentialTopology.lean` | 拓扑 | 9 | 5 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib DifferentialTopology`) |
| `GeometricTopology.lean` | 拓扑 | 10 | 34 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib GeometricTopology`) |
| `HairyBallTheorem.lean` | 拓扑 | 10 | 10 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Geometry.Manifold.Instances.Sphere`) |
| `HomotopyTypeTheory.lean` | 拓扑 | 6 | 8 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib HomotopyTypeTheory`) |
| `KnotTheory.lean` | 拓扑 | 17 | 39 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib KnotTheory`) |
| `LowDimensionalTopology.lean` | 拓扑 | 7 | 18 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib LowDimensionalTopology`) |
| `MorseTheory.lean` | 拓扑 | 20 | 30 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib MorseTheory`) |
| `PoincareConjecture.lean` | 拓扑 | 20 | 30 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib PoincareConjecture`) |
| `TychonoffTheorem.lean` | 拓扑 | 7 | 15 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Topology.Product, Mathlib.Topology.Compactness, Mathlib.Topology.Ultrafilter`) |
| `UrysohnLemma.lean` | 拓扑 | 6 | 23 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib UrysohnLemma`) |
| `AnalyticNumberTheory.lean` | 数论 | 13 | 13 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib AnalyticNumberTheory`) |
| `BirchSwinnertonDyer.lean` | 数论 | 11 | 46 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib BirchSwinnertonDyer`) |
| `ChineseRemainderTheorem.lean` | 数论 | 4 | 5 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib ChineseRemainderTheorem`) |
| `InfinitudeOfPrimes.lean` | 数论 | 5 | 5 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib InfinitudeOfPrimes`) |
| `ModularForm.lean` | 数论 | 11 | 17 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib ModularForm`) |
| `QuadraticReciprocity.lean` | 数论 | 9 | 10 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib QuadraticReciprocity`) |
| `RootsOfUnity.lean` | 数论 | 8 | 14 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.RingTheory.RootsOfUnity, Mathlib.NumberTheory.Cyclotomic`) |
| `TaniyamaShimura.lean` | 数论 | 10 | 43 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib TaniyamaShimura`) |
| `WeilConjectures.lean` | 数论 | 10 | 27 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib WeilConjectures`) |
| `p-adicHodgeTheory.lean` | 数论 | 6 | 33 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib p-adicHodgeTheory`) |
| `CentralLimitTheorem.lean` | 概率统计 | 8 | 8 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Probability.Distributions.Gaussian, Mathlib.Probability.CentralLimitTheorem`) |
| `InformationTheory.lean` | 概率统计 | 12 | 18 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib InformationTheory`) |
| `LawOfLargeNumbers.lean` | 概率统计 | 8 | 6 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Probability.Independence, Mathlib.Probability.IdentDistrib, Mathlib.Probability.StrongLaw`) |
| `MarkovChainErgodic.lean` | 概率统计 | 9 | 10 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Probability.MarkovChain`) |
| `MartingaleConvergence.lean` | 概率统计 | 11 | 12 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Probability.Martingale.Basic, Mathlib.Probability.Martingale.Convergence`) |
| `MaximumLikelihood.lean` | 概率统计 | 10 | 14 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Probability.Statistics`) |
| `ProbabilityTheory.lean` | 概率统计 | 11 | 12 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib ProbabilityTheory`) |
| `RandomMatrixTheory.lean` | 概率统计 | 8 | 15 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib RandomMatrixTheory`) |
| `Statistics.lean` | 概率统计 | 5 | 8 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib Statistics`) |
| `StochasticProcessesAdvanced.lean` | 概率统计 | 9 | 18 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib StochasticProcessesAdvanced`) |
| `StrongLawOfLargeNumbers.lean` | 概率统计 | 14 | 11 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Probability.StrongLaw`) |
| `Biology.lean` | 物理/其他应用 | 11 | 9 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Dynamics.OrdinaryDifferentialEquation, Mathlib.Analysis.SpecialFunctions.ExpLog`) |
| `Economics.lean` | 物理/其他应用 | 6 | 19 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Topology.FixedPoint.Brouwer, Mathlib.Analysis.Convex.Topology`) |
| `Finance.lean` | 物理/其他应用 | 12 | 11 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Probability.Martingale.Basic, Mathlib.Probability.StochasticProcess`) |
| `GameTheory.lean` | 物理/其他应用 | 5 | 22 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Topology.FixedPoint.Brouwer, Mathlib.Analysis.Convex.Topology`) |
| `GeneralRelativity.lean` | 物理/其他应用 | 6 | 23 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib GeneralRelativity`) |
| `MathematicalPhysics.lean` | 物理/其他应用 | 8 | 15 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib MathematicalPhysics`) |
| `QuantumMechanics.lean` | 物理/其他应用 | 10 | 23 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib QuantumMechanics`) |
| `StatisticalMechanics.lean` | 物理/其他应用 | 10 | 18 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib StatisticalMechanics`) |
| `YangMillsTheory.lean` | 物理/其他应用 | 4 | 35 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib YangMillsTheory`) |
| `ControlTheory.lean` | 算法/复杂度 | 7 | 10 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib ControlTheory`) |
| `DeepLearning.lean` | 算法/复杂度 | 6 | 7 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib DeepLearning`) |
| `MachineLearning.lean` | 算法/复杂度 | 8 | 8 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib MachineLearning`) |
| `OperationsResearch.lean` | 算法/复杂度 | 10 | 9 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Data.Matrix.Notation, Mathlib.LinearProgramming`) |
| `Optimization.lean` | 算法/复杂度 | 13 | 14 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib Optimization`) |
| `Optimization_advanced.lean` | 算法/复杂度 | 9 | 10 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib Optimization_advanced`) |
| `PvsNP.lean` | 算法/复杂度 | 9 | 8 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib PvsNP`) |
| `ReinforcementLearning.lean` | 算法/复杂度 | 9 | 9 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib ReinforcementLearning`) |
| `Combinatorics.lean` | 组合/图论 | 13 | 8 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Combinatorics.Pigeonhole, Mathlib.Combinatorics.DoubleCounting, Mathlib.Data.Nat.Choose.Basic, Mathlib.Combinatorics.SetFamily.Shadow`) |
| `Cryptography_advanced.lean` | 组合/图论 | 7 | 12 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib Cryptography_advanced`) |
| `GraphTheory.lean` | 组合/图论 | 13 | 17 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Combinatorics.SimpleGraph.Basic, Mathlib.Combinatorics.SimpleGraph.Connectivity, Mathlib.Combinatorics.SimpleGraph.Coloring, Mathlib.Combinatorics.SimpleGraph.Matching`) |
| `PigeonholePrinciple.lean` | 组合/图论 | 6 | 6 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib PigeonholePrinciple`) |
| `RamseyTheorem.lean` | 组合/图论 | 9 | 9 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib RamseyTheorem`) |
| `DerivedFunctor.lean` | 范畴论/高级结构 | 5 | 44 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib DerivedFunctor`) |
| `FunctorCategory.lean` | 范畴论/高级结构 | 7 | 12 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib FunctorCategory`) |
| `HigherCategoryTheory.lean` | 范畴论/高级结构 | 3 | 27 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib HigherCategoryTheory`) |
| `CantorDiagonal.lean` | 逻辑与基础 | 4 | 4 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib CantorDiagonal`) |
| `CompletenessTheorem.lean` | 逻辑与基础 | 11 | 14 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib CompletenessTheorem`) |
| `ComputabilityTheory.lean` | 逻辑与基础 | 7 | 7 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Computability.TuringMachine, Mathlib.Computability.Partrec, Mathlib.Computability.Halting`) |
| `Logic.lean` | 逻辑与基础 | 10 | 13 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib Logic`) |
| `MathematicalPhilosophy.lean` | 逻辑与基础 | 7 | 13 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib MathematicalPhilosophy`) |
| `ModelTheory.lean` | 逻辑与基础 | 3 | 3 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.ModelTheory.Basic, Mathlib.ModelTheory.Semantics, Mathlib.ModelTheory.Satisfiability, Mathlib.ModelTheory.Types`) |
| `ProofTheory.lean` | 逻辑与基础 | 5 | 5 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Logic.Basic`) |
| `ToposTheory.lean` | 逻辑与基础 | 5 | 7 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib ToposTheory`) |
| `UnivalentFoundations.lean` | 逻辑与基础 | 6 | 8 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib UnivalentFoundations`) |
| `ZornsLemma.lean` | 逻辑与基础 | 7 | 7 | C | 📖 定理陈述与概念解释（建议参考Mathlib4官方实现） | [搜索](https://leanprover-community.github.io/mathlib4_docs/) (`Mathlib.Order.Zorn`) |

### 分类说明

- **A类（✅ 完整形式化示例）**：sorry 数量为 0 或极少（<10%），可直接作为学习参考。
- **B类（⚠️ 部分证明）**：含有 sorry，但证明框架较完整（10%-50%），可用于理解证明结构。
- **C类（📖 定理陈述与概念解释）**：sorry 占绝大多数（>50%）或仅有声明，建议结合Mathlib4官方实现阅读。

## 50个核心定理

以下表格列出项目早期关注的50个核心定理（部分状态已根据实际代码更新）：

| # | 定理名称 | Mathlib4对应 | 文件名 | 领域 | 状态 |
|---|----------|--------------|--------|------|------|
| 1 | 拉格朗日定理 | `Subgroup.index_mul_card` | `LagrangeTheorem.lean` | 代数结构 | 📖 概念解释 |
| 2 | 第一同构定理 | `MonoidHom.quotientKerEquivRange` | `FirstIsomorphismTheorem.lean` | 代数结构 | 📖 概念解释 |
| 3 | 唯一分解定理 | `UniqueFactorizationMonoid` | `UniqueFactorization.lean` | 代数结构 | 📖 概念解释 |
| 4 | Cayley定理 | `Cayley.embedding` | `CayleyTheorem.lean` | 代数结构 | 📖 概念解释 |
| 5 | Sylow第一定理 | `Sylow.exists_subgroup_card_pow_prime` | `SylowFirstTheorem.lean` | 代数结构 | 📖 概念解释 |
| 6 | 中值定理 | `exists_hasDerivAt_eq_slope` | `MeanValueTheorem.lean` | 分析学 | 📖 概念解释 |
| 7 | Bolzano-Weierstrass定理 | `BolzanoWeierstrass.tendsto_subseq` | `BolzanoWeierstrass.lean` | 分析学 | 📖 概念解释 |
| 8 | 介值定理 | `intermediate_value_Icc` | `IntermediateValueTheorem.lean` | 分析学 | 📖 概念解释 |
| 9 | Heine-Borel定理 | `isCompact_iff_isClosed_bounded` | `HeineBorel.lean` | 分析学 | 📖 概念解释 |
| 10 | 费马小定理 | `ZMod.pow_card` | `FermatLittleTheorem.lean` | 数论 | 📖 概念解释 |
| 11 | 欧几里得算法 | `Nat.gcd_comm`, `EuclideanDomain` | `EuclideanAlgorithm.lean` | 数论 | 📖 概念解释 |
| 12 | 素数无穷多 | `Nat.infinite_setOf_prime` | `InfinitudeOfPrimes.lean` | 数论 | 📖 概念解释 |
| 13 | 康托尔定理 | `Cardinal.cantor` | `CantorDiagonal.lean` | 集合论 | 📖 概念解释 |
| 14 | 鸽巢原理 | `Fintype.exists_ne_map_eq_of_card_lt` | `PigeonholePrinciple.lean` | 组合数学 | 📖 概念解释 |
| 15 | 无穷鸽巢原理 | `infinite_pigeonhole` | `InfinitePigeonhole.lean` | 集合论 | 📖 概念解释 |
| 16 | 二次互反律 | `legendreSym.quadratic_reciprocity` | `QuadraticReciprocity.lean` | 数论 | 📖 概念解释 |
| 17 | 威尔逊定理 | `Nat.wilsons_lemma` | `WilsonTheorem.lean` | 数论 | 📖 概念解释 |
| 18 | 柯西-施瓦茨不等式 | `norm_inner_le_norm` | `CauchySchwarz.lean` | 泛函分析 | 📖 概念解释 |
| 19 | 凯莱-哈密顿定理 | `Matrix.aeval_self_charpoly` | `CayleyHamilton.lean` | 线性代数 | 📖 概念解释 |
| 20 | 阿廷-韦德伯恩定理 | `IsSemisimpleRing.exists_algEquiv_pi_matrix_end_mulOpposite` | `ArtinWedderburn.lean` | 环论 | 📖 概念解释 |
| 21 | 隐函数定理 | `HasStrictFDerivAt.implicitFunction` | `ImplicitFunctionTheorem.lean` | 分析学 | 📖 概念解释 |
| 22 | 逆函数定理 | `HasStrictFDerivAt.to_localInverse` | `InverseFunctionTheorem.lean` | 分析学 | 📖 概念解释 |
| 23 | 斯托克斯定理 | 发展中 | `StokesTheorem.lean` | 微分几何 | 📖 概念解释 |
| 24 | 乌雷松引理 | `exists_continuous_zero_one_of_isClosed` | `UrysohnsLemma.lean` | 拓扑学 | 📖 概念解释 |
| 25 | 蒂茨扩张定理 | `BoundedContinuousFunction.exists_extension` | `TietzeExtension.lean` | 拓扑学 | 📖 概念解释 |
| 26 | 一阶逻辑完备性定理 | `isSatisfiable_iff_all_finite_subsets_isSatisfiable` | `CompletenessTheorem.lean` | 数理逻辑 | 📖 概念解释 |
| 27 | 拉姆齐定理 | 发展中 | `RamseyTheorem.lean` | 组合数学 | 📖 概念解释 |
| 28 | 霍尔婚配定理 | `Finset.all_card_le_biUnion_card_iff_exists_injective` | `HallsMarriageTheorem.lean` | 组合数学 | 📖 概念解释 |
| 29 | 高斯-博内定理 | 发展中 | `GaussBonnet.lean` | 微分几何 | 📖 概念解释 |
| 30 | Faltings定理 | 发展中 | `FaltingsTheorem.lean` | 算术几何 | 📖 概念解释 |
| 31 | 中国剩余定理 | `ZMod.chineseRemainder` | `ChineseRemainderTheorem.lean` | 代数结构 | 📖 概念解释 |
| 32 | 原根存在定理 | `IsPrimitiveRoot` | `PrimitiveRootTheorem.lean` | 数论 | 📖 概念解释 |
| 33 | 希尔伯特基定理 | `Polynomial.isNoetherianRing` | `HilbertBasisTheorem.lean` | 代数结构 | 📖 概念解释 |
| 34 | Hilbert零点定理 | `Ideal.isVanishingIdeal` | `Nullstellensatz.lean` | 代数几何 | 📖 概念解释 |
| 35 | Picard-Lindelöf定理 | ODE存在唯一性框架 | `PicardLindelof.lean` | 微分方程 | 📖 概念解释 |
| 36 | Fourier级数收敛 | `hasSum_fourier_series` | `FourierSeriesConvergence.lean` | 调和分析 | 📖 概念解释 |
| 37 | Green定理 | 多元积分框架 | `GreenTheorem.lean` | 多元微积分 | 📖 概念解释 |
| 38 | 散度定理 | 流形积分框架 | `DivergenceTheorem.lean` | 多元微积分 | 📖 概念解释 |
| 39 | Morse理论基本定理 | `IsMorseFunction` | `MorseTheory.lean` | 微分拓扑 | 📖 概念解释 |
| 40 | 毛球定理 | `EulerCharacteristic` | `HairyBallTheorem.lean` | 代数拓扑 | 📖 概念解释 |
| 41 | Sard定理 | 光滑映射框架 | `SardTheorem.lean` | 微分拓扑 | 📖 概念解释 |
| 42 | Zorn引理 | `zorn_nonempty` | `ZornLemma.lean` | 集合论 | 📖 概念解释 |
| 43 | 良序定理 | `wellOrderingTheorem` | `WellOrderingTheorem.lean` | 集合论 | 📖 概念解释 |
| 44 | Atiyah-Singer指标定理 | 占位/框架 | `AtiyahSingerIndex.lean` | 全局分析 | 📖 概念解释 |
| 45 | Poincaré猜想（3维） | Perelman证明概述 | `PoincareConjecture3D.lean` | 几何拓扑 | 📖 概念解释 |

## 优先级分类（历史规划）

> 以下分类反映了项目早期的规划重点。当前实际代码状态请参见上方的"Lean4文件形式化状态总览"表格。

### P0级（基础代数）

- `LagrangeTheorem.lean` - 群论基础
- `FirstIsomorphismTheorem.lean` - 同态基本定理
- `UniqueFactorization.lean` - 环论基础
- `CayleyTheorem.lean` - 群的置换表示
- `SylowFirstTheorem.lean` - 有限群分类基础
- `ArtinWedderburn.lean` - 半单环分类
- `ChineseRemainderTheorem.lean` - 模算术
- `HilbertBasisTheorem.lean` - Noetherian环论
- `PrimitiveRootTheorem.lean` - 乘法群结构

### P1级（分析与拓扑）

- `MeanValueTheorem.lean` - 微积分核心
- `BolzanoWeierstrass.lean` - 实分析基础
- `IntermediateValueTheorem.lean` - 连续性核心
- `HeineBorel.lean` - 紧致性理论
- `BrouwerFixedPoint.lean` - 拓扑学应用
- `Compactness.lean` - 拓扑基础
- `ImplicitFunctionTheorem.lean` - 隐函数存在性
- `InverseFunctionTheorem.lean` - 局部可逆性
- `UrysohnsLemma.lean` - 正规空间刻画
- `TietzeExtension.lean` - 连续函数扩张
- `PicardLindelof.lean` - ODE存在唯一性
- `FourierSeriesConvergence.lean` - 调和分析
- `GreenTheorem.lean` - 多元微积分
- `DivergenceTheorem.lean` - 向量分析

### P2级（数论与逻辑）

- `FermatLittleTheorem.lean` - 初等数论
- `EuclideanAlgorithm.lean` - 算法数论
- `InfinitudeOfPrimes.lean` - 素数理论
- `QuadraticReciprocity.lean` - 二次互反律
- `WilsonTheorem.lean` - 威尔逊定理
- `CantorDiagonal.lean` - 集合论
- `PigeonholePrinciple.lean` - 组合数学
- `InfinitePigeonhole.lean` - 无穷组合
- `HallsMarriageTheorem.lean` - 二分图匹配
- `RamseyTheorem.lean` - Ramsey理论
- `FundamentalTheoremAlgebra.lean` - 代数与分析
- `GodelIncompleteness.lean` - 数理逻辑
- `CompletenessTheorem.lean` - 一阶逻辑完备性
- `ZornLemma.lean` - 选择公理等价形式
- `WellOrderingTheorem.lean` - 集合论基础

### P3级（微分几何与拓扑）

- `StokesTheorem.lean` - 微分几何统一定理
- `GaussBonnet.lean` - 曲率与拓扑
- `Nullstellensatz.lean` - 代数几何基础
- `MorseTheory.lean` - 临界点理论
- `HairyBallTheorem.lean` - 代数拓扑
- `SardTheorem.lean` - 微分拓扑

### P4级（前沿/挑战）

- `FaltingsTheorem.lean` - Mordell猜想
- `AtiyahSingerIndex.lean` - 指标理论（框架）
- `PoincareConjecture3D.lean` - 几何拓扑（框架）

## 使用指南

### 环境要求

```bash
# Lean 4 版本要求
lean --version  # 需要 ≥ 4.19.0

# 安装依赖
lake update mathlib
```

## 编译代码

```bash
# 在Lean4目录下
lake build

# 检查所有文件
lean *.lean
```

## 导入模块

```lean
import docs.形式化证明.Lean4.LagrangeTheorem
import docs.形式化证明.Lean4.FirstIsomorphismTheorem
```

## 代码结构

每个定理文件包含：

1. **Mathlib4对应说明** - 定理的Mathlib4位置和对应关系
2. **数学背景** - 定理的数学意义和历史
3. **形式化定义** - 核心概念的形式化
4. **主定理证明** - 完整的Lean4证明（A类）或证明框架（B/C类）
5. **应用示例** - 定理的具体应用

```
theorem_file.lean
├── 导入语句 (import)
├── 命名空间定义 (namespace)
├── 核心概念 (definitions)
├── 辅助引理 (lemmas)
├── 主定理证明 (main theorem)
└── 应用示例 (examples)
```

## 与Mathlib4的对齐策略

### 1. 直接引用

对于Mathlib4中已完整实现的定理，直接引用：

```lean
theorem my_theorem : ... := by
  exact Mathlib4.theorem_name
```

### 2. 补充证明

对于Mathlib4中有定义但缺少特定视角的证明，补充证明：

```lean
theorem alternative_proof : ... := by
  -- 不同的证明方法
```

### 3. 教学版本

为教学目的提供更详细的证明版本：

```lean
theorem detailed_proof : ... := by
  -- 分步详细注释
```

## 定理依赖关系

```
基础层:
├── PigeonholePrinciple.lean
├── InfinitePigeonhole.lean
└── EuclideanAlgorithm.lean

代数层:
├── LagrangeTheorem.lean
│   └── (使用) PigeonholePrinciple
├── FirstIsomorphismTheorem.lean
│   └── (使用) LagrangeTheorem
├── CayleyTheorem.lean
│   └── (使用) LagrangeTheorem
└── SylowFirstTheorem.lean
    └── (使用) LagrangeTheorem

分析层:
├── MeanValueTheorem.lean
├── BolzanoWeierstrass.lean
├── IntermediateValueTheorem.lean
└── HeineBorel.lean
    └── (使用) BolzanoWeierstrass

数论层:
├── FermatLittleTheorem.lean
│   └── (使用) LagrangeTheorem
├── InfinitudeOfPrimes.lean
└── UniqueFactorization.lean
    └── (使用) EuclideanAlgorithm

集合论层:
├── CantorDiagonal.lean
└── (与所有层关联)
```

## 扩展计划

### 近期（2026年Q2）

- [x] 补充更多群论定理（Cayley定理、Sylow定理）
- [x] 完善环论内容（欧几里得算法、素数无穷多）
- [x] 添加分析学基础（Bolzano-Weierstrass、介值定理）
- [ ] 添加线性代数基础（秩-零化度定理、谱定理）

### 中期（2026年Q3-Q4）

- [ ] 建立更完整的分析学分支（一致连续性、Riemann积分）
- [ ] 完善拓扑学内容（连通性、道路连通性）
- [ ] 添加测度论基础
- [ ] 添加复分析基础（Cauchy积分公式）

### 长期（2027年）

- [x] 代数几何初步（Hilbert零点定理）✅ 2026年4月
- [ ] 同调代数（长正合序列、导出函子）
- [ ] 范畴论应用（伴随函子、极限）
- [ ] 泛函分析基础（Hahn-Banach定理）
- [ ] 全指标定理形式化（长期目标）
- [ ] Ricci流理论（长期目标）

## 贡献指南

### 添加新定理

1. 在对应优先级目录下创建`.lean`文件
2. 按照模板填写Mathlib4对应信息
3. 提供完整的Lean4证明（针对A类示例）或清晰的概念解释框架（针对C类）
4. 添加数学背景和应用示例
5. 更新本README

### 代码规范

- 使用4空格缩进
- 遵循Mathlib4命名约定
- 添加详细的注释说明
- 包含完整的导入语句
- 每个定理包含Mathlib4对应关系注释

## 参考文献

### Mathlib4资源

- [Mathlib4文档](https://leanprover-community.github.io/mathlib4_docs/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)

### 数学参考

- Dummit, D. S., & Foote, R. M. *Abstract Algebra*
- Munkres, J. *Topology*
- Rudin, W. *Principles of Mathematical Analysis*
- Hardy, G. H., & Wright, E. M. *An Introduction to the Theory of Numbers*
- Boolos, G., et al. *Computability and Logic*

## 维护信息

- **最后更新**: 2026年4月15日
- **Mathlib4版本**: 4.19.0
- **Lean版本**: 4.19.0
- **维护者**: FormalMath项目团队
- **定理数量**: 168个Lean文件（A类11个 / B类7个 / C类150个）

## 许可证

本目录下的代码遵循与Mathlib4相同的许可证（Apache 2.0）。

---

**FormalMath项目**: 建立与Mathlib4紧密对齐的形式化数学知识体系
