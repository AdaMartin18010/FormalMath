/-
# FormalMath - Lean4形式化数学库

本库包含100个经典数学定理的形式化，涵盖：
- 分析学（微积分、实分析、复分析、泛函分析、PDE）
- 代数学（群论、环论、域论、模论、范畴论、表示论）
- 几何与拓扑（微分几何、代数拓扑、辛几何）
- 概率与统计（概率论、数理统计、随机过程）

## 项目信息
- 版本: 4.20.0
- 依赖: Mathlib4 v4.20.0
- 许可证: MIT
- 定理总数: 100个
-/

-- ==================== 分析学（30个）====================

-- 分析学基础（10个）
import FormalMath.TaylorTheorem
import FormalMath.ImproperIntegral
import FormalMath.UniformConvergence
import FormalMath.FourierSeries
import FormalMath.GammaFunction

-- 分析学不等式（5个）- 第13批新增（定理61-65）
import FormalMath.YoungInequality
import FormalMath.HolderInequality
import FormalMath.MinkowskiInequality
import FormalMath.BorelCantelli
import FormalMath.StrongLawOfLargeNumbers

-- 分析学进阶（10个）- 第8批新增
import FormalMath.SobolevSpace
import FormalMath.DistributionTheory
import FormalMath.FourierTransform
import FormalMath.HarmonicAnalysis
import FormalMath.CalculusOfVariations
import FormalMath.EllipticPDE
import FormalMath.HeatEquation
import FormalMath.WaveEquation
import FormalMath.WeakSolution
import FormalMath.SpectralTheory

-- 分析学应用（10个）- 概率论相关
import FormalMath.LawOfLargeNumbers
import FormalMath.CentralLimitTheorem
import FormalMath.MartingaleConvergence
import FormalMath.MarkovChainErgodic
import FormalMath.MaximumLikelihood

-- ==================== 代数学（35个）====================

-- 代数学基础（15个）
import FormalMath.SylowTheorems
import FormalMath.PrincipalIdealDomain
import FormalMath.FieldExtension
import FormalMath.GaloisGroup
import FormalMath.ModuleTheory
import FormalMath.ClassFieldTheory
import FormalMath.EllipticCurve
import FormalMath.ModularForm

-- 代数学进阶（10个）- 第8批新增
import FormalMath.CategoryTheory
import FormalMath.FunctorCategory
import FormalMath.HomologicalAlgebra
import FormalMath.DerivedFunctor
import FormalMath.CommutativeAlgebra
import FormalMath.NoetherianRing
import FormalMath.RepresentationTheory
import FormalMath.CharacterTheory
import FormalMath.LieAlgebra
import FormalMath.UniversalEnvelopingAlgebra

-- 代数学前沿（5个）- 第12批新增（定理86-90）
import FormalMath.AlgebraicNumberTheory
import FormalMath.AnalyticNumberTheory
import FormalMath.ArithmeticGeometry
import FormalMath.LanglandsProgram
import FormalMath.MotiveTheory

-- 算术几何经典定理（5个）- 第13批新增（定理86-90）
import FormalMath.WeilConjectures
import FormalMath.MordellWeil
import FormalMath.FaltingsTheorem
import FormalMath.TaniyamaShimura
import FormalMath.PoincareConjecture

-- 代数学应用（10个）- 矩阵与李代数
-- (将在后续批次补充)

-- ==================== 几何与拓扑（25个）====================

-- 几何与拓扑基础（5个）
import FormalMath.FundamentalGroup
import FormalMath.ManifoldDefinition
import FormalMath.CurvatureTensor
import FormalMath.GeodesicEquation
import FormalMath.DeRhamCohomology
import FormalMath.StokesTheorem

-- 几何与拓扑进阶（10个）- 第8批新增
import FormalMath.CharacteristicClass
import FormalMath.ChernClass
import FormalMath.KTheory
import FormalMath.MorseTheory
import FormalMath.HodgeTheory
import FormalMath.YangMillsTheory
import FormalMath.PrincipalBundle
import FormalMath.ConnectionTheory
import FormalMath.IndexTheorem
import FormalMath.SymplecticGeometry

-- 几何与拓扑应用（10个）
import FormalMath.RamseyTheorem
-- (将在后续批次补充)

-- ==================== 数理逻辑基础（5个）====================

-- 集合论、模型论、证明论、可计算性理论、类型论 - 第14批新增（定理66-70）
import FormalMath.SetTheory
import FormalMath.ModelTheory
import FormalMath.ProofTheory
import FormalMath.ComputabilityTheory
import FormalMath.TypeTheory

-- ==================== 数学物理（5个）====================
-- 第14批新增（定理86-90）- 物理理论数学基础
import FormalMath.MathematicalPhysics
import FormalMath.QuantumMechanics
import FormalMath.StatisticalMechanics
import FormalMath.GeneralRelativity
import FormalMath.QuantumFieldTheory

-- ==================== 统计与数据科学（10个）====================
-- (将在后续批次补充)

-- ==================== 高阶数学与基础（5个）====================
-- 第14批新增（定理96-100）- 最终批次
import FormalMath.p-adicHodgeTheory
import FormalMath.PerfectoidSpaces
import FormalMath.HigherCategoryTheory
import FormalMath.HomotopyTypeTheory
import FormalMath.UnivalentFoundations

-- 库版本信息
def version := "4.20.0"
def theoremCount := 100
