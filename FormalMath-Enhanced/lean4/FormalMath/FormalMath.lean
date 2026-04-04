/-
# FormalMath - Lean4形式化数学库

本库包含70个经典数学定理的形式化，涵盖：
- 分析学（微积分、实分析、复分析）
- 代数学（群论、环论、域论、模论）
- 几何与拓扑（微分几何、代数拓扑）
- 概率与统计（概率论、数理统计、随机过程）

## 项目信息
- 版本: 4.19.0
- 依赖: Mathlib4 v4.19.0
- 许可证: MIT
-/

-- 分析学进阶（P1级）
import FormalMath.TaylorTheorem
import FormalMath.ImproperIntegral
import FormalMath.UniformConvergence
import FormalMath.FourierSeries
import FormalMath.GammaFunction

-- 代数学进阶（P2级）
import FormalMath.SylowTheorems
import FormalMath.PrincipalIdealDomain
import FormalMath.FieldExtension
import FormalMath.GaloisGroup
import FormalMath.ModuleTheory

-- 几何与拓扑（P2级）
import FormalMath.FundamentalGroup
import FormalMath.ManifoldDefinition
import FormalMath.CurvatureTensor
import FormalMath.GeodesicEquation
import FormalMath.DeRhamCohomology

-- 概率与统计（P3级）
import FormalMath.LawOfLargeNumbers
import FormalMath.CentralLimitTheorem
import FormalMath.MartingaleConvergence
import FormalMath.MarkovChainErgodic
import FormalMath.MaximumLikelihood
