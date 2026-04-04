/-
# 数学生物学基础定理

## 数学背景

数学生物学运用数学模型研究生物系统的动态行为。
核心领域包括种群动力学、流行病模型、进化博弈等。

## 核心结果
- 种群增长模型（Malthus, Verhulst）
- Lotka-Volterra捕食者-猎物模型
- SIR流行病模型
- Fisher-KPP方程（反应扩散）
- 进化稳定策略

## Mathlib4对应
- `Mathlib.Dynamics.OrdinaryDifferentialEquation`
- `Mathlib.Analysis.SpecialFunctions.ExpLog`

-/

import FormalMath.Mathlib.Analysis.SpecialFunctions.ExpDeriv
import FormalMath.Mathlib.Data.Real.Basic

namespace Biology

open Real Set Topology

/-
## 指数增长模型（Malthus, 1798）

最简单的种群模型：
dN/dt = rN

解：N(t) = N₀·e^{rt}

其中：
- N(t)：t时刻种群数量
- r：内禀增长率
- N₀：初始种群数量
-/
structure MalthusianGrowth where
  /-- 内禀增长率 -/
  r : ℝ
  /-- 初始种群数量 -/
  N0 : ℝ
  /-- 参数约束 -/
  r_realistic : r > 0
  N0_positive : N0 > 0

/-
## Malthus模型解的存在唯一性

**定理**：Malthus方程存在唯一解N(t) = N₀·e^{rt}。
-/
theorem malthus_solution_unique (M : MalthusianGrowth) :
    ∃! N : ℝ → ℝ,
      N 0 = M.N0 ∧
      Differentiable ℝ N ∧
      ∀ t, deriv N t = M.r * N t := by
  -- Malthus方程解的存在唯一性
  use fun t => M.N0 * Real.exp (M.r * t)
  constructor
  · -- 验证这是解
    constructor
    · -- 初始条件
      simp [M.N0_positive]
    constructor
    · -- 可微性
      apply Differentiable.mul
      · exact differentiable_const M.N0
      · apply Differentiable.exp
        exact Differentiable.const_mul differentiable_id' M.r
    · -- 满足微分方程
      intro t
      simp [deriv_mul, deriv_id'', differentiableAt_exp, deriv_const_mul, deriv_id'', mul_comm M.r]
  · -- 唯一性
    intro N h
    rcases h with ⟨h0, hdiff, heq⟩
    -- 应用ODE解的唯一性
    sorry -- 需要ODE理论

/-
## Logistic增长模型（Verhulst, 1838）

考虑资源限制的种群模型：
dN/dt = rN(1 - N/K)

其中：
- r：内禀增长率
- K：环境容纳量（carrying capacity）
-/
structure LogisticGrowth where
  /-- 内禀增长率 -/
  r : ℝ
  /-- 环境容纳量 -/
  K : ℝ
  /-- 初始种群数量 -/
  N0 : ℝ
  /-- 参数约束 -/
  r_positive : r > 0
  K_positive : K > 0
  N0_positive : N0 > 0

/-
## Logistic方程的解析解

**定理**：Logistic方程的解为：
N(t) = K / (1 + ((K - N₀)/N₀)·e^{-rt})

**性质**：
- N(t) → K 当 t → ∞
- 在 N = K/2 处增长最快
-/
theorem logistic_solution (L : LogisticGrowth) :
    ∃! N : ℝ → ℝ,
      N 0 = L.N0 ∧
      Differentiable ℝ N ∧
      ∀ t, deriv N t = L.r * N t * (1 - N t / L.K) := by
  -- Logistic方程解的存在唯一性
  use fun t => L.K / (1 + ((L.K - L.N0) / L.N0) * Real.exp (-L.r * t))
  constructor
  · -- 验证这是解
    constructor
    · -- 初始条件
      field_simp [L.N0_positive]
    constructor
    · -- 可微性（分母不为零）
      sorry -- 需要验证分母恒正
    · -- 满足微分方程
      intro t
      sorry -- 直接计算验证
  · -- 唯一性由ODE理论保证
    sorry

/-
## Logistic模型的长期行为

**定理**：对于任何正初始条件，N(t) → K。
-/
theorem logistic_convergence (L : LogisticGrowth) :
    let N t := L.K / (1 + ((L.K - L.N0) / L.N0) * Real.exp (-L.r * t))
    Tendsto N atTop (𝓝 L.K) := by
  -- Logistic解收敛到环境容纳量
  intro N
  have h : ∀ t, N t = L.K / (1 + ((L.K - L.N0) / L.N0) * Real.exp (-L.r * t)) := by intro t; rfl
  rw [show 𝓝 L.K = 𝓝 (L.K / (1 + 0)) by simp]
  apply Tendsto.div
  · exact tendsto_const_nhds
  · -- 证明分母收敛到1
    have h_exp : Tendsto (fun t => Real.exp (-L.r * t)) atTop (𝓝 0) := by
      apply tendsto_exp_atBot.comp
      apply Tendsto.atBot_mul_const_of_neg (by linarith [L.r_positive])
      exact tendsto_id
    have h_denom : Tendsto (fun t => 1 + ((L.K - L.N0) / L.N0) * Real.exp (-L.r * t)) atTop (𝓝 1) := by
      have : (fun t => 1 + ((L.K - L.N0) / L.N0) * Real.exp (-L.r * t)) =
               (fun t => 1) + (fun t => ((L.K - L.N0) / L.N0) * Real.exp (-L.r * t)) := by funext; ring
      rw [this]
      apply Tendsto.add
      · exact tendsto_const_nhds
      · -- 系数乘指数收敛到0
        have h_const : Tendsto (fun t => ((L.K - L.N0) / L.N0) : ℝ) atTop (𝓝 ((L.K - L.N0) / L.N0)) := tendsto_const_nhds
        have := Tendsto.mul h_const h_exp
        simp at this
        exact this
    convert h_denom
    simp
  · simp
  · -- 分母不收敛到0
    sorry -- 分母收敛到1

/-
## Lotka-Volterra捕食者-猎物模型

经典的二维种群交互模型：
dx/dt = αx - βxy  (猎物)
dy/dt = δxy - γy  (捕食者)

其中：
- x(t)：猎物数量
- y(t)：捕食者数量
- α：猎物增长率
- β：捕食率
- δ：转化率
- γ：捕食者死亡率
-/
structure LotkaVolterra where
  /-- 猎物增长率 -/
  alpha : ℝ
  /-- 捕食率 -/
  beta : ℝ
  /-- 转化率 -/
  delta : ℝ
  /-- 捕食者死亡率 -/
  gamma : ℝ
  /-- 初始条件 -/
  x0 : ℝ
  y0 : ℝ
  /-- 参数约束 -/
  alpha_pos : alpha > 0
  beta_pos : beta > 0
  delta_pos : delta > 0
  gamma_pos : gamma > 0
  x0_pos : x0 > 0
  y0_pos : y0 > 0

/-
## Lotka-Volterra系统的平衡点

平衡点满足 dx/dt = dy/dt = 0：
- 平凡平衡点：(0, 0)
- 共存平衡点：(γ/δ, α/β)
-/
def LVEquilibrium (LV : LotkaVolterra) (x y : ℝ) : Prop :=
  x ≥ 0 ∧ y ≥ 0 ∧
  LV.alpha * x - LV.beta * x * y = 0 ∧
  LV.delta * x * y - LV.gamma * y = 0

theorem lv_equilibrium_points (LV : LotkaVolterra) :
    LVEquilibrium LV 0 0 := by
  -- 验证(0,0)是平衡点
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · ring
  · ring

theorem lv_coexistence_equilibrium (LV : LotkaVolterra) :
    LVEquilibrium LV (LV.gamma / LV.delta) (LV.alpha / LV.beta) := by
  -- 验证共存平衡点
  constructor
  · -- x > 0
    apply div_nonneg
    · linarith [LV.gamma_pos]
    · linarith [LV.delta_pos]
  constructor
  · -- y > 0
    apply div_nonneg
    · linarith [LV.alpha_pos]
    · linarith [LV.beta_pos]
  constructor
  · -- dx/dt = 0
    field_simp [LV.beta_pos]
    ring
  · -- dy/dt = 0
    field_simp [LV.delta_pos]
    ring

/-
## Lotka-Volterra系统的首次积分

**定理**：函数 H(x,y) = δx - γln(x) + βy - αln(y) 是首次积分。
即：dH/dt = 0 沿解曲线。

这解释了为什么解是周期性的。
-/
def LotkaVolterraIntegral (LV : LotkaVolterra) (x y : ℝ) : ℝ :=
  LV.delta * x - LV.gamma * Real.log x + LV.beta * y - LV.alpha * Real.log y

theorem lv_first_integral (LV : LotkaVolterra) :
    let H := LotkaVolterraIntegral LV
    -- 沿解曲线H为常数
    sorry := by
  -- 证明H是首次积分
  -- dH/dt = (∂H/∂x)(dx/dt) + (∂H/∂y)(dy/dt)
  -- = (δ - γ/x)(αx - βxy) + (β - α/y)(δxy - γy)
  -- = (δ - γ/x)·x·(α - βy) + (β - α/y)·y·(δx - γ)
  -- = (δx - γ)(α - βy) + (βy - α)(δx - γ)
  -- = 0
  sorry -- 直接计算

/-
## SIR流行病模型

Kermack-McKendrick (1927) 提出的经典模型：
dS/dt = -βSI/N
dI/dt = βSI/N - γI
dR/dt = γI

其中：
- S：易感者数量
- I：感染者数量
- R：康复/移除者数量
- N = S + I + R：总人口
- β：传染率
- γ：康复率
- R₀ = β/γ：基本再生数
-/
structure SIRModel where
  /-- 总人口 -/
  N : ℝ
  /-- 传染率 -/
  beta : ℝ
  /-- 康复率 -/
  gamma : ℝ
  /-- 初始条件 -/
  S0 : ℝ
  I0 : ℝ
  R0 : ℝ
  /-- 参数约束 -/
  N_positive : N > 0
  beta_pos : beta > 0
  gamma_pos : gamma > 0
  S0_nonneg : S0 ≥ 0
  I0_nonneg : I0 ≥ 0
  R0_nonneg : R0 ≥ 0
  total_pop : S0 + I0 + R0 = N

/-
## 总人口守恒

**定理**：S(t) + I(t) + R(t) = N 对所有t成立。
-/
theorem sir_total_population_constant (SIR : SIRModel) :
    let dS_dt S I := -SIR.beta * S * I / SIR.N
    let dI_dt S I := SIR.beta * S * I / SIR.N - SIR.gamma * I
    let dR_dt I := SIR.gamma * I
    ∀ S I R : ℝ → ℝ,
      Differentiable ℝ S → Differentiable ℝ I → Differentiable ℝ R →
      S 0 = SIR.S0 → I 0 = SIR.I0 → R 0 = SIR.R0 →
      (∀ t, deriv S t = dS_dt (S t) (I t)) →
      (∀ t, deriv I t = dI_dt (S t) (I t)) →
      (∀ t, deriv R t = dR_dt (I t)) →
      ∀ t, S t + I t + R t = SIR.N := by
  -- 总人口守恒的证明
  intros dS_dt dI_dt dR_dt S I R hS hI hR hS0 hI0 hR0 hS_eq hI_eq hR_eq
  intro t
  -- 令Z(t) = S(t) + I(t) + R(t) - N
  -- Z'(t) = S' + I' + R' = -βSI/N + βSI/N - γI + γI = 0
  -- Z(0) = S0 + I0 + R0 - N = 0
  -- 因此Z(t) = 0对所有t
  sorry -- 需要ODE理论

/-
## 最终规模方程

**定理**：疫情的最终规模S(∞)满足：
log(S₀/S(∞)) = R₀·(1 - S(∞)/N)

其中 R₀ = β/γ 是基本再生数。
-/
theorem final_size_equation (SIR : SIRModel) :
    let R0 := SIR.beta / SIR.gamma
    -- 最终易感者比例满足超越方程
    sorry := by
  -- 最终规模方程的推导
  -- 由dR/dS = -γN/(βS) = -1/(R₀·S/N)
  -- 积分得：R(∞) - R(0) = -(N/R₀)·log(S(∞)/S(0))
  -- 利用S(∞) + I(∞) + R(∞) = N 和 I(∞) = 0
  sorry -- 需要积分

/-
## 阈值定理

**定理**：当 R₀ > 1 时，疫情会发生（I达到峰值）；
当 R₀ ≤ 1 时，感染者单调递减。
-/
theorem epidemic_threshold (SIR : SIRModel) :
    let R0 := SIR.beta / SIR.gamma
    R0 > 1 ↔ ∃ t, SIR.I0 < sorry := by
  -- 阈值定理
  -- dI/dt > 0 当且仅当 βS/N > γ
  -- 即 S/N > γ/β = 1/R₀
  -- 由于S递减，如果S(0)/N > 1/R₀（即R₀ > N/S(0)），则I先增后减
  sorry -- 需要分析dI/dt的符号

/-
## Fisher-KPP方程（反应扩散方程）

描述空间扩展的种群：
∂u/∂t = D·∂²u/∂x² + r·u·(1 - u/K)

这是偏微分方程，在Lean中需要特殊处理。
-/
structure FisherKPP where
  /-- 扩散系数 -/
  D : ℝ
  /-- 增长率 -/
  r : ℝ
  /-- 环境容纳量 -/
  K : ℝ
  /-- 参数约束 -/
  D_positive : D > 0
  r_positive : r > 0
  K_positive : K > 0

/-
## 行波解

Fisher-KPP方程存在形式为 u(x,t) = φ(x - ct) 的行波解，
其中c是波速，φ是波形函数。

**定理**：行波解存在的最小波速为 c* = 2√(Dr)。
-/
theorem minimal_wave_speed (FK : FisherKPP) :
    let c_star := 2 * Real.sqrt (FK.D * FK.r)
    -- 存在波速为c的行波解当且仅当c ≥ c*
    sorry := by
  -- 行波解的存在性
  -- 将行波形式代入PDE，得到ODE：
  -- -cφ' = Dφ'' + rφ(1 - φ/K)
  -- 这是非线性ODE，可以证明当c ≥ 2√(Dr)时存在连接0和K的解
  sorry -- 需要PDE理论

/-
## Leslie矩阵模型（离散时间年龄结构模型）

n(t+1) = L·n(t)

其中L是Leslie矩阵，n(t)是年龄结构向量。
-/
structure LeslieMatrix (k : ℕ) where
  /-- 生育率（第一行） -/
  fertility : Fin k → ℝ
  /-- 存活率（次对角线） -/
  survival : Fin (k - 1) → ℝ
  /-- 非负性约束 -/
  fertility_nonneg : ∀ i, fertility i ≥ 0
  survival_nonneg : ∀ i, survival i ≥ 0
  /-- 至少一个生育率为正 -/
  fertility_positive : ∃ i, fertility i > 0

/-
## Perron-Frobenius定理在人口学中的应用

**定理**：Leslie矩阵有唯一的正特征值λ（主导特征值），
对应正特征向量。长期行为：n(t) ≈ C·λ^t·v。

λ > 1：种群增长
λ = 1：种群稳定
λ < 1：种群衰退
-/
theorem leslie_dominant_eigenvalue {k : ℕ} (L : LeslieMatrix k) :
    -- 存在唯一正特征值
    sorry := by
  -- Perron-Frobenius定理的应用
  -- Leslie矩阵是不可约非负矩阵
  -- 因此存在唯一正特征值
  sorry -- 需要Perron-Frobenius定理

end Biology
