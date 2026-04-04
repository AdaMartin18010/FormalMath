/-
# 最优化进阶 (Advanced Optimization)

## 数学背景

最优化理论研究在给定约束条件下寻找函数极值的方法，
在运筹学、机器学习、经济学等领域有广泛应用。

核心问题分类：
- 无约束优化：min f(x)，x ∈ ℝⁿ
- 等式约束优化：min f(x)，s.t. h(x) = 0
- 不等式约束优化：min f(x)，s.t. g(x) ≤ 0
- 凸优化：f凸函数，约束集凸集
- 非凸优化：可能存在多个局部极值

核心算法：
- 梯度下降法及其变体
- Newton法和拟Newton法
- 内点法
- 随机优化算法

## 核心定理
- 一阶最优性条件（KKT条件）
- 二阶最优性条件
- 对偶理论（强对偶、弱对偶）
- 收敛性分析（凸情形、非凸情形）

## 参考
- Boyd & Vandenberghe, "Convex Optimization"
- Nocedal & Wright, "Numerical Optimization"
- Bertsekas, "Nonlinear Programming"
- Rockafellar, "Convex Analysis"

## 形式化说明
最优化理论的形式化涉及凸分析、变分分析和数值分析。
本文件建立KKT理论和收敛性分析的框架。
完整证明需要非光滑分析和算子理论工具。
-/

import FormalMath.Mathlib.Analysis.Calculus.Gradient.Basic
import FormalMath.Mathlib.Analysis.Calculus.FDeriv.Basic
import FormalMath.Mathlib.Analysis.InnerProductSpace.PiL2

namespace OptimizationAdvanced

open Real Filter Topology Set

variable {n m p : ℕ}

/-
## 约束优化问题的标准形式

标准形式的优化问题：
minimize    f(x)
subject to  gᵢ(x) ≤ 0,  i = 1,...,m    (不等式约束)
            hⱼ(x) = 0,  j = 1,...,p    (等式约束)

其中：
- f: ℝⁿ → ℝ 是目标函数
- gᵢ: ℝⁿ → ℝ 是不等式约束函数
- hⱼ: ℝⁿ → ℝ 是等式约束函数

可行集：所有满足约束的x的集合。
-/
structure ConstrainedOptimizationProblem where
  /-- 目标函数 -/
  f : (Fin n → ℝ) → ℝ
  /-- 不等式约束函数（m个） -/
  g : (Fin m → ((Fin n → ℝ) → ℝ))
  /-- 等式约束函数（p个） -/
  h : (Fin p → ((Fin n → ℝ) → ℝ))
  /-- 目标函数可微 -/
  h_f_diff : Differentiable ℝ f
  /-- 约束函数可微 -/
  h_g_diff : ∀ i, Differentiable ℝ (g i)
  h_h_diff : ∀ j, Differentiable ℝ (h j)

/-- 可行集：满足所有约束的点 -/
def FeasibleSet (prob : ConstrainedOptimizationProblem) : 
    Set (Fin n → ℝ) :=
  {x | (∀ i, prob.g i x ≤ 0) ∧ (∀ j, prob.h j x = 0)}

/-- 局部最优解 -/
def IsLocalMinimum (prob : ConstrainedOptimizationProblem) 
    (x_star : Fin n → ℝ) : Prop :=
  x_star ∈ FeasibleSet prob ∧ 
  ∃ ε > 0, ∀ x ∈ FeasibleSet prob, dist x x_star < ε → 
    prob.f x_star ≤ prob.f x

/-
## Lagrange函数（Lagragian）

定义：L(x, λ, μ) = f(x) + Σ λᵢgᵢ(x) + Σ μⱼhⱼ(x)

其中：
- λᵢ ≥ 0：不等式约束的Lagrange乘子
- μⱼ ∈ ℝ：等式约束的Lagrange乘子

Lagrange函数将约束优化转化为无约束优化，
是KKT条件和对偶理论的基础。
-/
def Lagrangian (prob : ConstrainedOptimizationProblem)
    (x : Fin n → ℝ) (λ : Fin m → ℝ) (μ : Fin p → ℝ) : ℝ :=
  prob.f x + ∑ i, λ i * prob.g i x + ∑ j, μ j * prob.h j x

/-
## KKT条件（Karush-Kuhn-Tucker条件）

约束优化问题的一阶最优性必要条件：

1. 平稳性（Stationarity）：∇ₓL = 0
   ∇f(x*) + Σ λᵢ∇gᵢ(x*) + Σ μⱼ∇hⱼ(x*) = 0

2. 原始可行性（Primal Feasibility）：
   gᵢ(x*) ≤ 0, hⱼ(x*) = 0

3. 对偶可行性（Dual Feasibility）：
   λᵢ ≥ 0

4. 互补松弛性（Complementary Slackness）：
   λᵢgᵢ(x*) = 0

KKT条件是Lagrange乘子法的推广，
在满足约束规格（如Slater条件、LICQ）时是最优解的必要条件。
-/
structure KKTConditions (prob : ConstrainedOptimizationProblem) 
    (x_star : Fin n → ℝ) (λ : Fin m → ℝ) (μ : Fin p → ℝ) : Prop where
  /-- 平稳性：∇ₓL = 0 -/
  stationarity : ∇ (fun x ↦ Lagrangian prob x λ μ) x_star = 0
  /-- 原始可行性 -/
  primal_feasibility : x_star ∈ FeasibleSet prob
  /-- 对偶可行性 -/
  dual_feasibility : ∀ i, λ i ≥ 0
  /-- 互补松弛性：λᵢgᵢ(x*) = 0 -/
  complementary_slackness : ∀ i, λ i * prob.g i x_star = 0

/-
## KKT必要性定理

**定理**：设x*是局部最优解，且满足LICQ（线性无关约束规格），
则存在Lagrange乘子λ* ≥ 0和μ*，使得KKT条件成立。

**LICQ定义**：在最优解处，活跃约束的梯度线性无关。
活跃约束：gᵢ(x*) = 0的约束。

**证明思路**：
1. 利用隐函数定理处理等式约束
2. 使用Farkas引理或分离超平面定理处理不等式约束
3. 构造Lagrange乘子
-/
theorem kkt_necessary_condition 
    (prob : ConstrainedOptimizationProblem) 
    (x_star : Fin n → ℝ)
    (h_local_min : IsLocalMinimum prob x_star)
    (h_licq : -- 线性无关约束规格
      let active := {i | prob.g i x_star = 0}
      LinearIndependent ℝ (fun (i : active) ↦ ∇ (prob.g i.val) x_star)) :
    ∃ (λ : Fin m → ℝ) (μ : Fin p → ℝ),
      KKTConditions prob x_star λ μ := by
  -- KKT必要性定理证明概要
  --
  -- 步骤1：活跃约束分析
  -- 设I = {i : gᵢ(x*) = 0}为活跃约束集
  -- 由LICQ，{∇gᵢ(x*) : i ∈ I} ∪ {∇hⱼ(x*)}线性无关
  --
  -- 步骤2：切锥刻画
  -- 定义可行方向锥F = {d : d·∇gᵢ ≤ 0 (i∈I), d·∇hⱼ = 0}
  -- 由局部最优性，对可行方向d，有d·∇f ≥ 0
  --
  -- 步骤3：应用Farkas引理
  -- 若对满足d·∇gᵢ ≤ 0, d·∇hⱼ = 0的d，有d·∇f ≥ 0
  -- 则∇f在由∇gᵢ, ∇hⱼ生成的锥中
  -- 即∇f = -Σ λᵢ∇gᵢ - Σ μⱼ∇hⱼ，其中λᵢ ≥ 0
  --
  -- 步骤4：验证KKT条件
  -- 平稳性：由上述表示直接得到
  -- 原始可行性：由x*可行
  -- 对偶可行性：λᵢ ≥ 0
  -- 互补松弛性：对非活跃约束(i∉I)，设λᵢ = 0
  --
  sorry -- 这是约束优化的核心定理

/-
## KKT充分性定理（凸情形）

**定理**：设f和gᵢ是凸函数，hⱼ是仿射函数，
若(x*, λ*, μ*)满足KKT条件，则x*是全局最优解。

这是凸优化的重要性质：局部最优 = 全局最优。

**证明**：利用凸函数的次梯度性质。
对凸函数，f(y) ≥ f(x) + ∇f(x)ᵀ(y-x)。
-/
theorem kkt_sufficient_convex 
    (prob : ConstrainedOptimizationProblem) 
    (x_star : Fin n → ℝ) (λ : Fin m → ℝ) (μ : Fin p → ℝ)
    (h_convex_f : ConvexOn ℝ Set.univ prob.f)
    (h_convex_g : ∀ i, ConvexOn ℝ Set.univ (prob.g i))
    (h_affine_h : ∀ j, ∃ A b, prob.h j = fun x ↦ A *ᵥ x + b)
    (h_kkt : KKTConditions prob x_star λ μ) :
    ∀ x ∈ FeasibleSet prob, prob.f x_star ≤ prob.f x := by
  -- KKT充分性证明（凸情形）
  --
  -- 步骤1：利用凸性
  -- 对凸函数f，有f(x) ≥ f(x*) + ∇f(x*)ᵀ(x - x*)
  --
  -- 步骤2：展开Lagrange函数
  -- L(x,λ,μ) = f(x) + Σλᵢgᵢ(x) + Σμⱼhⱼ(x)
  --
  -- 步骤3：利用KKT条件
  -- 由平稳性：∇f(x*) = -Σλᵢ∇gᵢ(x*) - Σμⱼ∇hⱼ(x*)
  --
  -- 步骤4：估计f(x) - f(x*)
  -- f(x) - f(x*) ≥ ∇f(x*)ᵀ(x - x*)
  --             = -Σλᵢ∇gᵢ(x*)ᵀ(x-x*) - Σμⱼ∇hⱼ(x*)ᵀ(x-x*)
  --
  -- 步骤5：利用约束
  -- 由凸性：gᵢ(x) ≥ gᵢ(x*) + ∇gᵢ(x*)ᵀ(x-x*)
  -- 因gᵢ(x) ≤ 0且gᵢ(x*) ≤ 0
  -- 若λᵢ > 0，则gᵢ(x*) = 0（互补松弛）
  -- 所以∇gᵢ(x*)ᵀ(x-x*) ≤ gᵢ(x) - gᵢ(x*) ≤ 0
  --
  -- 步骤6：组合结果
  -- f(x) - f(x*) ≥ -Σλᵢ·0 - Σμⱼ·0 = 0
  sorry -- 凸优化的基本结果

/-
## 拉格朗日对偶问题

原问题（Primal）：
min f(x)，s.t. g(x) ≤ 0, h(x) = 0

对偶函数：g(λ, μ) = infₓ L(x, λ, μ)

对偶问题（Dual）：
max g(λ, μ)，s.t. λ ≥ 0

弱对偶性：对偶问题的最优值 ≤ 原问题的最优值
-/
def DualFunction (prob : ConstrainedOptimizationProblem)
    (λ : Fin m → ℝ) (μ : Fin p → ℝ) : ℝ :=
  ⨅ x, Lagrangian prob x λ μ

/-- 对偶问题最优值 -/
def DualOptimalValue (prob : ConstrainedOptimizationProblem) : ℝ :=
  ⨆ (λ : Fin m → ℝ) (μ : Fin p → ℝ) (_ : ∀ i, λ i ≥ 0), 
    DualFunction prob λ μ

/-- 原问题最优值 -/
def PrimalOptimalValue (prob : ConstrainedOptimizationProblem) : ℝ :=
  ⨅ x ∈ FeasibleSet prob, prob.f x

/-
## 弱对偶定理

**定理**：对任意λ ≥ 0和μ，有
g(λ, μ) ≤ p*

其中p*是原问题最优值。

**证明**：对任意可行x，
g(λ, μ) ≤ L(x, λ, μ) = f(x) + Σλᵢgᵢ(x) + Σμⱼhⱼ(x) ≤ f(x)
因为gᵢ(x) ≤ 0, hⱼ(x) = 0, λᵢ ≥ 0。
取下确界得证。
-/
theorem weak_duality 
    (prob : ConstrainedOptimizationProblem) :
    ∀ (λ : Fin m → ℝ) (μ : Fin p → ℝ), 
      (∀ i, λ i ≥ 0) → 
      DualFunction prob λ μ ≤ PrimalOptimalValue prob := by
  -- 弱对偶性证明
  --
  -- 步骤1：对偶函数定义
  -- g(λ,μ) = infₓ L(x,λ,μ)
  --
  -- 步骤2：对可行x估计
  -- 若x可行：gᵢ(x) ≤ 0, hⱼ(x) = 0
  -- 则L(x,λ,μ) = f(x) + Σλᵢgᵢ(x) ≤ f(x)（因为λᵢ ≥ 0）
  --
  -- 步骤3：对偶函数上界
  -- g(λ,μ) ≤ L(x,λ,μ) ≤ f(x) 对所有可行x
  -- 所以g(λ,μ) ≤ inf_{可行x} f(x) = p*
  sorry -- 对偶理论的基本结果

/-
## 强对偶定理（凸情形）

**定理**：在凸性假设和Slater条件下，强对偶性成立：
d* = p*

且若p*有限，则对偶问题达到最优值。

**Slater条件**：存在严格可行点x̃，使得
- gᵢ(x̃) < 0（严格不等式）
- hⱼ(x̃) = 0

强对偶性是凸优化的核心性质。
-/
theorem strong_duality_convex 
    (prob : ConstrainedOptimizationProblem)
    (h_convex_f : ConvexOn ℝ Set.univ prob.f)
    (h_convex_g : ∀ i, ConvexOn ℝ Set.univ (prob.g i))
    (h_affine_h : ∀ j, ∃ A b, prob.h j = fun x ↦ A *ᵥ x + b)
    (h_slater : ∃ x_tilde, (∀ i, prob.g i x_tilde < 0) ∧ 
      (∀ j, prob.h j x_tilde = 0)) :
    DualOptimalValue prob = PrimalOptimalValue prob := by
  -- 强对偶性证明概要
  --
  -- 步骤1：构造分离超平面
  -- 考虑集合A = {(u,v,t) | ∃x, gᵢ(x) ≤ uᵢ, hⱼ(x) = vⱼ, f(x) ≤ t}
  -- 和点(0, 0, p*)
  --
  -- 步骤2：应用超平面分离定理
  -- 由Slater条件，A的内部非空
  -- (0,0,p*)不在A的内部
  -- 存在分离超平面
  --
  -- 步骤3：构造Lagrange乘子
  -- 分离超平面的法向量给出(λ*, μ*, 1)
  -- 其中λ* ≥ 0
  --
  -- 步骤4：验证最优性
  -- 证明g(λ*, μ*) = p*
  -- 由弱对偶性，g(λ*, μ*) ≤ p*
  -- 由构造，g(λ*, μ*) ≥ p*
  --
  sorry -- 凸优化的核心定理

/-
## 梯度下降法

无约束优化问题 min f(x) 的基本迭代算法：
x_{k+1} = x_k - α_k ∇f(x_k)

其中α_k > 0是步长（学习率）。

**收敛性**：对凸且L-光滑的函数，
使用适当步长时，f(x_k) → f*。
-/
structure GradientDescent where
  /-- 目标函数 -/
  f : (Fin n → ℝ) → ℝ
  /-- 初始点 -/
  x0 : Fin n → ℝ
  /-- 步长序列 -/
  alpha : ℕ → ℝ
  /-- 步长为正 -/
  h_alpha_pos : ∀ k, alpha k > 0
  /-- 函数可微 -/
  h_diff : Differentiable ℝ f

def GradientDescentIteration (gd : GradientDescent) : ℕ → Fin n → ℝ
  | 0 => gd.x0
  | k + 1 => 
    let xk := GradientDescentIteration gd k
    xk - gd.alpha k • ∇ gd.f xk

/-
## L-光滑性（L-smoothness）

函数f是L-光滑的，如果梯度是L-Lipschitz的：
‖∇f(x) - ∇f(y)‖ ≤ L‖x - y‖

等价于：f(y) ≤ f(x) + ∇f(x)ᵀ(y-x) + L/2‖y-x‖²

L-光滑性保证梯度下降的收敛性。
-/
def LSmooth (f : (Fin n → ℝ) → ℝ) (L : ℝ) : Prop :=
  L > 0 ∧ ∀ x y, ‖∇ f x - ∇ f y‖ ≤ L * ‖x - y‖

/-
## 梯度下降收敛性（凸情形）

**定理**：设f是凸且L-光滑的，使用固定步长α ∈ (0, 2/L)，
则梯度下降满足：
f(x_k) - f* ≤ ‖x_0 - x*‖² / (2αk)

即O(1/k)收敛率。

**证明思路**：
1. 利用L-光滑性得到下降引理
2. 利用凸性估计函数值差距
3. 递推得到收敛率
-/
theorem gradient_descent_convergence_convex 
    (gd : GradientDescent) (L : ℝ) (x_star : Fin n → ℝ)
    (h_convex : ConvexOn ℝ Set.univ gd.f)
    (h_smooth : LSmooth gd.f L)
    (h_optimal : ∇ gd.f x_star = 0)  -- x*是最优解
    (h_stepsize : ∀ k, gd.alpha k = 1 / L) :  -- 固定步长
    ∀ k, gd.f (GradientDescentIteration gd k) - gd.f x_star ≤ 
      ‖gd.x0 - x_star‖^2 / (2 * (1 / L) * k) := by
  -- 梯度下降收敛性证明（凸情形）
  --
  -- 步骤1：下降引理（Descent Lemma）
  -- 由L-光滑性：f(x_{k+1}) ≤ f(x_k) - α(1-αL/2)‖∇f(x_k)‖²
  -- 当α ≤ 1/L时，f(x_{k+1}) ≤ f(x_k) - (1/2L)‖∇f(x_k)‖²
  --
  -- 步骤2：凸性估计
  -- 由凸性：f(x_k) - f* ≤ ∇f(x_k)ᵀ(x_k - x*)
  --
  -- 步骤3：递推分析
  -- ‖x_{k+1} - x*‖² = ‖x_k - α∇f(x_k) - x*‖²
  --                 = ‖x_k - x*‖² - 2α∇f(x_k)ᵀ(x_k - x*) + α²‖∇f(x_k)‖²
  --                 ≤ ‖x_k - x*‖² - 2α(f(x_k) - f*) + α²‖∇f(x_k)‖²
  --
  -- 步骤4：组合估计
  -- 利用下降引理消去梯度项
  -- 递推得到累积误差界
  --
  -- 步骤5：收敛率
  -- f(x_k) - f* ≤ ‖x_0 - x*‖² / (2αk) = O(1/k)
  sorry -- 凸优化的基本收敛性结果

/-
## Newton法（无约束优化）

利用二阶信息的迭代方法：
x_{k+1} = x_k - [∇²f(x_k)]⁻¹ ∇f(x_k)

收敛速度更快（局部二次收敛），但计算代价更高。
-/
structure NewtonMethod where
  /-- 目标函数 -/
  f : (Fin n → ℝ) → ℝ
  /-- 初始点 -/
  x0 : Fin n → ℝ
  /-- Hessian矩阵 -/
  hessian : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ
  /-- 梯度 -/
  gradient : (Fin n → ℝ) → Fin n → ℝ

def NewtonIterationStep (nm : NewtonMethod) (x : Fin n → ℝ) : Fin n → ℝ :=
  x - (nm.hessian x)⁻¹ *ᵥ nm.gradient x

/-
## Newton法局部收敛性

**定理**：设f在局部最优解x*附近C²光滑，
且∇²f(x*)正定，则当初始点足够接近x*时，
Newton法二次收敛：

‖x_{k+1} - x*‖ ≤ C‖x_k - x*‖²

**证明思路**：
1. 利用Taylor展开
2. 证明在x*附近，Newton步近似最优
3. 建立二次收敛的递推关系
-/
theorem newton_method_local_convergence 
    (nm : NewtonMethod) (x_star : Fin n → ℝ) (L : ℝ)
    (h_optimal : nm.gradient x_star = 0)
    (h_hessian_posdef : Matrix.PosDef (nm.hessian x_star))
    (h_lipschitz : ∀ x y, ‖nm.hessian x - nm.hessian y‖ ≤ L * ‖x - y‖) :
    ∃ ε > 0, ∀ x0, ‖x0 - x_star‖ < ε →
      ∃ C > 0, ∀ k, 
        ‖NewtonIterationStep nm^[k] x0 - x_star‖ ≤ 
          C * ‖NewtonIterationStep nm^[k-1] x0 - x_star‖^2 := by
  -- Newton法局部收敛性证明
  --
  -- 步骤1：定义误差
  -- e_k = x_k - x*
  --
  -- 步骤2：Newton步分析
  -- x_{k+1} = x_k - H_k⁻¹g_k
  -- 其中H_k = ∇²f(x_k), g_k = ∇f(x_k)
  --
  -- 步骤3：Taylor展开
  -- g_k = g* + H*(x_k - x*) + O(‖x_k - x*‖²)
  --     = H*e_k + O(‖e_k‖²)  （因为g* = 0）
  --
  -- 步骤4：Hessian近似
  -- H_k = H* + O(‖e_k‖)
  -- H_k⁻¹ = H*⁻¹ + O(‖e_k‖)
  --
  -- 步骤5：误差递推
  -- e_{k+1} = e_k - H_k⁻¹g_k
  --         = e_k - (H*⁻¹ + O(‖e_k‖))(H*e_k + O(‖e_k‖²))
  --         = e_k - e_k + O(‖e_k‖²)
  --         = O(‖e_k‖²)
  --
  -- 步骤6：二次收敛
  -- ‖e_{k+1}‖ ≤ C‖e_k‖²
  sorry -- 二阶优化方法的核心结果

/-
## 内部点法（Interior Point Method）

求解不等式约束优化问题的有效算法。

核心思想：将不等式约束转化为障碍函数，
通过参数μ控制近似精度。

障碍问题：min f(x) - μ Σ log(-gᵢ(x))
当μ → 0时，解趋于原问题解。
-/
def BarrierFunction (prob : ConstrainedOptimizationProblem)
    (x : Fin n → ℝ) (mu : ℝ) : ℝ :=
  prob.f x - mu * ∑ i, Real.log (-(prob.g i x))

/-
## 内部点法收敛性

**定理**：在适当条件下，内部点法产生的序列
收敛到原问题的KKT点。

**复杂度**：
- 线性规划：O(√n · L)次迭代（L是输入精度）
- 凸二次规划：多项式时间
- 一般凸优化：依赖于障碍函数的Self-concordance
-/
theorem interior_point_convergence 
    (prob : ConstrainedOptimizationProblem)
    (mu_seq : ℕ → ℝ)  -- 障碍参数序列
    (h_mu_pos : ∀ k, mu_seq k > 0)
    (h_mu_tends_zero : Tendsto mu_seq atTop (𝓝 0))
    (x_seq : ℕ → Fin n → ℝ)  -- 迭代序列
    (h_barrier_opt : ∀ k, 
      x_seq k ∈ argmin (fun x ↦ BarrierFunction prob x (mu_seq k))) :
    ∃ x_limit λ_limit μ_limit,
      Tendsto x_seq atTop (𝓝 x_limit) ∧
      KKTConditions prob x_limit λ_limit μ_limit := by
  -- 内部点法收敛性证明概要
  --
  -- 步骤1：障碍函数性质
  -- 当μ → 0时，障碍问题的解趋于原问题可行集的边界
  --
  -- 步骤2：KKT条件分析
  -- 障碍问题的KKT条件：∇f(x) + Σ (μ/(-gᵢ(x)))∇gᵢ(x) = 0
  -- 定义λᵢ = μ/(-gᵢ(x))，则λᵢ > 0
  --
  -- 步骤3：极限分析
  -- 当μ → 0时，若gᵢ(x) < 0，则λᵢ → 0
  -- 若gᵢ(x) → 0，则λᵢ可能趋于有限值
  -- 互补松弛性在极限下保持
  --
  -- 步骤4：收敛性
  -- 由紧性论证，存在收敛子列
  -- 极限点满足原问题的KKT条件
  sorry -- 约束优化算法的高级结果

/-
## 次梯度方法（Subgradient Method）

处理非光滑凸优化的基本算法。

对凸但非光滑的函数f，次梯度g满足：
f(y) ≥ f(x) + gᵀ(y-x), ∀y

迭代：x_{k+1} = x_k - α_k g_k
其中g_k ∈ ∂f(x_k)是次梯度。
-/
def Subgradient (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : 
    Set (Fin n → ℝ) :=
  {g | ∀ y, f y ≥ f x + inner g (y - x)}

structure SubgradientMethod where
  /-- 目标函数 -/
  f : (Fin n → ℝ) → ℝ
  /-- 初始点 -/
  x0 : Fin n → ℝ
  /-- 步长序列 -/
  alpha : ℕ → ℝ
  /-- 次梯度选择函数 -/
  subgrad : (Fin n → ℝ) → Fin n → ℝ
  /-- 次梯度有效性 -/
  h_subgrad : ∀ x, subgrad x ∈ Subgradient f x

def SubgradientIteration (sg : SubgradientMethod) : ℕ → Fin n → ℝ
  | 0 => sg.x0
  | k + 1 =>
    let xk := SubgradientIteration sg k
    xk - sg.alpha k • sg.subgrad xk

/-
## 次梯度方法收敛性

**定理**：设f是凸且L-Lipschitz的，使用步长α_k = c/√k，
则次梯度方法满足：
min_{i≤k} f(x_i) - f* ≤ O(1/√k)

这比光滑情形的O(1/k)慢，是处理非光滑性的代价。
-/
theorem subgradient_method_convergence 
    (sg : SubgradientMethod) (L : ℝ) (x_star : Fin n → ℝ)
    (h_lipschitz : ∀ x y, |sg.f x - sg.f y| ≤ L * ‖x - y‖)
    (h_optimal : ∀ x, sg.f x_star ≤ sg.f x)
    (h_stepsize : ∀ k, sg.alpha k = 1 / Real.sqrt (k + 1)) :
    ∀ k, ⨅ i in Finset.Icc 0 k, sg.f (SubgradientIteration sg i) - sg.f x_star ≤ 
      L * ‖sg.x0 - x_star‖ / Real.sqrt (k + 1) := by
  -- 次梯度方法收敛性证明
  --
  -- 步骤1：距离估计
  -- ‖x_{k+1} - x*‖² = ‖x_k - α_k g_k - x*‖²
  --                 = ‖x_k - x*‖² - 2α_k g_kᵀ(x_k - x*) + α_k²‖g_k‖²
  --
  -- 步骤2：利用次梯度性质
  -- g_kᵀ(x_k - x*) ≥ f(x_k) - f(x*)
  --
  -- 步骤3：递推
  -- ‖x_{k+1} - x*‖² ≤ ‖x_k - x*‖² - 2α_k(f(x_k) - f*) + α_k²L²
  --
  -- 步骤4：求和
  -- 2Σ α_i(f(x_i) - f*) ≤ ‖x_0 - x*‖² + L²Σ α_i²
  --
  -- 步骤5：利用步长选择
  -- Σ 1/√i = O(√k), Σ 1/i = O(log k)
  -- 所以min_{i≤k}(f(x_i) - f*) = O(1/√k)
  sorry -- 非光滑优化的基本结果

/-
## 随机梯度下降（SGD）

机器学习中大规模优化的核心算法。

目标：min f(x) = (1/N) Σ f_i(x)

SGD迭代：x_{k+1} = x_k - α_k ∇f_{i_k}(x_k)
其中i_k随机采样。

计算复杂度：每步O(1)而非O(N)。
-/
structure StochasticGradientDescent where
  /-- 样本数量 -/
  N : ℕ
  /-- 分量函数 -/
  f_components : Fin N → (Fin n → ℝ) → ℝ
  /-- 完整目标函数 -/
  f : (Fin n → ℝ) → ℝ := fun x ↦ 
    (∑ i, f_components i x) / N
  /-- 初始点 -/
  x0 : Fin n → ℝ
  /-- 步长序列 -/
  alpha : ℕ → ℝ

def SGDIteration (sgd : StochasticGradientDescent) 
    (sample_seq : ℕ → Fin sgd.N) : ℕ → Fin n → ℝ
  | 0 => sgd.x0
  | k + 1 =>
    let xk := SGDIteration sgd sample_seq k
    let ik := sample_seq k
    xk - sgd.alpha k • ∇ (sgd.f_components ik) xk

/-
## SGD收敛性（凸情形）

**定理**：设每个f_i是凸且L-光滑的，使用递减步长α_k = O(1/k)，
则SGD满足：E[f(x̄_k)] - f* = O(1/√k)

其中x̄_k是迭代平均。

注：SGD的收敛率比全梯度下降慢，但每步计算代价低，
在大规模问题中更高效。
-/
theorem sgd_convergence_convex 
    (sgd : StochasticGradientDescent) 
    (sample_seq : ℕ → Fin sgd.N)
    (h_iid : ∀ k, sample_seq k = 
      fun _ ↦ Classical.choice ⟨inferInstance⟩)  -- 均匀采样
    (h_convex : ∀ i, ConvexOn ℝ Set.univ (sgd.f_components i))
    (h_stepsize : ∀ k, sgd.alpha k = 1 / (k + 1)) :
    let x_bar k := (∑ i in Finset.Icc 0 k, SGDIteration sgd sample_seq i) / (k + 1)
    ∀ k, sgd.f (x_bar k) - ⨅ x, sgd.f x ≤ 
      1 / Real.sqrt (k + 1) := by
  -- SGD收敛性证明概要
  --
  -- 步骤1：期望分析
  -- E[∇f_{i_k}(x_k)] = ∇f(x_k)（无偏估计）
  --
  -- 步骤2：方差控制
  -- E[‖∇f_{i_k}(x_k)‖²] ≤ σ² + ‖∇f(x_k)‖²
  --
  -- 步骤3：递推分析（类似次梯度方法）
  -- E[‖x_{k+1} - x*‖²] ≤ E[‖x_k - x*‖²] - 2α_k E[f(x_k) - f*] + α_k² G²
  --
  -- 步骤4：Jensen不等式
  -- f(x̄_k) ≤ (1/k) Σ f(x_i)
  --
  -- 步骤5：收敛率
  -- 适当选择步长，得到E[f(x̄_k)] - f* = O(1/√k)
  sorry -- 大规模优化的核心结果

/-
## 辅助定义 -/

notation "argmin " f => {x | ∀ y, f x ≤ f y}

def ⨅ (s : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : ℝ := sorry

end OptimizationAdvanced
