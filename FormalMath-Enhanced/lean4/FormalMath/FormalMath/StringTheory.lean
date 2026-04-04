/-
# 弦理论基础 (String Theory)

## 数学背景

弦理论是试图统一量子力学与广义相对论的量子引力理论，
认为基本粒子不是点状，而是1维的"弦"。

## 核心概念
- 弦的作用量（Nambu-Goto, Polyakov）
- 世界面与弦场论
- 紧化与Calabi-Yau流形
- T-对偶性
- 超弦理论
- M-理论

## 数学工具
- 共形场论
- 代数几何
- K-理论
- 表示论
- 拓扑学

## 参考
- Green, Schwarz & Witten "Superstring Theory" (Vol 1-2)
- Polchinski, J. "String Theory" (Vol 1-2)
- Becker, Becker & Schwarz "String Theory and M-Theory"
- McDuff & Salamon "J-holomorphic Curves and Symplectic Topology"
- 丘成桐、纳迪斯《大宇之形》

## 形式化说明
弦理论的数学结构极为丰富和复杂，
本文件提供基础框架和关键概念的形式化表述。
所有主要定理以详细框架+数学注释形式呈现，
为后续完整形式化奠定基础。
-/ 

import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.RepresentationTheory.Basic

namespace StringTheory

open Real Complex Manifold

/-! 
## 弦的世界面

弦在时空中扫过的2维曲面称为世界面。

**参数化**：Xᵘ(τ, σ)
- τ：世界面时间参数
- σ：空间参数（0 ≤ σ ≤ ℓ，ℓ是弦的长度）

**开弦**：有两个端点（σ ∈ [0, π]）
**闭弦**：没有端点，拓扑为圆（σ ∈ [0, 2π]，周期性）
-/ 

/-- 世界面参数：二维世界面的坐标 (τ, σ) -/
structure WorldsheetParameter where
  /-- 时间参数 τ -/
  tau : ℝ
  /-- 空间参数 σ -/
  sigma : ℝ
  deriving Inhabited

/-- 时空流形：d维Minkowski时空或更一般的弯曲时空 -/
structure Spacetime (d : ℕ) where
  /-- 底流形 -/
  manifold : Type*
  /-- 光滑结构 -/
  [smooth : SmoothManifoldWithCorners (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin d))) manifold]
  /-- 度规张量 g_μν -/
  metric : ∀ x : manifold, (TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin d))) x) →ₗ[ℝ]
    (TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin d))) x) →ₗ[ℝ] ℝ

/-- 世界面：2维参数空间，具有共形结构 -/
structure Worldsheet where
  /-- 底流形（2维）-/
  surface : Type*
  /-- 拓扑结构 -/
  [topological_space : TopologicalSpace surface]
  /-- 光滑结构 -/
  [smooth : ChartedSpace (EuclideanSpace ℝ (Fin 2)) surface]
  /-- 世界面度规 h_{ab} -/
  metric : ∀ w : surface, 
    (TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) w) →ₗ[ℝ]
    (TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) w) →ₗ[ℝ] ℝ

/-- 度规矩阵：用于表示二维度规张量的分量 -/
structure MetricMatrix where
  /-- h_{ττ} 分量 -/
  h_tautau : ℝ
  /-- h_{τσ} = h_{στ} 分量 -/
  h_tausigma : ℝ
  /-- h_{σσ} 分量 -/
  h_sigmasigma : ℝ

/-- 计算度规矩阵的行列式 -/
def MetricMatrix.det (h : MetricMatrix) : ℝ :=
  h.h_tautau * h.h_sigmasigma - h.h_tausigma^2

/-- 世界面度规：带符号检查的度规矩阵表示 -/
structure WorldsheetMetric extends MetricMatrix where
  /-- Lorentz符号要求：det(h) < 0 -/
  h_lorentzian : h_sigmasigma * h_tautau - h_tausigma^2 < 0

/-- 共形结构：度规的共形等价类 -/
structure ConformalStructure where
  /-- 代表元度规 -/
  representative : WorldsheetMetric
  /-- 共形因子空间 -/
  conformal_factor : ℝ → ℝ

/-! 
## 弦的作用量

**Nambu-Goto作用量**：
S = -T ∫ dτ dσ √(-det(γ))

其中：
- T = 1/(2πα') 是弦张力
- α' 是Regge斜率参数（具有长度平方的量纲）
- γ_{ab} = ∂ₐXᵘ ∂ᵦXᵛ ηᵤᵥ 是诱导度规

**Polyakov作用量**：
S = -(T/2) ∫ d²σ √(-h) h^{ab} ∂ₐXᵘ ∂ᵦXᵛ ηᵤᵥ

Polyakov作用量引入了世界面度规h_{ab}作为独立变量，
更容易进行量子化，且在经典极限下等价于Nambu-Goto作用量。
-/ 

/-- Regge斜率参数：弦理论的基本参数，决定弦的张力 -/
structure ReggeSlope where
  /-- 参数值 α' -/
  alpha_prime : ℝ
  /-- 正定性保证 -/
  h_pos : alpha_prime > 0

/-- 弦张力：T = 1/(2πα') -/
def StringTension (αp : ReggeSlope) : ℝ :=
  1 / (2 * π * αp.alpha_prime)

/-- 弦的嵌入映射：X^μ(τ, σ) -/
def StringEmbedding (d : ℕ) :=
  WorldsheetParameter → (Spacetime d).manifold

/-- 诱导度规：γ_{ab} = ∂_a X^μ ∂_b X^ν η_{μν}

这是时空度规在世界面上的拉回（pullback）。
对于d维Minkowski时空，η_{μν} = diag(-1, 1, ..., 1)。
-/ 
def InducedMetric {d : ℕ} (X : StringEmbedding d) (w : WorldsheetParameter) : MetricMatrix :=
  { h_tautau := sorry,  -- ∂_τ X^μ ∂_τ X^ν η_{μν}
    h_tausigma := sorry, -- ∂_τ X^μ ∂_σ X^ν η_{μν}
    h_sigmasigma := sorry -- ∂_σ X^μ ∂_σ X^ν η_{μν}
  }

/-- Nambu-Goto作用量：S = -T ∫ dτ dσ √(-det(γ))

这是弦理论的经典作用量，几何上等于世界面的面积。
最小作用量原理给出弦的经典运动方程。
-/ 
def NambuGotoAction {d : ℕ} (X : StringEmbedding d) (T : ℝ) : ℝ :=
  -T * sorry  -- ∫ dτ dσ √(-det(γ_{ab}))

/-- Polyakov作用量：S = -(T/2) ∫ d²σ √(-h) h^{ab} ∂_a X^μ ∂_b X^ν η_{μν}

这是弦理论的另一种表述，将世界面度规h_{ab}视为独立变量。
优点：
1. 作用量是场的一阶导数（而非Nambu-Goto中的平方根）
2. 更容易量子化
3. 显式表现出共形对称性
-/ 
def PolyakovAction {d : ℕ} (X : StringEmbedding d)
    (h : WorldsheetMetric) (T : ℝ) : ℝ :=
  -(T / 2) * sorry  -- ∫ d²σ √(-h) h^{ab} ∂_a X^μ ∂_b X^ν η_{μν}

/-! 
## 弦的运动方程与Virasoro约束

从Polyakov作用量变分得到：
1. 运动方程：(∂_τ² - ∂_σ²)X^μ = 0（2维波动方程）
2. 约束方程：能量-动量张量 T_{ab} = 0

**通解分解**：
X^μ(τ, σ) = X^μ_L(τ + σ) + X^μ_R(τ - σ)

其中X_L是左移波（向右传播），X_R是右移波（向左传播）。
-/ 

/-- 弦的运动方程：(∂_τ² - ∂_σ²)X^μ = 0

这是2维波动方程，描述弦的横向振动。
-/ 
def StringEquationOfMotion {d : ℕ} (X : StringEmbedding d) : Prop :=
  ∀ (τ σ : ℝ), 
    -- (∂²X^μ/∂τ² - ∂²X^μ/∂σ²) = 0 对所有μ成立
    sorry

/-- 左移波条件：X(τ, σ) = f(τ + σ) -/
def LeftMoving {d : ℕ} (X : StringEmbedding d) : Prop :=
  ∃ f : ℝ → (Spacetime d).manifold,
    ∀ w : WorldsheetParameter, X w = f (w.tau + w.sigma)

/-- 右移波条件：X(τ, σ) = g(τ - σ) -/
def RightMoving {d : ℕ} (X : StringEmbedding d) : Prop :=
  ∃ g : ℝ → (Spacetime d).manifold,
    ∀ w : WorldsheetParameter, X w = g (w.tau - w.sigma)

/-- 弦运动方程的通解分解定理

**定理**：满足运动方程的解可以唯一分解为左移波和右移波之和。

**证明思路**：
1. 引入光锥坐标：σ⁺ = τ + σ, σ⁻ = τ - σ
2. 在光锥坐标下，波动方程化为 ∂₊∂₋X = 0
3. 通解为 X = X_L(σ⁺) + X_R(σ⁻)
4. 唯一性由边界条件保证
-/ 
theorem string_solution_decomposition {d : ℕ} {X : StringEmbedding d}
    (h_solution : StringEquationOfMotion X) :
    ∃ (X_L X_R : ℝ → (Spacetime d).manifold),
      (∀ w, X w = X_L (w.tau + w.sigma) + X_R (w.tau - w.sigma)) ∧
      LeftMoving (fun w ↦ X_L (w.tau + w.sigma)) ∧
      RightMoving (fun w ↦ X_R (w.tau - w.sigma)) := by
  /- 【证明框架】
     
     步骤1：光锥坐标变换
     - 定义 σ⁺ = τ + σ, σ⁻ = τ - σ
     - 偏导数变换：∂_τ = ∂_+ + ∂_-, ∂_σ = ∂_+ - ∂_-
     
     步骤2：方程简化
     - 波动方程 ∂_τ²X - ∂_σ²X = 0 变为 4∂_+∂_-X = 0
     - 即 ∂_+∂_-X = 0
     
     步骤3：求解
     - 由 ∂_+∂_-X = 0，首先对σ⁻积分得 ∂_+X = f'(σ⁺)
     - 再对σ⁺积分得 X = f(σ⁺) + g(σ⁻)
     
     步骤4：验证
     - 验证 X_L(τ+σ) + X_R(τ-σ) 满足原方程
  -/
  sorry  -- 需要完整的流形值函数分析

/-! 
## 弦的量子化与质量壳条件

**正则量子化**：
[X^μ(τ, σ), P^ν(τ, σ')] = iℏ η^{μν} δ(σ - σ')

其中P^μ = T ∂_τ X^μ 是共轭动量。

**模式展开（闭弦）**：
X^μ(τ, σ) = x^μ + p^μ τ + i√(α'/2) Σ_{n≠0} (α^μ_n/n)e^{-2inτ}cos(2nσ)

**质量壳条件**：
M² = (4/α')(N + Ñ - 2)

其中 N = Σ_{n=1}^∞ α_{-n}·α_n 是左激发数算符，
Ñ = Σ_{n=1}^∞ ã_{-n}·ã_n 是右激发数算符。
-/ 

/-- 弦的振动模式 -/
structure StringMode where
  /-- 模式数（n > 0 对应产生算符，n < 0 对应湮灭算符）-/
  n : ℤ
  /-- 时空指标 μ = 0, 1, ..., d-1 -/
  mu : ℕ
  /-- 产生/湮灭算符的表示 -/
  operator : sorry  -- 需要希尔伯特空间上的算符代数

/-- 激发数算符：N = Σ_{n=1}^∞ α_{-n}·α_n -/
def ExcitationNumber (modes : List StringMode) : ℕ :=
  modes.filter (fun m => m.n < 0) |>.length

/-- 质量壳条件：M² = (4/α')(N + Ñ - a)

其中a是正规序常数（玻色弦a=2，超弦a=0）。
-/ 
def MassShellCondition (M : ℝ) (αp : ReggeSlope) (N Ntilde : ℕ) (a : ℝ) : Prop :=
  M^2 = (4 / αp.alpha_prime) * (N + Ntilde - a)

/-- Tachyon质量：M² = -4/α' < 0

这是弦理论的基态，具有负质量平方，表示不稳定。
超弦理论通过GSO投影消除了tachyon。
-/ 
def TachyonMassSq (αp : ReggeSlope) : ℝ :=
  -4 / αp.alpha_prime

/-- 无质量激发态定理

当N = Ñ = 1时，M = 0，对应于：
- 开弦：规范玻色子
- 闭弦：引力子（自旋2粒子）

这解释了为什么弦理论必然包含引力！
-/ 
theorem massless_excitations (αp : ReggeSlope) :
    MassShellCondition 0 αp 1 1 2 := by
  /- 【证明】
     M² = (4/α')(1 + 1 - 2) = 0
  -/
  rw [MassShellCondition]
  simp
  ring_nf

/-! 
## Virasoro代数与约束

**Virasoro生成元**：
L_m = (1/2) Σ_{n=-∞}^∞ α_{m-n}·α_n

满足Virasoro代数：
[L_m, L_n] = (m-n)L_{m+n} + (c/12)(m³-m)δ_{m+n,0}

其中c是中心荷，对于自由玻色子c = D（时空维数）。

**物理态条件**：
- L_n|ψ⟩ = 0 对 n > 0（消灭条件）
- (L_0 - 1)|ψ⟩ = 0（质量壳条件）
-/ 

/-- Virasoro代数元素 -/
structure VirasoroElement where
  /-- 下标 m ∈ ℤ -/
  m : ℤ
  /-- 中心荷 c -/
  central_charge : ℝ

/-- Virasoro代数的交换关系

**定理**：[L_m, L_n] = (m-n)L_{m+n} + (c/12)(m³-m)δ_{m+n,0}

这是共形场论的核心代数结构。
中心项(c/12)(m³-m)来源于正规序。
-/ 
theorem virasoro_algebra (m n : ℤ) (c : ℝ) :
    sorry  -- [L_m, L_n] = (m-n)L_{m+n} + (c/12)(m³-m)δ_{m+n,0}
    := by
  /- 【证明框架】
     
     步骤1：定义Virasoro生成元
     L_m = (1/2) Σ_n : α_{m-n}·α_n （正规序）
     
     步骤2：计算对易子
     [L_m, L_n] = (1/4) Σ_{k,l} [α_{m-k}·α_k, α_{n-l}·α_l]
     
     步骤3：利用振荡子代数
     [α_m^μ, α_n^ν] = m δ_{m+n,0} η^{μν}
     
     步骤4：收集各项
     - (m-n)L_{m+n} 来自非中心项
     - (c/12)(m³-m)δ_{m+n,0} 来自正规序
     
     注：c = D（时空维数）对于d个自由标量场
  -/
  sorry

/-- 物理态的Virasoro约束条件 -/
structure PhysicalState where
  /-- 态向量 |ψ⟩ -/
  state : sorry  -- 希尔伯特空间元素
  /-- Virasoro消灭条件：L_n|ψ⟩ = 0 对 n > 0 -/
  h_annihilation : ∀ n > 0, sorry  -- L_n • state = 0
  /-- 质量壳条件：(L_0 - 1)|ψ⟩ = 0 -/
  h_mass_shell : sorry  -- (L_0 - 1) • state = 0

/-! 
## 紧化与额外维度

弦理论需要26维（玻色弦）或10维（超弦）。
这与我们的4维经验不符，因此需要紧化。

**Kaluza-Klein紧化**：
将额外的D-4维紧致化为一个小流形（通常是Calabi-Yau）。

**T-对偶性**：
紧致化在半径R和α'/R的圆上是等价的。
动量模式（Kaluza-Klein）↔ 缠绕模式（拓扑）。

**镜像对称性**：
两个不同的Calabi-Yau流形可以给出等价的物理理论。
导致H^{p,q}(X) = H^{3-p,q}(X^∨)。
-/ 

/-- Calabi-Yau n-流形

定义：n维复Kähler流形，满足：
1. Ricci平坦Kähler度量
2. 第一陈类 c₁ = 0
3. 典范丛平凡

由Yau定理，这些条件等价。
-/ 
structure CalabiYau (n : ℕ) where
  /-- n维复流形 -/
  manifold : Type*
  /-- 拓扑结构 -/
  [topo : TopologicalSpace manifold]
  /-- 复结构 -/
  complex_structure : sorry
  /-- Kähler形式 -/
  kahler_form : sorry
  /-- Ricci平坦条件 -/
  h_ricci_flat : sorry
  /-- 第一陈类为零 -/
  h_c1_zero : sorry

/-- 紧化后的低能有效理论：4维超引力 -/
def EffectiveTheory4D (CY : CalabiYau 3) : sorry :=
  -- 从10维超弦紧化到4维
  sorry

/-- T-对偶性定理

**定理**：紧致化在半径R和α'/R的圆上，弦理论等价。

**物理解释**：
- 动量模式（Kaluza-Klein）：p = m/R
- 缠绕模式：w = nR/α'
- 对偶交换m ↔ n 和 R ↔ α'/R
-/ 
theorem T_duality (R : ℝ) (αp : ReggeSlope) (hR : R > 0) :
    sorry  -- 紧致化在半径R和α'/R的理论等价
    := by
  /- 【证明框架】
     
     步骤1：考虑圆紧致化 S¹(R)
     - 坐标X ~ X + 2πR
     
     步骤2：模式展开
     - 动量模式：p = m/R, m ∈ ℤ
     - 缠绕模式：w = nR/α', n ∈ ℤ
     
     步骤3：质量公式
     M² = (m/R)² + (nR/α')² + (激发态贡献)
     
     步骤4：对偶变换
     - 交换m ↔ n
     - 同时 R → α'/R
     - 质量谱不变
     
     步骤5：验证等价性
     - 配分函数Z(R) = Z(α'/R)
     - 所有物理可观测量相同
  -/
  sorry

/-- 镜像对称性定理（弦理论预言）

**定理**：对于镜像对(X, X^∨)，有H^{p,q}(X) ≅ H^{3-p,q}(X^∨)。

这个数学定理已被Givental和Lian-Liu-Yau证明。
-/ 
theorem mirror_symmetry_hodge (X X_check : CalabiYau 3)
    (h_mirror : sorry) :  -- X和X_check构成镜像对
    sorry  -- H^{p,q}(X) ≅ H^{3-p,q}(X^∨) 对所有p,q成立
    := by
  /- 【背景说明】
     
     SYZ猜想（Strominger-Yau-Zaslow，1996）：
     镜像对都存在特殊Lagrangian纤维化，
     镜像是纤维的T-对偶。
     
     这解释了Hodge数的镜像对称：
     - X的复结构 ↔ X^∨的辛结构
     - 导致H^{p,q}(X) = H^{3-p,q}(X^∨)
     
     注意：完整证明需要SYZ猜想或同调镜像对称（Kontsevich）。
  -/
  sorry

/-! 
## 超弦理论

超弦理论在世界面上引入超对称，消除了tachyon不稳定态。

**五种超弦理论**：
1. Type I：N=1超对称，包含开弦和闭弦
2. Type IIA：N=2超对称，非手性
3. Type IIB：N=2超对称，手性
4. Heterotic SO(32)
5. Heterotic E₈ × E₈

**临界维数**：D = 10

**Green-Schwarz机制**：
反常消除要求D=10且规范群为SO(32)或E₈×E₈。
-/ 

/-- 超弦理论的类型 -/
inductive SuperstringTheory
  | TypeI      /-- N=1超对称，开弦+闭弦 -/
  | TypeIIA    /-- N=2超对称，非手性 -/
  | TypeIIB    /-- N=2超对称，手性 -/
  | HeteroticSO32  /-- 杂化弦，规范群SO(32) -/
  | HeteroticE8E8  /-- 杂化弦，规范群E₈×E₈ -/
  deriving Inhabited

/-- 超弦的临界维数定理

**定理**：所有一致的超弦理论都需要10维时空。

**证明要点**：
1. 计算Weyl反常（中心荷）
2. 要求共形对称性无反常
3. 得到D = 10
-/ 
theorem superstring_critical_dimension (theory : SuperstringTheory) :
    sorry  -- 时空维数 = 10
    := by
  /- 【证明框架】
     
     步骤1：共形场论的中心荷
     - 每个自由玻色子贡献 c = 1
     - 每个自由费米子贡献 c = 1/2
     
     步骤2：超弦世界面场
     - X^μ：D个玻色子，贡献 D
     - ψ^μ：D个费米子，贡献 D/2
     - 鬼场：贡献 -26
     - 超鬼场：贡献 +11
     
     步骤3：总中心荷
     c_total = D + D/2 - 26 + 11 = (3D/2) - 15
     
     步骤4：共形不变性要求
     c_total = 0 ⟹ 3D/2 = 15 ⟹ D = 10
     
     这是超弦理论的核心结果。
  -/
  sorry

/-! 
## M-理论与AdS/CFT对应

**M-理论**：11维的超引力理论，统一五种超弦理论。

**AdS/CFT对应（Maldacena，1997）**：
IIB型超弦在AdS₅ × S⁵背景上等价于4维N=4超杨-米尔斯理论。

这是全息原理的具体实现。
-/ 

/-- M-理论：11维超引力 -/
structure MTheory where
  /-- 11维时空流形 -/
  spacetime : Type*
  /-- 度规场 g_{MN} -/
  metric : sorry
  /-- 3-形式场 C_{MNP} -/
  three_form : sorry

/-- D-膜：开弦端点附着的子流形 -/
structure Dbrane (p : ℕ) where
  /-- p+1维世界体 -/
  worldvolume : Type*
  /-- 嵌入映射到10维时空 -/
  embedding : worldvolume → sorry
  /-- 携带的Ramond-Ramond荷 -/
  rr_charge : ℤ

/-- AdS_{n+1}空间：n+1维反de Sitter空间 -/
def AntiDeSitter (n : ℕ) (R : ℝ) : Type _ :=
  -- AdS_{n+1} = SO(n, 2)/SO(n, 1)
  sorry

/-- 共形场论（CFT）-/
def ConformalFieldTheory (n : ℕ) : Type _ :=
  -- n维共形场论
  sorry

/-- AdS/CFT对应定理（Maldacena对偶）

**定理**：AdS₅ × S⁵上的IIB超弦理论 ≅ 4维N=4超杨-米尔斯理论

对应关系：
- 弦耦合 g_s ↔ 规范耦合 g_YM² = 4πg_s
- 弦张力 α' ↔ 't Hooft耦合 λ = g_YM²N_c = R⁴/α'²
-/ 
theorem ads_cft_correspondence :
    sorry  -- AdS₅ × S⁵上的弦理论 ≅ 边界上的CFT₄
    := by
  /- 【背景说明】
     
     AdS/CFT是弦理论最重要的结果之一：
     
     1. 强耦合规范理论的计算
        - 当λ ≫ 1时，CFT侧强耦合
        - 但弦理论侧变为经典超引力（容易计算）
     
     2. 黑洞物理
        - AdS黑洞 ↔ CFT热态
        - Bekenstein-Hawking熵 = 微观态计数
     
     3. 应用
        - 夸克-胶子等离子体（RHIC实验）
        - 凝聚态系统（全息超导体）
        - 量子信息（ER=EPR猜想）
     
     注：完整证明仍是开放问题。
  -/
  sorry

/-! 
## 弦理论与数学的联系

弦理论对数学产生了深远影响：

1. **镜像对称**：Calabi-Yau流形的辛几何与复几何对应
2. **Gromov-Witten理论**：计数曲线的不变量
3. **Donaldson-Thomas理论**：计数稳定凝聚态
4. **几何Langlands纲领**：规范理论与表示论

这些联系仍在不断发展中。
-/ 

/-- Donaldson-Thomas不变量：计数Calabi-Yau上的稳定凝聚态 -/
def DonaldsonThomasInvariant (X : CalabiYau 3) : ℤ :=
  -- 由Pandharipande-Thomas等人发展
  sorry

/-- 几何Langlands对应 -/
theorem geometric_langlands_from_string :
    sorry  -- G-丛的模空间 ↔ G^L-局部系统的模空间
    := by
  /- 【背景】
     
     几何Langlands对应与4维超杨-米尔斯理论的
     S-对偶密切相关（Kapustin-Witten，2006）。
     
     这是弦理论、量子场论与表示论的深刻联系。
  -/
  sorry

/-! 
## 总结

弦理论的主要成就：
1. 预言了引力的量子理论
2. 统一了所有基本相互作用
3. 预言了额外维度
4. 与深刻的数学结构相联系

开放问题：
- 实验验证（目前能量远超现有加速器）
- 真空选择问题（10^{500}种可能）
- 非微扰定义的严格构造

尽管如此，弦理论已经深刻改变了我们对物理和数学的理解。
-/ 

end StringTheory
