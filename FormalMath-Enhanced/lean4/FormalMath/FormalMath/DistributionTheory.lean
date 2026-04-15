/-
# 分布理论（广义函数）Distribution Theory

## 数学背景

分布理论由Laurent Schwartz于1945年创立，
为偏微分方程和调和分析提供了强有力的框架。

分布是测试函数空间上的连续线性泛函。
它允许我们对不可微的函数进行"微分"，
甚至包括如Dirac δ函数这样的广义对象。

## 核心概念
- **测试函数空间D(Ω)** = C_c^∞(Ω)
- **分布空间D'(Ω)**：测试函数空间的对偶
- **分布的导数**：通过分部积分定义
- **分布的支集**：广义支集概念
- **缓增分布S'(ℝⁿ)**：Fourier变换的自然定义域

## 历史意义
- 统一了微分算子和积分算子
- 为PDE提供了弱解框架
- 物理中的"点粒子"、"点电荷"获得数学严格性

## 参考
- Schwartz, L. "Théorie des distributions" (1950-51)
- Hörmander, L. "The Analysis of Linear Partial Differential Operators I"
- Rudin, W. "Functional Analysis"

## 应用
- 偏微分方程（弱解理论）
- 调和分析和Fourier分析
- 数学物理（量子场论、信号处理）
- 概率论（随机过程）
-/

import FormalMath.MathlibStub.Analysis.InnerProductSpace.PiL2
import FormalMath.MathlibStub.MeasureTheory.Function.LpSpace
import FormalMath.MathlibStub.Topology.Algebra.ContinuousMonoidHom
import FormalMath.MathlibStub.Analysis.Calculus.ContDiff.Basic

namespace DistributionTheory

open MeasureTheory Topology

variable {n : ℕ} {Ω : Set (Fin n → ℝ)} [IsOpen Ω]

/-
## 测试函数空间D(Ω)

测试函数空间由具有紧支集的光滑函数组成。

### 拓扑结构
D(Ω)配备归纳极限拓扑：
- 对每个紧集K ⊂ Ω，D_K = {φ ∈ C_c^∞(Ω) : supp(φ) ⊂ K}
- D(Ω) = ∪_K D_K
- 收敛：φ_j → 0意味着存在公共紧支集，且所有导数一致收敛到0

### 性质
- 完备的局部凸拓扑向量空间
- 不可度量（除非Ω紧）
- Montel空间（有界集相对紧）
-/ 
structure TestFunction (Ω : Set (Fin n → ℝ)) : Type where
  toFun : (Fin n → ℝ) → ℝ
  smooth : ContDiff ℝ ⊤ toFun
  hasCompactSupport : HasCompactSupport toFun
  supportInΩ : support toFun ⊆ Ω

def D (Ω : Set (Fin n → ℝ)) : Type := TestFunction Ω

/-- 测试函数的加法 -/
instance : Add (D Ω) where
  add φ ψ := {
    toFun := φ.toFun + ψ.toFun
    smooth := ContDiff.add φ.smooth ψ.smooth
    hasCompactSupport := by
      -- 支集的和仍是紧的
      -- supp(φ + ψ) ⊆ supp(φ) ∪ supp(ψ)
      have h_sub : support (φ.toFun + ψ.toFun) ⊆ 
        support φ.toFun ∪ support ψ.toFun := 
        support_add_subset φ.toFun ψ.toFun
      apply IsCompact.of_isClosed_subset 
        (IsCompact.union φ.hasCompactSupport ψ.hasCompactSupport)
      · -- 闭集
        apply isClosed_support
      · -- 包含关系
        exact h_sub
    supportInΩ := by
      -- 支集包含关系
      have h_sub : support (φ.toFun + ψ.toFun) ⊆ 
        support φ.toFun ∪ support ψ.toFun := 
        support_add_subset φ.toFun ψ.toFun
      apply h_sub.trans
      apply union_subset φ.supportInΩ ψ.supportInΩ
  }

/-- 测试函数的数乘 -/
instance : SMul ℝ (D Ω) where
  smul c φ := {
    toFun := c • φ.toFun
    smooth := ContDiff.smul (by exact contDiff_const) φ.smooth
    hasCompactSupport := by
      -- 数乘不改变支集
      -- supp(cφ) = supp(φ)（若c ≠ 0）
      by_cases hc : c = 0
      · -- c = 0时，cφ = 0，支集为空
        simp [hc]
        exact isCompact_empty
      · -- c ≠ 0时
        have h_eq : support (c • φ.toFun) = support φ.toFun := 
          support_smul_eq hc φ.toFun
        rw [h_eq]
        exact φ.hasCompactSupport
    supportInΩ := by
      by_cases hc : c = 0
      · -- c = 0
        simp [hc]
        apply empty_subset
      · -- c ≠ 0
        have h_eq : support (c • φ.toFun) = support φ.toFun := 
          support_smul_eq hc φ.toFun
        rw [h_eq]
        exact φ.supportInΩ
  }

/-- 测试函数空间是加法群 -/
instance : AddCommGroup (D Ω) where
  add_assoc φ ψ χ := by
    simp [HAdd.hAdd, Add.add]
  zero := {
    toFun := 0
    smooth := contDiff_const
    hasCompactSupport := by simp [HasCompactSupport]
    supportInΩ := by simp
  }
  zero_add φ := by simp [HAdd.hAdd, Add.add]
  add_zero φ := by simp [HAdd.hAdd, Add.add]
  neg φ := {
    toFun := -φ.toFun
    smooth := ContDiff.neg φ.smooth
    hasCompactSupport := by
      simp [HasCompactSupport]
      exact φ.hasCompactSupport
    supportInΩ := by
      simp [support_neg]
      exact φ.supportInΩ
  }
  add_comm φ ψ := by simp [HAdd.hAdd, Add.add, add_comm]

/-- 测试函数空间的拓扑 -/
instance : TopologicalSpace (D Ω) := 
  -- 紧开拓扑的变体
  TopologicalSpace.induced TestFunction.toFun 
    (UniformSpace.toTopologicalSpace ((Fin n → ℝ) →ᵤ ℝ))

/-
## 分布空间D'(Ω)

分布是测试函数空间上的连续线性泛函：
T : D(Ω) → ℝ

### 连续性
T是连续的，如果φ_j → 0在D(Ω)中 ⟹ T(φ_j) → 0。

### 例子
1. 局部可积函数：T_f(φ) = ∫ fφ
2. Dirac δ：δ_a(φ) = φ(a)
3. 主值：P.V.(1/x)
-/
def Distribution (Ω : Set (Fin n → ℝ)) : Type _ :=
  {T : D Ω → ℝ // Continuous T ∧ ∀ (c : ℝ) (φ ψ : D Ω), 
    T (c • φ) = c * T φ ∧ T (φ + ψ) = T φ + T ψ}

def D_prime (Ω : Set (Fin n → ℝ)) : Type := Distribution Ω

notation:max "D'(" Ω ")" => D_prime Ω

/-- 分布的加法 -/
instance : Add (D' Ω) where
  add T S := ⟨fun φ ↦ T.1 φ + S.1 φ, by 
    constructor
    · -- 连续性：连续函数的和连续
      apply Continuous.add
      · exact T.2.1
      · exact S.2.1
    · -- 线性性验证
      intro c φ ψ
      constructor
      · -- 齐次性
        simp [HSMul.hSMul, SMul.smul]
        rw [T.2.2 c φ ψ |>.1, S.2.2 c φ ψ |>.1]
        ring
      · -- 可加性
        simp [HAdd.hAdd, Add.add]
        rw [T.2.2 c φ ψ |>.2, S.2.2 c φ ψ |>.2]
        ring
  ⟩

/-- 分布的数乘 -/
instance : SMul ℝ (D' Ω) where
  smul c T := ⟨fun φ ↦ c * T.1 φ, by
    constructor
    · -- 连续性
      apply Continuous.mul
      · exact continuous_const
      · exact T.2.1
    · -- 线性性
      intro d φ ψ
      constructor
      · -- 齐次性
        simp [HSMul.hSMul, SMul.smul]
        rw [T.2.2 d φ ψ |>.1]
        ring
      · -- 可加性
        simp [HAdd.hAdd, Add.add]
        rw [T.2.2 d φ ψ |>.2]
        ring
  ⟩

/-- 分布空间是向量空间 -/
instance : AddCommGroup (D' Ω) where
  add_assoc T S R := by simp [HAdd.hAdd, Add.add, add_assoc]
  zero := ⟨0, continuous_const, by simp⟩
  zero_add T := by simp [HAdd.hAdd, Add.add]
  add_zero T := by simp [HAdd.hAdd, Add.add]
  neg T := ⟨fun φ ↦ -T.1 φ, by
    constructor
    · apply Continuous.neg; exact T.2.1
    · intro c φ ψ
      constructor
      · simp [T.2.2 c φ ψ |>.1]
      · simp [T.2.2 c φ ψ |>.2]
  ⟩
  add_comm T S := by simp [HAdd.hAdd, Add.add, add_comm]

/-
## 局部可积函数诱导的分布

任何f ∈ L^1_loc(Ω)定义一个分布：
T_f(φ) = ∫_Ω f(x)φ(x) dx

这是分布理论的基础：
局部可积函数可以等同于一个分布。
-/
def distributionOfLocallyIntegrable (f : (Fin n → ℝ) → ℝ)
    (hf : ∀ (K : Set (Fin n → ℝ)), K ⊆ Ω → IsCompact K → 
      IntegrableOn f K volume) : D' Ω :=
  ⟨fun φ ↦ ∫ x in Ω, f x * φ.toFun x, 
   by 
    -- 连续性证明
    -- 利用积分的估计和测试函数拓扑
    sorry,
   by 
    -- 线性性证明
    intro c φ ψ
    constructor
    · -- 齐次性
      simp [HSMul.hSMul, SMul.smul]
      rw [← integral_mul_left]
      congr
      funext
      ring
    · -- 可加性
      simp [HAdd.hAdd, Add.add]
      rw [← integral_add]
      · congr; funext; ring
      · sorry -- 可积性
      · sorry -- 可积性
  ⟩

/-- L^p函数诱导分布 -/
def distributionOfLp {p : ℝ≥0∞} (hp : 1 ≤ p) 
    (f : Lp (fun _ : Fin n → ℝ ↦ ℝ) p (volume.restrict Ω)) : D' Ω :=
  distributionOfLocallyIntegrable f (by
    intro K hK hK_compact
    -- L^p函数在紧集上局部可积
    sorry
  )

/-
## Dirac δ分布

最著名的分布例子：
δ_a(φ) = φ(a)

### 性质
- 不是任何局部可积函数诱导的
- δ的"导数"是负的δ'，其中δ'(φ) = -φ'(a)
- 在Fourier分析中：δ̂ = 1（常函数1）
-/
def DiracDelta (a : Fin n → ℝ) (ha : a ∈ Ω) : D' Ω :=
  ⟨fun φ ↦ φ.toFun a, 
   by 
    -- 连续性：在紧开拓扑下，求值是连续的
    apply continuous_iff_continuousAt.mpr
    intro φ
    -- 利用测试函数的光滑性
    sorry,
   by 
    -- 线性性
    intro c φ ψ
    constructor
    · -- 齐次性
      simp [HSMul.hSMul, SMul.smul]
    · -- 可加性
      simp [HAdd.hAdd, Add.add]
  ⟩

notation:max "δ_" a => DiracDelta a

/-- δ分布的筛选性质 -/
theorem dirac_delta_sifting (a : Fin n → ℝ) (ha : a ∈ Ω) 
    (f : (Fin n → ℝ) → ℝ) (hf : Continuous f) (hsupp : HasCompactSupport f) :
    distributionOfLocallyIntegrable f sorry (δ_a ha) = f a := by
  -- 这不是严格的数学陈述，而是启发性的
  -- 严格地说，δ作用于测试函数
  sorry

/-
## 分布的导数

对于分布T，其α阶导数定义为：
∂^α T(φ) = (-1)^{|α|} T(∂^α φ)

### 动机
这与分部积分一致：
若T = T_f且f光滑，则：
∫ f' φ = -∫ f φ'
即 T_f'(φ) = -T_f(φ')

### 重要性
所有分布都是无限可微的！
这是分布理论最强大的特征之一。
-/ 
structure Multiindex (n : ℕ) : Type :=
  indices : Fin n → ℕ

def Multiindex.order (α : Multiindex n) : ℕ := 
  ∑ i, α.indices i

def distribution_derivative (T : D' Ω) (α : Multiindex n) : D' Ω :=
  ⟨fun φ ↦ (-1 : ℝ) ^ α.order * T.1 {
    toFun := iteratedDeriv α.indices φ.toFun
    smooth := ContDiff.iteratedDeriv α.order φ.smooth
    hasCompactSupport := by
      -- 导数不扩大支集
      apply HasCompactSupport.iteratedDeriv
      exact φ.hasCompactSupport
    supportInΩ := by
      -- 导数不扩大支集
      apply subset_trans _ φ.supportInΩ
      apply support_iteratedDeriv_subset
  }, by 
    -- 连续性
    apply Continuous.mul
    · exact continuous_const
    · -- T的连续性与测试函数求导的连续性
      sorry,
   by 
    -- 线性性
    intro c φ ψ
    constructor
    · -- 齐次性
      simp [HSMul.hSMul, SMul.smul, HAdd.hAdd, Add.add]
      rw [T.2.2 c _ _ |>.1]
      ring
    · -- 可加性
      simp [HSMul.hSMul, SMul.smul, HAdd.hAdd, Add.add]
      rw [T.2.2 c _ _ |>.2]
      ring
  ⟩

notation:max "∂^" α T => distribution_derivative T α

/-- 分布导数是导数的推广 -/
theorem distribution_derivative_agrees {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ ⊤ f) (hsupp : HasCompactSupport f)
    (hΩ' : support f ⊆ Ω) (α : Multiindex n) :
    ∂^α (distributionOfLocallyIntegrable f sorry) = 
    distributionOfLocallyifferentiable (iteratedDeriv α.indices f) sorry := by
  -- 对于光滑函数，分布导数与经典导数一致
  sorry

/-
## Heaviside函数的导数是Dirac δ

H(x) = 1_{x>0}的分布导数是δ_0

这是分布理论的经典例子，展示了如何处理不连续函数的"导数"。

### 验证
对于测试函数φ：
H'(φ) = -H(φ') = -∫_0^∞ φ'(x) dx = φ(0) = δ_0(φ)
-/
theorem heaviside_derivative (n : ℕ) (hn : n = 1) (h0 : (fun _ : Fin 1 ↦ (0 : ℝ)) ∈ Ω) :
    let H : D' Ω := distributionOfLocallyIntegrable 
      (fun x ↦ if x 0 > 0 then (1 : ℝ) else 0) 
      (by 
        -- 证明Heaviside函数局部可积
        sorry
      )
    let α : Multiindex 1 := ⟨fun i ↦ if i = 0 then 1 else 0⟩
    ∂^α H = δ_(fun _ ↦ 0) h0 := by
  -- 通过分部积分证明
  intro H α
  apply Subtype.ext
  funext φ
  -- H'(φ) = -H(φ') = -∫_0^∞ φ'(x) dx
  have h1 : (∂^α H).1 φ = (-1) ^ α.order * H.1 {
    toFun := iteratedDeriv α.indices φ.toFun
    smooth := sorry
    hasCompactSupport := sorry
    supportInΩ := sorry
  } := rfl
  
  -- 计算
  simp [h1, H, α]
  -- -∫_0^∞ φ'(x) dx = φ(0)
  sorry -- 微积分基本定理

/-
## 分布的支集

分布T的支集是最小的闭集F，使得
对于支集与F不相交的测试函数φ，有T(φ) = 0。

### 形式定义
supp(T) = ⋂{F闭集 | ∀φ, supp(φ)∩F=∅ ⟹ T(φ)=0}

### 性质
- 若T = T_f，则supp(T) = ess supp(f)
- δ_a的支集是{a}
- 支集可以任意"差"（如支集为单点但非δ的分布）
-/
def support_distribution (T : D' Ω) : Set (Fin n → ℝ) :=
  ⋂₀ {F : Set (Fin n → ℝ) | IsClosed F ∧ 
    ∀ φ : D Ω, Disjoint (support φ.toFun) F → T.1 φ = 0}

/-- 支集是闭集 -/
theorem support_distribution_closed (T : D' Ω) : 
    IsClosed (support_distribution T) := by
  -- 闭集的任意交是闭的
  apply isClosed_sInter
  intro F hF
  exact hF.1

/-- 局部可积函数的支集 -/
theorem support_locally_integrable {f : (Fin n → ℝ) → ℝ}
    (hf : ∀ (K : Set (Fin n → ℝ)), K ⊆ Ω → IsCompact K → 
      IntegrableOn f K volume) :
    support_distribution (distributionOfLocallyIntegrable f hf) = 
    essentialSupport f := by
  -- 本质是f的支集
  sorry

/-
## 具有紧支集的分布ε'(Ω)

这些是支集为紧集的分布，形成测试函数空间的对偶。

### 性质
1. ε'(Ω)可以等同于D(Ω)上的连续线性泛函
2. 与D'(Ω)不同，ε'(Ω)上的拓扑更简单（Banach空间结构）
3. 紧支集分布可以卷积任意分布
-/
def CompactlySupportedDistribution (Ω : Set (Fin n → ℝ)) : Type _ :=
  {T : D' Ω // IsCompact (support_distribution T)}

def E_prime (Ω : Set (Fin n → ℝ)) : Type := 
  CompactlySupportedDistribution Ω

/-
## 分布与光滑函数的卷积

对于f ∈ C^∞(ℝⁿ), T ∈ D'(ℝⁿ)，卷积定义为：
(f * T)(φ) = T(f̃ * φ)

其中f̃(x) = f(-x)。

### 性质
1. f * T是光滑函数
2. ∂^α(f * T) = (∂^αf) * T = f * (∂^αT)
3. 卷积与平移交换
-/
def distribution_convolution (f : (Fin n → ℝ) → ℝ) 
    (hf : ContDiff ℝ ⊤ f) (T : D' (Set.univ : Set (Fin n → ℝ))) : 
    D' (Set.univ : Set (Fin n → ℝ)) :=
  ⟨fun φ ↦ T.1 {
    toFun := fun x ↦ ∫ y, f y * φ.toFun (x - y)
    smooth := sorry -- 卷积的光滑性
    hasCompactSupport := sorry -- 紧支集的保持
    supportInΩ := by simp [Set.univ]
  }, sorry, sorry⟩

/-- 卷积的光滑性 -/
theorem convolution_smooth (f : (Fin n → ℝ) → ℝ) 
    (hf : ContDiff ℝ ⊤ f) (T : D' (Set.univ : Set (Fin n → ℝ))) :
    ∃ g : (Fin n → ℝ) → ℝ, ContDiff ℝ ⊤ g ∧ 
    distribution_convolution f hf T = distributionOfLocallyIntegrable g sorry := by
  -- 光滑函数与分布的卷积是光滑的
  sorry

/-
## 缓增分布S'(ℝⁿ)

缓增分布是速降函数空间S(ℝⁿ)上的连续线性泛函。
这是Fourier变换的自然定义域。

### 速降函数
f ∈ S(ℝⁿ)如果：
∀ α, β, ∃ C, |x^β ∂^α f(x)| ≤ C

即f及其所有导数比任何多项式衰减都快。

### 重要性
Fourier变换是S(ℝⁿ)上的拓扑同构，
因此可以扩展到S'(ℝⁿ)。
-/
def SchwartzSpace (n : ℕ) : Type _ :=
  {f : (Fin n → ℝ) → ℝ | ContDiff ℝ ⊤ f ∧ 
    ∀ (α β : Multiindex n), ∃ C, ∀ x, 
      |x^β * iteratedDeriv α.indices f x| ≤ C}

def S (n : ℕ) : Type := SchwartzSpace n

/-- 速降函数空间是Fréchet空间 -/
instance : TopologicalSpace (S n) := sorry
instance : AddCommGroup (S n) := sorry

/- 缓增分布 -/
def TemperedDistribution (n : ℕ) : Type _ :=
  {T : S n → ℝ // Continuous T ∧ ∀ (c : ℝ) (φ ψ : S n), 
    T (c • φ) = c * T φ ∧ T (φ + ψ) = T φ + T ψ}

def S_prime (n : ℕ) : Type := TemperedDistribution n

notation:max "S'(" n ")" => S_prime n

/-
## 缓增分布的Fourier变换

F{T}(φ) = T(F̂φ)

其中F̂是速降函数的Fourier变换：
F̂f(ξ) = ∫ f(x) e^{-2πi x·ξ} dx

### 关键性质
1. F: S'(ℝⁿ) → S'(ℝⁿ)是拓扑同构
2. F(∂^α T) = (2πiξ)^α F(T)
3. F(x^α T) = (-1)^{|α|}/(2πi)^{|α|} ∂^α F(T)
-/
def fourier_transform_tempered (T : S' n) : S' n :=
  ⟨fun φ ↦ T.1 (fourier_schwartz φ), 
   sorry, -- 连续性
   sorry  -- 线性性
  ⟩

/-- Fourier变换的逆 -/
theorem fourier_transform_inversion (T : S' n) :
    fourier_transform_tempered (fourier_transform_tempered T) = 
    (fun φ ↦ T.1 (fun x ↦ φ (-x))) := by
  -- Fourier反演公式
  sorry

/-
## 微分算子的基本解

对于常系数微分算子P(D)，基本解E满足：
P(D)E = δ

这是通过Fourier变换求解PDE的基础。

### 例子
1. Laplace算子：E = c_n/|x|^{n-2}（n ≥ 3）
2. 热算子：E = (4πt)^{-n/2} exp(-|x|²/4t) H(t)
3. 波动算子：E依赖于维数的奇偶性
-/
def FundamentalSolution (P : (Multiindex n → ℝ) → ℝ) 
    (E : S' n) : Prop :=
  ∀ φ : S n, distribution_derivative E (PToMultiindex P) φ = 
    DiracDeltaSchwartz (fun _ ↦ 0) φ

/-- Laplace算子的基本解 -/
theorem laplace_fundamental_solution {n : ℕ} (hn : n ≥ 3) :
    let E : S' n := distributionOfTempered 
      (fun x ↦ if x ≠ 0 then 
        1 / ((n-2) * volumeUnitSphere n * ‖x‖^(n-2)) else 0) 
      sorry
    FundamentalSolution (fun α ↦ if α = LaplacianMultiindex then 1 else 0) E := by
  -- 验证ΔE = δ
  -- 计算Δ(1/|x|^{n-2})在分布意义下
  sorry

/-
## 分布的收敛

分布序列T_n → T意味着：
对于所有测试函数φ，有T_n(φ) → T(φ)。

这是弱*拓扑中的收敛。

### 性质
1. 分布空间在弱*拓扑下完备
2. 若T_n → T，则∂^α T_n → ∂^α T
3. 若f_n → f在L^1_loc中，则T_{f_n} → T_f
-/
def DistributionConvergence (T_seq : ℕ → D' Ω) (T : D' Ω) : Prop :=
  ∀ φ : D Ω, Filter.Tendsto (fun n ↦ T_seq n φ) Filter.atTop 
    (nhds (T φ))

/-- 分布收敛的线性性 -/
theorem distribution_convergence_linear (T_seq S_seq : ℕ → D' Ω) 
    (T S : D' Ω) (hT : DistributionConvergence T_seq T)
    (hS : DistributionConvergence S_seq S) (c : ℝ) :
    DistributionConvergence (fun n ↦ T_seq n + c • S_seq n) 
      (T + c • S) := by
  intro φ
  -- 点态收敛保持线性运算
  simpa using Tendsto.add (hT φ) (Tendsto.const_mul c (hS φ))

/-
## 分布的极限唯一性

**定理**：若T_n → T且T_n → S，则T = S。

这是Hausdorff性质的结果，
也是分布空间完备性的基础。
-/
theorem distribution_limit_unique 
    (T_seq : ℕ → D' Ω) (T S : D' Ω)
    (hT : DistributionConvergence T_seq T)
    (hS : DistributionConvergence T_seq S) : T = S := by
  -- 利用测试函数空间的分离性
  apply Subtype.ext
  funext φ
  -- 对每个φ，T_seq n φ收敛到唯一极限
  have h_limT : Tendsto (fun n ↦ T_seq n φ) atTop (𝓝 (T φ)) := hT φ
  have h_limS : Tendsto (fun n ↦ T_seq n φ) atTop (𝓝 (S φ)) := hS φ
  -- 极限唯一
  exact tendsto_nhds_unique h_limT h_limS

/- 辅助定义 -/
def support_add_subset {α : Type*} [TopologicalSpace α] 
    (f g : α → ℝ) : support (f + g) ⊆ support f ∪ support g := sorry

def support_smul_eq {α : Type*} [TopologicalSpace α] {c : ℝ} 
    (hc : c ≠ 0) (f : α → ℝ) : support (c • f) = support f := sorry

def support_neg {α : Type*} [TopologicalSpace α] 
    (f : α → ℝ) : support (-f) = support f := sorry

def isClosed_support {α : Type*} [TopologicalSpace α] 
    {f : α → ℝ} (hf : Continuous f) : IsClosed (support f) := sorry

def HasCompactSupport.iteratedDeriv {α : Type*} [TopologicalSpace α] 
    {f : α → ℝ} {n : ℕ} (hf : HasCompactSupport f) :
    HasCompactSupport (iteratedDeriv n f) := sorry

def support_iteratedDeriv_subset {α : Type*} [TopologicalSpace α] 
    {f : α → ℝ} {n : ℕ} : 
    support (iteratedDeriv n f) ⊆ support f := sorry

def ContDiff.iteratedDeriv {n : ℕ} {f : (Fin n → ℝ) → ℝ} 
    (k : ℕ) (hf : ContDiff ℝ ⊤ f) : 
    ContDiff ℝ ⊤ (iteratedDeriv k f) := sorry

def iteratedDeriv (n : ℕ) {α : Type*} [NormedAddCommGroup α] 
    [NormedSpace ℝ α] (f : α → ℝ) : α → ℝ := sorry

def essentialSupport {f : (Fin n → ℝ) → ℝ} : Set (Fin n → ℝ) := sorry

def fourier_schwartz {n : ℕ} (f : S n) : S n := sorry

def distributionOfTempered {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hf : ∀ (α β : Multiindex n), ∃ C, ∀ x, 
      |x^β * iteratedDeriv α.indices f x| ≤ C) : S' n := sorry

def PToMultiindex {n : ℕ} (P : (Multiindex n → ℝ) → ℝ) : Multiindex n := sorry

def DiracDeltaSchwartz {n : ℕ} (a : Fin n → ℝ) : S' n := sorry

def LaplacianMultiindex {n : ℕ} : Multiindex n := sorry

def volumeUnitSphere (n : ℕ) : ℝ := sorry

def x^β {n : ℕ} (x : Fin n → ℝ) (β : Multiindex n) : ℝ := 
  ∏ i, x i ^ β.indices i

end DistributionTheory
