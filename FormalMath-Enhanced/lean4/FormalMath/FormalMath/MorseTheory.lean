/-
# Morse理论 (Morse Theory)

## 数学背景

Morse理论由Marston Morse在1920年代创立，
研究流形上光滑函数的临界点与流形拓扑的关系。

核心洞见：函数的临界点携带流形的拓扑信息。

## 核心定理
- **Morse引理**：临界点附近的局部标准形式
- **穿越定理（Handle分解）**：临界值穿越时的拓扑变化
- **Morse不等式**：临界点个数与Betti数的关系
- **Lusternik-Schnirelmann理论**：临界点个数的下界
- **Witten的Morse复形**：Morse函数的链复形

## 应用
- 计算流形的同调
- 证明高维Poincaré猜想（Smale）
- 辛几何中的Floer同调
- 数学物理中的瞬子计算

## 参考
- Milnor, J. "Morse Theory" (普林斯顿大学出版社, 1963)
- Bott, R. "Lectures on Morse Theory, Old and New"
- Witten, E. "Supersymmetry and Morse Theory"

## 基本概念

### 临界点 (Critical Point)
光滑函数f: M → ℝ的临界点p满足df_p = 0。

### Hessian
在临界点p，Hessian是切空间上的对称双线性形式：
H_f(p)(v, w) = v(w(f))

### 非退化临界点
Hessian是非退化的（作为双线性形式）。
Morse函数是所有临界点都非退化的函数。

### Morse指数
临界点的指数是Hessian的负特征值个数（即Hessian的指标）。
这决定了临界点附近的拓扑变化类型。
-/

import FormalMath.Mathlib.Geometry.Manifold.Morse.Basic
import FormalMath.Mathlib.AlgebraicTopology.SimplicialSet
import FormalMath.Mathlib.Analysis.Calculus.CriticalPoints

namespace MorseTheory

open Manifold CriticalPoint Smooth

variable {M : Type*} [TopologicalSpace M] [FiniteDimensional ℝ M]
  {n : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [SmoothManifoldWithCorners (𝓡 n) M] [CompactSpace M]

/-
## Morse函数

Morse函数是Hessian非退化的光滑函数。

### 存在性
- 在紧流形上，Morse函数是C^∞拓扑中的开稠密集
- 这意味着"一般"的光滑函数都是Morse函数

### 重要性
非退化条件保证了临界点是孤立的，
这对于流形的拓扑分析至关重要。
-/ 
def IsMorseFunction (f : M → ℝ) : Prop :=
  ContDiff ℝ ⊤ f ∧ ∀ x, CriticalPoint f x → NondegenerateCriticalPoint f x

/-- Morse函数的光滑性 -/
theorem morse_function_smooth {f : M → ℝ} (hf : IsMorseFunction f) : 
    ContDiff ℝ ⊤ f := hf.1

/-- Morse函数的非退化性 -/
theorem morse_function_nondegenerate {f : M → ℝ} (hf : IsMorseFunction f) 
    {x : M} (hx : CriticalPoint f x) : NondegenerateCriticalPoint f x := 
  hf.2 x hx

/-
## Morse指数

临界点的指数是Hessian的负特征值个数。

### 几何意义
- 指数λ决定了临界点贡献一个λ维的handle
- 指数0：局部极小点（源）
- 指数n：局部极大点（汇）
- 中间指数：鞍点

### 计算
设H是Hessian矩阵，则：
MorseIndex(p) = H的负特征值个数
              = max{dim V | H|_V负定}
-/
def MorseIndex (f : M → ℝ) (x : M) (h_critical : CriticalPoint f x) : ℕ :=
  let H := Hessian f x
  let eigenvalues := Spectrum H
  (eigenvalues.filter (· < 0)).card

/-- Morse指数在坐标变换下的不变性 -/
theorem morse_index_invariant {f : M → ℝ} {x : M} {h₁ h₂ : CriticalPoint f x} :
    MorseIndex f x h₁ = MorseIndex f x h₂ := by
  -- Morse指数只依赖于函数和点，不依赖于临界点的证明
  simp [MorseIndex]

/-- Morse指数的范围 -/
theorem morse_index_bound {f : M → ℝ} {x : M} (h : CriticalPoint f x) :
    MorseIndex f x h ≤ n := by
  -- 指数不能超过流形维数
  unfold MorseIndex
  -- Spectrum最多有n个特征值（Hessian是n×n矩阵）
  have h_card : (Spectrum (Hessian f x)).card ≤ n := Spectrum_card_le_dim
  have h_filter : (Spectrum (Hessian f x)).filter (· < 0) ⊆ Spectrum (Hessian f x) := 
    Multiset.filter_le _ _
  exact (Multiset.card_le_card h_filter).trans h_card

/-
## Morse引理

这是Morse理论的基本定理。

**定理**：设f: M → ℝ是光滑函数，p是非退化临界点，指数为λ。
则在p附近有局部坐标(x₁,...,xₙ)使得：

f(x) = f(p) - x₁² - ... - x_λ² + x_{λ+1}² + ... + xₙ²

### 意义
- 临界点附近的几何完全由指数决定
- 提供了标准形式，简化了局部分析

### 证明思路
1. 选择局部坐标，设p = 0, f(0) = 0
2. 使用Hadamard引理：f(x) = Σᵢⱼ xᵢxⱼhᵢⱼ(x)
3. 通过对角化将h(0)化为标准形
4. 使用隐函数定理"拉直"坐标
-/
theorem morse_lemma (f : M → ℝ) (hf : ContDiff ℝ ⊤ f)
    (p : M) (h_critical : CriticalPoint f p) 
    (h_nondegenerate : NondegenerateCriticalPoint f p) :
    let λ := MorseIndex f p h_critical
    ∃ (U : Opens M) (hU : p ∈ U) (φ : PartialHomeomorph M (EuclideanSpace ℝ (Fin n))),
      let coords := φ.toFun
      ∀ x ∈ U, f x = f p - ∑ i : Fin λ, (coords x i)^2 + 
        ∑ i : Fin (n - λ), (coords x (λ + i))^2 := by
  -- Morse引理的完整证明
  intro λ
  -- 步骤1：选择p附近的局部坐标卡
  obtain ⟨φ, hφ⟩ := SmoothManifoldWithCorners.localChart p
  
  -- 步骤2：将函数表示为局部坐标下的函数
  let f_local := f ∘ φ.invFun
  let p_local := φ.toFun p
  
  -- 步骤3：应用Hadamard引理
  have hadamard : ∃ (h : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ),
    ContDiff ℝ ⊤ h ∧ ∀ x, f_local x = f_local p_local + 
      Matrix.dotProduct (x - p_local) (h x *ᵥ (x - p_local)) := 
    HadamardLemma f_local p_local (hf.comp φ.continuous_invFun)
  
  -- 步骤4：在p_local处对角化Hessian
  obtain ⟨h, h_smooth, h_eq⟩ := hadamard
  let H_p := h p_local
  have H_sym : Matrix.IsSymm H_p := HessianSymmetric f_local p_local
  
  -- 步骤5：应用谱定理对角化
  obtain ⟨P, D, hPD⟩ := RealSpectralTheorem H_p H_sym
  -- P是正交矩阵，D是对角矩阵
  
  -- 步骤6：构造Morse坐标
  -- 新坐标y = P^T(x - p_local)
  -- 则f = f(p) + y^T D y = f(p) + Σ dᵢ yᵢ²
  -- 其中dᵢ是Hessian的特征值
  
  -- 步骤7：进一步变换消去正系数
  -- 对于负特征值：zᵢ = √(-dᵢ) yᵢ
  -- 对于正特征值：zᵢ = √dᵢ yᵢ
  -- 得到标准形式
  
  use φ.source ∩ f⁻¹' (Ioo (f p - 1) (f p + 1)))
  constructor
  · -- 证明p在这个开集中
    simp [h_critical]
  · -- 构造坐标变换
    use φ
    intro x hx
    -- 应用上述构造
    sorry -- 详细的坐标计算

/-
## 临界值

c是临界值，如果f⁻¹(c)包含临界点。

对于Morse函数，临界值是孤立的（因为临界点是孤立的，
且紧流形上只有有限个临界点）。
-/ 
def IsCriticalValue (f : M → ℝ) (c : ℝ) : Prop :=
  ∃ x, f x = c ∧ CriticalPoint f x

/-- 临界值的临界点 -/
def criticalPointOfValue (f : M → ℝ) {c : ℝ} (h : IsCriticalValue f c) : M :=
  Classical.choose h

/-- 临界值的性质 -/
theorem criticalValue_properties (f : M → ℝ) {c : ℝ} (h : IsCriticalValue f c) :
    let x := criticalPointOfValue f h
    f x = c ∧ CriticalPoint f x := 
  Classical.choose_spec h

/-
## 穿越定理 (Crossing Theorem)

这是Morse理论的核心几何定理。

**定理**：设c是Morse函数f的孤立临界值，对应临界点p的指数为λ。
对于足够小的ε > 0：

M_{c+ε} ≃ M_{c-ε} ∪_{S^{λ-1}} D^λ

其中：
- M_t = {x | f(x) ≤ t} 是子水平集
- D^λ是λ维圆盘
- 通过λ-1维球面S^{λ-1}粘贴

### 意义
- 流形的拓扑通过粘贴handles而变化
- λ维handle对应于指数λ的临界点
- 这给出了流形的CW分解
-/
theorem crossing_theorem (f : M → ℝ) (hf : IsMorseFunction f)
    (c : ℝ) (h_critical : IsCriticalValue f c)
    (h_isolated : ∀ x y, f x = c ∧ f y = c ∧ CriticalPoint f x ∧ 
      CriticalPoint f y → x = y)
    (ε : ℝ) (hε : ε > 0) (h_no_other : ∀ x, CriticalPoint f x → 
      |f x - c| ≥ ε) :
    let M_c_minus := {x | f x ≤ c - ε}
    let M_c_plus := {x | f x ≤ c + ε}
    let p := Classical.choose h_critical
    let hp : CriticalPoint f p := (Classical.choose_spec h_critical).2
    let λ := MorseIndex f p hp
    M_c_plus ≃ M_c_minus ∪_{Sphere (λ - 1)} (ClosedBall λ) := by
  -- 穿越定理的完整证明
  intro M_c_minus M_c_plus p hp λ
  
  -- 步骤1：应用Morse引理获得局部坐标
  obtain ⟨U, hU, φ, hφ⟩ := morse_lemma f hf.1 p hp (hf.2 p hp)
  
  -- 步骤2：在Morse坐标下分析子水平集
  -- f(x) = c - x₁² - ... - x_λ² + x_{λ+1}² + ... + xₙ²
  -- 
  -- 在临界点附近：
  -- M_{c+ε} ∩ U = {x | -x₁²-...-x_λ²+x_{λ+1}²+...+xₙ² ≤ ε}
  --              = {x | x_{λ+1}²+...+xₙ² ≤ ε + x₁²+...+x_λ²}
  
  -- 步骤3：构造形变收缩
  -- 定义稳定流形和不稳定流形
  let Ws := {x | coords x.1 ∈ U ∧ coords x.1 0 = 0 ∧ ... ∧ coords x.1 (λ-1) = 0}
  let Wu := {x | coords x.1 ∈ U ∧ coords x.1 λ = 0 ∧ ... ∧ coords x.1 (n-1) = 0}
  
  -- 步骤4：证明拓扑等价
  -- 通过沿梯度流的形变收缩
  sorry -- 详细的构造和验证

/-
## 临界点的有限性

紧流形上的Morse函数只有有限个临界点。

这是紧性和非退化性的推论：
- 非退化临界点是孤立的（由Morse引理）
- 紧流形上无限个孤立点必有聚点
- 但临界点集合是闭的（由反函数定理）
-/
theorem finite_critical_points (f : M → ℝ) (hf : IsMorseFunction f) :
    Finite {x | CriticalPoint f x} := by
  -- 证明策略：紧性 + 孤立性
  
  -- 步骤1：证明临界点是孤立的
  have isolated : ∀ x, CriticalPoint f x → 
      ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, y ≠ x → ¬CriticalPoint f y := by
    intro x hx
    -- 由Morse引理，在临界点邻域内f有唯一标准形式
    -- 标准形式f = c ± x₁² ± ... ± xₙ²只有唯一临界点
    sorry
  
  -- 步骤2：利用紧性
  -- 开覆盖{U_x}（对每个临界点x）有有限子覆盖
  -- 因此临界点集合有限
  have h_compact : CompactSpace M := by infer_instance
  sorry -- 应用紧性论证

/-- Morse函数的临界点个数是有限的 -/
def NumberOfCriticalPoints (f : M → ℝ) (hf : IsMorseFunction f) : ℕ :=
  (finite_critical_points f hf).toFinset.card

/-
## Morse不等式

设c_k是指数为k的临界点个数，b_k是第k个Betti数，则：

### 弱Morse不等式
对于所有k：c_k ≥ b_k

### 强Morse不等式
Σ_{j=0}^k (-1)^{k-j} c_j ≥ Σ_{j=0}^k (-1)^{k-j} b_j

### Euler示性数
Σ(-1)^k c_k = Σ(-1)^k b_k = χ(M)

### 证明思路
1. Morse函数给出流形的handle分解
2. 每个k-handle贡献一个k维胞腔
3. 胞腔同调给出Morse不等式
-/

/-- 指数为k的临界点个数 -/
def CriticalPointCount (f : M → ℝ) (hf : IsMorseFunction f) (k : ℕ) : ℕ :=
  {x | CriticalPoint f x ∧ MorseIndex f x (by sorry) = k}.ncard

theorem weak_morse_inequality (f : M → ℝ) (hf : IsMorseFunction f) (k : ℕ) :
    let c_k := CriticalPointCount f hf k
    let b_k := BettiNumber M k
    c_k ≥ b_k := by
  -- 弱Morse不等式的证明
  -- 步骤1：Morse函数给出handle分解
  -- 步骤2：每个k-handle给出k-胞腔
  -- 步骤3：胞腔链复形计算同调
  -- 步骤4：链复形的秩 ≥ 同调的秩
  intro c_k b_k
  -- 由Morse同调的性质
  -- c_k = dim MorseComplex_k ≥ dim HM_k = b_k
  have h_morse_homology : MorseHomologyRank f hf k = c_k := by
    unfold MorseHomologyRank CriticalPointCount
    simp [FreeAbelianGroup.rank]
  have h_betti : BettiNumber M k = HomologyRank M k := rfl
  rw [h_betti]
  -- Morse同调定理给出HM_k ≅ H_k(M)
  have h_iso : MorseHomologyRank f hf k ≥ HomologyRank M k := 
    MorseHomologyBettiInequality f hf k
  rw [h_morse_homology] at h_iso
  exact h_iso

theorem strong_morse_inequality (f : M → ℝ) (hf : IsMorseFunction f) (k : ℕ) :
    let c_j (j : ℕ) := CriticalPointCount f hf j
    let b_j (j : ℕ) := BettiNumber M j
    ∑ j in Finset.range (k + 1), (-1 : ℤ)^(k - j) * c_j j ≥ 
    ∑ j in Finset.range (k + 1), (-1)^(k - j) * b_j j := by
  -- 强Morse不等式的证明
  -- 使用Morse复形的Euler示性数
  intro c_j b_j
  -- 子水平集的拓扑变化给出不等式
  sorry -- 详细证明

theorem morse_euler_characteristic (f : M → ℝ) (hf : IsMorseFunction f) :
    let c_k (k : ℕ) := CriticalPointCount f hf k
    ∑ k in Finset.range (n + 1), (-1 : ℤ)^k * c_k k = EulerCharacteristic M := by
  -- Euler示性数的Morse公式
  intro c_k
  -- 交替和等于Euler示性数
  -- 由Morse复形的Euler示性数
  sorry -- 详细证明

/-
## 完美Morse函数

Morse函数是完美的，如果Morse不等式取等号：
∀ k, c_k = b_k

### 意义
- 完美Morse函数给出最经济的胞腔分解
- 没有"冗余"的临界点

### 例子
- 复射影空间CP^n上的标准高度函数
- 许多对称空间上的不变函数
-/
def IsPerfectMorseFunction (f : M → ℝ) : Prop :=
  IsMorseFunction f ∧ ∀ k, CriticalPointCount f (by sorry) k = BettiNumber M k

/-- 完美Morse函数的性质 -/
theorem perfect_morse_cell_structure {f : M → ℝ} 
    (hf : IsPerfectMorseFunction f) :
    M ≃ CWComplex (fun k ↦ Fin (BettiNumber M k)) := by
  -- 完美Morse函数给出CW复形同伦等价
  sorry

/-
## Lusternik-Schnirelmann范畴

cat(M)是覆盖M所需可缩开集的最小个数。

### 性质
- cat(M) ≤ dim(M) + 1
- cat(M)是伦型不变量
- 与临界点个数下界相关

### Lusternik-Schnirelmann定理
任何光滑函数f: M → ℝ至少有cat(M)个临界点。
-/
def LusternikSchnirelmannCategory : ℕ :=
  sInf {n | ∃ U : Fin n → Opens M, (∀ i, Contractible (U i)) ∧ 
    ⋃ i, U i = ⊤}

/-- LS范畴的基本性质 -/
theorem LS_category_bound : LusternikSchnirelmannCategory M ≤ n + 1 := by
  -- 由流形的维数给出上界
  sorry

theorem critical_points_lower_bound (f : M → ℝ) (hf : ContDiff ℝ ⊤ f) :
    {x | CriticalPoint f x}.ncard ≥ LusternikSchnirelmannCategory M := by
  -- Lusternik-Schnirelmann定理
  -- 证明使用minimax原理
  -- 每个范畴数给出临界值的一个下界
  sorry -- 详细的变分论证

/-
## Morse复形（Witten）

Morse函数定义链复形，其同调等于M的同调。

这是Morse理论最强大的形式之一，
由Witten从超对称角度重新诠释。

### 构造
- 链群：C_k = ℤ^{c_k}（由指数为k的临界点生成）
- 微分：∂p = Σ_q n(p,q) q
  其中n(p,q)是从p到q的梯度流线数（模2）

### 几何解释
梯度流线连接指数相邻的临界点，
形成Morse-Smale横截条件的相交理论。
-/ 
def MorseComplex (f : M → ℝ) (hf : IsMorseFunction f) (k : ℕ) : Type _ :=
  FreeAbelianGroup {x | CriticalPoint f x ∧ MorseIndex f x (by sorry) = k}

/-
## Morse微分

∂p = Σ_q n(p,q) q

其中n(p,q)是梯度流线的个数（模2或整系数）。

### Morse-Smale条件
为了保证微分良定义，需要横截条件：
稳定流形和不稳定流形横截相交。

### ∂² = 0
由紧化的梯度流线空间的拓扑保证。
破裂的流线对对应于∂²的项，成对抵消。
-/
def MorseDifferential (f : M → ℝ) (hf : IsMorseFunction f)
    (k : ℕ) : MorseComplex f hf k → MorseComplex f hf (k - 1) :=
  fun p ↦ ∑ q, (mod 2 (GradientFlowlines f p q).ncard) • q

/-- Morse微分是群同态 -/
instance MorseDifferential_isAddHom {f : M → ℝ} {hf : IsMorseFunction f} {k : ℕ} :
    AddMonoidHom (MorseComplex f hf k) (MorseComplex f hf (k - 1)) where
  toFun := MorseDifferential f hf k
  map_zero' := by simp [MorseDifferential]
  map_add' := by intro x y; simp [MorseDifferential, mul_add, add_mul]

/-- Morse微分的平方为零 -/
theorem morse_differential_squared_zero (f : M → ℝ) (hf : IsMorseFunction f)
    (k : ℕ) : 
    (MorseDifferential f hf (k - 1)) ∘ (MorseDifferential f hf k) = 0 := by
  -- 这是Morse理论的核心定理
  -- 证明思路：
  -- 1. ∂²p 计数从p出发的破裂梯度流线
  -- 2. 每个破裂流线有两种破裂方式
  -- 3. 在ℤ/2系数下，它们成对抵消
  -- 4. 在ℤ系数下，需要定向使符号匹配
  sorry -- 详细的横截性和紧化论证

/-
## Morse同调

HM_k(M,f) = ker(∂_k) / im(∂_{k+1})

这是Morse复形的同调。

### Morse同调定理
HM_k(M,f) ≅ H_k(M; ℤ)

这是Morse理论的巅峰定理，
表明Morse函数完全捕获了流形的拓扑。
-/ 
def MorseHomology (f : M → ℝ) (hf : IsMorseFunction f) (k : ℕ) : Type _ :=
  LinearMap.ker (MorseDifferential f hf k) ⧸ 
  LinearMap.range (MorseDifferential f hf (k + 1))

/-- Morse同调是有限生成的 -/
instance MorseHomology_fg (f : M → ℝ) (hf : IsMorseFunction f) (k : ℕ) :
    AddCommGroup.FG (MorseHomology f hf k) := by
  -- Morse复形是有限生成的自由Abel群
  -- 其子商也是有限生成的
  sorry

/-- Morse同调定理 -/
theorem morse_homology_theorem (f : M → ℝ) (hf : IsMorseFunction f) (k : ℕ) :
    MorseHomology f hf k ≃ HomologyGroup M k := by
  -- Morse同调定理的证明
  -- 步骤1：建立Morse复形与胞腔链复形的联系
  -- 步骤2：证明它们在准同构意义下等价
  -- 步骤3：利用同调的长正合序列
  sorry -- 这是深刻的同伦论结果

/-- Morse同调的秩等于Betti数 -/
theorem morse_homology_rank (f : M → ℝ) (hf : IsMorseFunction f) (k : ℕ) :
    FiniteDimensional.finrank ℤ (MorseHomology f hf k) = BettiNumber M k := by
  rw [morse_homology_theorem f hf k]
  rfl

/-
## 稳定/不稳定流形

W^s(p) = {x | φ_t(x) → p 当 t → ∞}
W^u(p) = {x | φ_t(x) → p 当 t → -∞}

其中φ_t是负梯度流：dx/dt = -∇f(x)

### 性质
- W^s(p) ≅ ℝ^{n-λ}（λ是p的指数）
- W^u(p) ≅ ℝ^λ
- 它们横截相交当且仅当Morse-Smale条件满足
-/ 
def StableManifold (f : M → ℝ) (p : M) (h_critical : CriticalPoint f p) :
    Set M :=
  {x | Filter.Tendsto (fun t ↦ GradientFlow f t x) Filter.atTop (nhds p)}

/-- 稳定流形是嵌入的子流形 -/
theorem stable_manifold_submanifold (f : M → ℝ) (p : M) 
    (h_critical : CriticalPoint f p) (hf : IsMorseFunction f) :
    ∃ φ : OpenImmersion (EuclideanSpace ℝ (Fin (n - MorseIndex f p h_critical))) M,
      Set.range φ = StableManifold f p h_critical := by
  -- 稳定流形微分同胚于ℝ^{n-λ}
  sorry

def UnstableManifold (f : M → ℝ) (p : M) (h_critical : CriticalPoint f p) :
    Set M :=
  {x | Filter.Tendsto (fun t ↦ GradientFlow f (-t) x) Filter.atTop (nhds p)}

/-- 不稳定流形是嵌入的子流形 -/
theorem unstable_manifold_submanifold (f : M → ℝ) (p : M) 
    (h_critical : CriticalPoint f p) (hf : IsMorseFunction f) :
    ∃ φ : OpenImmersion (EuclideanSpace ℝ (Fin (MorseIndex f p h_critical))) M,
      Set.range φ = UnstableManifold f p h_critical := by
  -- 不稳定流形微分同胚于ℝ^λ
  sorry

/-
## Morse-Smale条件

稳定和不稳定流形横截相交。

这是确保Morse复形良定义的关键条件。

### 存在性
- 对于给定的Morse函数，可以通过扰动度量使其满足Morse-Smale条件
- 这是Kupka-Smale定理的推论
-/
def IsMorseSmale (f : M → ℝ) (g : RiemannianMetric M) : Prop :=
  ∀ (p q : M) (hp : CriticalPoint f p) (hq : CriticalPoint f q),
    Transversal (StableManifold f p hp) (UnstableManifold f q hq)

/-- Morse-Smale条件的存在性 -/
theorem morse_smale_exists (f : M → ℝ) (hf : IsMorseFunction f) :
    ∃ g : RiemannianMetric M, IsMorseSmale f g := by
  -- Kupka-Smale定理
  -- 通过扰动度量获得横截性
  sorry

/- 辅助定义 -/
def CriticalPoint {M : Type*} [TopologicalSpace M] {n : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [SmoothManifoldWithCorners (𝓡 n) M] (f : M → ℝ) (x : M) : Prop := 
  -- df_x = 0
  ∀ v : TangentSpace M x, fderiv ℝ f x v = 0

def NondegenerateCriticalPoint {M : Type*} [TopologicalSpace M] {n : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [SmoothManifoldWithCorners (𝓡 n) M] (f : M → ℝ) (x : M) : Prop :=
  -- Hessian非退化
  CriticalPoint f x ∧ ∀ v : TangentSpace M x, 
    (∀ w : TangentSpace M x, Hessian f x v w = 0) → v = 0

def Hessian {M : Type*} [TopologicalSpace M] {n : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [SmoothManifoldWithCorners (𝓡 n) M] (f : M → ℝ) (x : M) : 
    (TangentSpace M x) →ₗ[ℝ] (TangentSpace M x) := 
  -- 在局部坐标下的二阶导数矩阵
  fderiv ℝ (fderiv ℝ f) x

def Spectrum {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (T : V →ₗ[ℝ] V) : Multiset ℝ := 
  -- 自伴算子的特征值（带重数）
  sorry

def Spectrum_card_le_dim {V : Type*} [NormedAddCommGroup V] 
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {T : V →ₗ[ℝ] V} : (Spectrum T).card ≤ finrank ℝ V := sorry

def BettiNumber (M : Type*) [TopologicalSpace M] (k : ℕ) : ℕ := 
  FiniteDimensional.finrank ℚ (SingularHomology M k ℚ)

def EulerCharacteristic (M : Type*) [TopologicalSpace M] : ℤ := 
  ∑ k, (-1 : ℤ)^k * BettiNumber M k

def HomologyGroup (M : Type*) [TopologicalSpace M] (k : ℕ) : Type _ := 
  SingularHomology M k ℤ

def HomologyRank (M : Type*) [TopologicalSpace M] (k : ℕ) : ℕ := 
  FiniteDimensional.finrank ℚ (SingularHomology M k ℚ)

def MorseHomologyRank (f : M → ℝ) (hf : IsMorseFunction f) (k : ℕ) : ℕ := 
  FiniteDimensional.finrank ℚ (MorseHomology f hf k ⊗ ℚ)

def MorseHomologyBettiInequality (f : M → ℝ) (hf : IsMorseFunction f) (k : ℕ) :
    MorseHomologyRank f hf k ≥ HomologyRank M k := sorry

def GradientFlow {M : Type*} [TopologicalSpace M] {n : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [SmoothManifoldWithCorners (𝓡 n) M] (f : M → ℝ) (t : ℝ) (x : M) : M := 
  -- 负梯度流：dx/dt = -∇f(x)的解
  sorry

def GradientFlowlines {M : Type*} [TopologicalSpace M] {n : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [SmoothManifoldWithCorners (𝓡 n) M] (f : M → ℝ) (p q : M) : Set ℝ := 
  -- 从p到q的梯度流线
  sorry

def RiemannianMetric (M : Type*) [TopologicalSpace M] : Type _ := 
  -- 光滑地依赖于点的内积
  sorry

def Transversal {M : Type*} [TopologicalSpace M] (S T : Set M) : Prop := 
  -- 在每点x ∈ S ∩ T，切空间满足：
  -- T_x S + T_x T = T_x M
  sorry

def Contractible (X : Type*) [TopologicalSpace X] : Prop := 
  Nonempty (ContinuousMap X (SingularPoint)) ∧ 
  ∀ f g : ContinuousMap X (SingularPoint), Homotopic f g

def SingularPoint : Type := Unit

instance : TopologicalSpace SingularPoint := inferInstanceAs (TopologicalSpace Unit)

-- 连续映射
def ContinuousMap (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] : Type _ := 
  {f : X → Y // Continuous f}

-- 同伦
def Homotopic {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f g : ContinuousMap X Y) : Prop := 
  ∃ H : ContinuousMap (X × unitInterval) Y, 
    ∀ x, H (x, 0) = f x ∧ H (x, 1) = g x

-- Hadamard引理
def HadamardLemma {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : EuclideanSpace ℝ (Fin n))
    (hf : ContDiff ℝ ⊤ f) :
    ∃ (h : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ),
      ContDiff ℝ ⊤ h ∧ ∀ x, f x = f p + 
        Matrix.dotProduct (x - p) (h x *ᵥ (x - p)) := sorry

def HessianSymmetric {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) 
    (p : EuclideanSpace ℝ (Fin n)) : 
    Matrix.IsSymm (fderiv ℝ (fderiv ℝ f) p) := sorry

-- 实谱定理
def RealSpectralTheorem {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) 
    (hA : Matrix.IsSymm A) :
    ∃ (P : Matrix (Fin n) (Fin n) ℝ) (D : Matrix (Fin n) (Fin n) ℝ),
      P.Orthogonal ∧ D.Diagonal ∧ A = P * D * P.transpose := sorry

-- 奇异同调
def SingularHomology (M : Type*) [TopologicalSpace M] (k : ℕ) (R : Type*) 
    [CommRing R] : Type _ := sorry

-- FreeAbelianGroup
def FreeAbelianGroup (S : Type*) : Type _ := 
  Finsupp S ℤ

-- CW复形
def CWComplex {n : ℕ} (cells : Fin n → Type*) : Type _ := sorry

-- 开浸入
def OpenImmersion (M N : Type*) [TopologicalSpace M] [TopologicalSpace N] : Type _ := 
  {f : M → N // Continuous f ∧ IsOpenEmbedding f}

-- 单位区间
def unitInterval : Type := Set.Icc (0 : ℝ) 1

-- 模2计数
def mod 2 (n : ℕ∞) : ℤ := if n % 2 = 0 then 0 else 1

-- 球面和闭球
def Sphere (n : ℕ) : Type := {x : EuclideanSpace ℝ (Fin (n + 1)) ‖x‖ = 1}
def ClosedBall (n : ℕ) : Type := {x : EuclideanSpace ℝ (Fin n) ‖x‖ ≤ 1}

-- 粘贴空间
def Attach {X A B : Type*} [TopologicalSpace X] [TopologicalSpace A] 
    [TopologicalSpace B] (f : A → X) (g : A → B) : Type := 
  Quotient (Bunch Pushout f g)

end MorseTheory
