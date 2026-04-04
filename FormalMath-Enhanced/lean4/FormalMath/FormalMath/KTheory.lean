/-
# K-理论基础与进阶 (K-Theory)

## 数学背景

K-理论是研究向量丛（或模）的稳定等价类的代数拓扑工具。
它提供了上同调理论的推广，在指标定理、代数几何和数论中有核心应用。

由Grothendieck在代数几何中引入，Atiyah和Hirzebruch将其推广到拓扑空间。

## 核心概念
- K⁰(X)：向量丛的Grothendieck群
- 约化K-理论 K̃⁰(X)
- Bott周期性
- Thom同构
- Atiyah-Hirzebruch谱序列
- 指标定理

## 参考
- Atiyah, M.F. "K-Theory"
- Hatcher, "Vector Bundles and K-Theory"
- Karoubi, M. "K-Theory: An Introduction"
- Weibel, C. "The K-book"

## 证明策略说明

本文件包含拓扑K-理论和代数K-理论的核心定理。
这些定理需要大量代数拓扑背景，我们提供完整的证明框架和详细注释。
-/ 

import FormalMath.Mathlib.Topology.VectorBundle.Basic
import FormalMath.Mathlib.AlgebraicTopology.CechNerve
import FormalMath.Mathlib.LinearAlgebra.CliffordAlgebra.Basic

namespace KTheory

open TopologicalSpace CategoryTheory

universe u v w

variable {X : Type u} [TopologicalSpace X] [CompactSpace X]

/-
## 向量丛的半群

同构类向量丛在同构直和下形成交换半群。

### 构造
- 对象：复向量丛 E → X（有限秩）
- 运算：[E] + [F] = [E ⊕ F]（Whitney和）
- 等价关系：E ~ F 当且仅当 E ≅ F（向量丛同构）
-/ 

/-- 向量丛同构类 -/
structure VectorBundleIsoClass where
  /-- 秩 -/
  rank : ℕ
  /-- 向量丛 -/
  bundle : VectorBundle ℂ (Fin rank → ℂ) X

/-- 向量丛的直和 -/
def VectorBundleIsoClass.add (E F : VectorBundleIsoClass X) : VectorBundleIsoClass X where
  rank := E.rank + F.rank
  bundle := sorry -- Whitney和

/-- 向量丛半群 -/
instance : AddCommSemigroup (VectorBundleIsoClass X) where
  add := VectorBundleIsoClass.add
  add_assoc := by 
    -- 证明直和满足结合律
    -- (E ⊕ F) ⊕ G ≅ E ⊕ (F ⊕ G)
    -- 由向量丛范畴的幺半范畴结构
    intro E F G
    sorry
  add_comm := by 
    -- 证明直和满足交换律
    -- E ⊕ F ≅ F ⊕ E
    -- 由向量空间的直和交换性提升
    intro E F
    sorry

/-
## Grothendieck群K⁰(X)

K⁰(X)是VectorBundleSemigroup的Grothendieck完备化。

### 构造
给定交换半群(M,+)，其Grothendieck群是形式差m-n的群，
模等价关系：m-n = p-q 当且仅当 ∃r, m+q+r = n+p+r

### 泛性质
Grothendieck群是包含M的最小阿贝尔群。
-/ 

/-- Grothendieck群构造 -/
def GrothendieckGroup (M : Type*) [AddCommSemigroup M] : Type _ :=
  {p : M × M // ∃ r : M, p.1 + p.2.2 + r = p.2.1 + p.1.2 + r} ⧸
    (fun x y ↦ x.val = y.val)

instance {M : Type*} [AddCommSemigroup M] : AddCommGroup (GrothendieckGroup M) := by
  unfold GrothendieckGroup
  -- 构造加法逆元
  sorry

/-- K⁰(X)群 -/
def K0 : Type _ :=
  GrothendieckGroup (VectorBundleIsoClass X)

instance : AddCommGroup (K0 X) := by
  unfold K0
  infer_instance

/-
## 环结构

K⁰(X)是张量积下的交换环。

### 乘法
[E] · [F] = [E ⊗ F]（向量丛的张量积）

### 单位元
[ε¹]：平凡线丛

### 验证
需要验证分配律、结合律等，这些都来自向量丛范畴的性质。
-/ 

/-- K⁰的乘法 -/
def K0.mul (E F : K0 X) : K0 X :=
  sorry -- 张量积诱导

/-- K⁰的单位元 -/
def K0.one : K0 X :=
  sorry -- 平凡线丛

instance : CommRing (K0 X) where
  mul := K0.mul
  mul_assoc := by 
    -- 张量积结合律：(E ⊗ F) ⊗ G ≅ E ⊗ (F ⊗ G)
    sorry
  one := K0.one
  one_mul := by 
    -- ε¹ ⊗ E ≅ E
    sorry
  mul_one := by 
    -- E ⊗ ε¹ ≅ E
    sorry
  left_distrib := by 
    -- E ⊗ (F ⊕ G) ≅ (E ⊗ F) ⊕ (E ⊗ G)
    sorry
  right_distrib := by 
    -- (F ⊕ G) ⊗ E ≅ (F ⊗ E) ⊕ (G ⊗ E)
    sorry
  mul_comm := by 
    -- 张量积交换性：E ⊗ F ≅ F ⊗ E
    sorry
  zero_mul := sorry
  mul_zero := sorry

/-
## 约化K-理论

K̃⁰(X) = ker(K⁰(X) → K⁰(pt))

### 几何意义
- 对应稳定等价的向量丛
- 对于连通空间，K̃⁰(X) = K̃⁰(X, x₀)
- 与约化上同调类似
-/ 

/-- 秩同态 -/
def rankHom : K0 X →+ ℤ :=
  sorry -- 向量丛的秩

/-- 约化K-理论 -/
def ReducedK0 : Type _ :=
  (rankHom (X := X)).ker

/-- K⁰的分解：K⁰(X) ≅ K̃⁰(X) ⊕ ℤ -/
theorem k0_decomposition :
    K0 X ≃+ ReducedK0 X × ℤ := by
  -- 利用秩同态的截面
  sorry

/-
## K⁰与上同调的关系

Chern特征ch : K⁰(X) → H^{even}(X; ℚ) 是有理同构。

### 构造
对于线丛L，ch(L) = exp(c₁(L)) = 1 + c₁(L) + c₁(L)²/2! + ...
对于一般向量丛，利用分裂原理。

### 重要性
- Chern特征将K-理论中的乘法对应到上同调的cup积
- 是有理同构，但非整同构
-/ 

/-- Chern特征 -/
def ChernCharacter : K0 X → DirectSum (fun i ↦ CohomologyGroup X (2 * i) ℚ) :=
  sorry

/-- Chern特征是环同态 -/
theorem chern_character_ring_hom :
    ∀ (E F : K0 X), ChernCharacter (E * F) =
      sorry -- ChernCharacter E ⌣ ChernCharacter F
  := by
  -- 利用分裂原理
  -- 将向量丛分裂为线丛的直和
  sorry

/-
## Chern特征是有理同构

**定理**：ch ⊗ ℚ : K⁰(X) ⊗ ℚ ≅ H^{even}(X; ℚ)

### 证明思路
1. 对于复射影空间ℂPⁿ，直接验证
2. 利用胞腔逼近，对有限CW复形归纳
3. 利用Mayer-Vietoris序列对一般空间
4. 关键：Chern特征保持乘法（环同态）
-/ 

/-- Chern特征是有理同构 -/
theorem chern_character_rational_isomorphism :
    let K0_Q := K0 X ⊗[ℤ] ℚ
    let H_even := DirectSum (fun i ↦ CohomologyGroup X (2 * i) ℚ)
    Function.Bijective (ChernCharacter (X := X)) := by
  -- 证明框架（Chern特征同构）：
  
  -- 步骤1: 对于X = pt（单点）
  -- K⁰(pt) = ℤ, H^{even}(pt) = ℚ
  -- ch : ℤ → ℚ是标准包含，ch⊗ℚ是同构
  
  -- 步骤2: 对于X = ℂPⁿ（复射影空间）
  -- K⁰(ℂPⁿ) = ℤ[ξ]/(ξ^{n+1})，其中ξ = [γ¹] - 1
  -- H^*(ℂPⁿ) = ℤ[x]/(x^{n+1})
  -- ch(ξ) = exp(x) - 1，诱导同构
  
  -- 步骤3: 对于有限CW复形，归纳法
  -- 利用贴胞腔的正合序列
  -- 五引理（Five Lemma）完成归纳步骤
  
  -- 步骤4: 一般紧空间
  -- 利用CW逼近
  sorry

/-
## 高阶K-群

利用Bott周期性定义所有K-群。

### 定义
K⁻ⁿ(X) = K̃⁰(Sⁿ ∧ X)
其中Sⁿ是n维球面，∧是压碎积（smash product）。

利用Bott周期性，只需要周期为2的群。
-/ 

/-- n维球面 -/
def Sphere (n : ℕ) : Type _ :=
  sorry

/-- 纬悬 -/
def Suspension (X : Type u) [TopologicalSpace X] : Type u :=
  sorry

/-- n重纬悬 -/
def Suspension^[n] (X : Type u) [TopologicalSpace X] : Type u :=
  match n with
  | 0 => X
  | n + 1 => Suspension (Suspension^[n] X)

/-- 高阶K-群 -/
def HigherK (n : ℕ) : Type _ :=
  ReducedK0 (Suspension^[n] X)

/-
## Bott周期性

**定理**：K⁻ⁿ(X) ≅ K⁻ⁿ⁻²(X)

### 复Bott周期性
K⁰(X) ≅ K̃⁰(S² ∧ X)
或等价地，K̃⁰(S² × X) ≅ K̃⁰(X) ⊕ K̃⁰(S² ∧ X)

### 证明思路
1. 利用Clifford代数或Toeplitz算子
2. 构造显式的同构（Bott元素）
3. 验证诱导了K-群的同构

### 重要性
- 使得K-理论成为广义上同调理论
- 周期为2（复K-理论）或8（实K-理论）
-/ 

/-- Bott元素 -/
def BottElement : ReducedK0 (Sphere 2) :=
  sorry -- [γ¹] - 1，其中γ¹是 tautological 线丛

/-- Bott周期性的同构 -/
def BottIsomorphism : HigherK (n + 2) X ≃ HigherK n X :=
  sorry

/-- Bott周期性定理 -/
theorem bott_periodicity_theorem (n : ℕ) :
    Function.Bijective (BottIsomorphism (X := X) (n := n)) := by
  -- 证明框架（Bott周期性）：
  
  -- 步骤1: 构造Bott元素
  -- 令β = [γ¹] - 1 ∈ K̃⁰(S²)
  -- 其中γ¹是S² = ℂP¹上的 tautological 线丛
  
  -- 步骤2: 定义映射
  -- φ : K⁰(X) → K̃⁰(S² ∧ X)
  -- φ([E]) = β · [E]（外积）
  
  -- 步骤3: 构造逆映射
  -- 利用Thom同构（对于平凡丛）
  -- ψ : K̃⁰(S² ∧ X) → K⁰(X)
  
  -- 步骤4: 验证φ∘ψ = id和ψ∘φ = id
  -- 对于X = pt，利用K⁰(S²) = ℤ[β]/(β²)
  -- 一般情况利用五引理
  sorry

/-
## 复Bott周期性的显式表述

K⁰(X) ≅ K̃⁰(S² ∧ X)

这是计算K-群的关键工具。
-/ 

/-- 压碎积 -/
def SmashProduct (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] :
    Type u :=
  sorry

/-- 复Bott周期性（显式形式） -/
theorem complex_bott_periodicity_explicit :
    K0 X ≃ ReducedK0 (SmashProduct (Sphere 2) X) := by
  -- 这是Bott周期性的特例（n=0）
  -- 直接应用bott_periodicity
  sorry

/-
## K-理论中的Thom同构

对于复向量丛E → X，有Thom同构：
K⁰(X) ≅ K̃⁰(Th(E))

其中Th(E)是E的Thom空间（一点紧化）。

### 几何意义
这是K-理论版本的Poincaré对偶。
-/ 

/-- Thom空间（一点紧化） -/
def ThomSpace {n : ℕ} (E : VectorBundle ℂ (Fin n → ℂ) X) : Type u :=
  sorry

/-- Thom类 -/
def ThomClass {n : ℕ} (E : VectorBundle ℂ (Fin n → ℂ) X) :
    ReducedK0 (ThomSpace E) :=
  sorry

/-- Thom同构 -/
def ThomIsomorphism {n : ℕ} (E : VectorBundle ℂ (Fin n → ℂ) X) :
    K0 X ≃ ReducedK0 (ThomSpace E) :=
  sorry

/-- Thom同构定理 -/
theorem thom_isomorphism_theorem {n : ℕ} (E : VectorBundle ℂ (Fin n → ℂ) X) :
    Function.Bijective (ThomIsomorphism E) := by
  -- 证明框架（Thom同构）：
  
  -- 步骤1: 构造Thom类
  -- 对于复向量丛E，有自然定义的Thom类λ_E ∈ K̃⁰(Th(E))
  -- 利用外代数丛Λ^* E
  
  -- 步骤2: 定义Thom映射
  -- φ : K⁰(X) → K̃⁰(Th(E))
  -- φ(x) = π*(x) · λ_E
  -- 其中π : Th(E) → X是投影
  
  -- 步骤3: 证明φ是同构
  -- 对于平凡丛，Th(E) = S^{2n} ∧ X₊
  -- 利用Bott周期性
  -- 一般情况利用Mayer-Vietoris和有限型逼近
  sorry

/-
## K-理论的长正合序列

对于闭子空间A ⊆ X，有长正合序列：
⋯ → K⁻ⁿ(X,A) → K⁻ⁿ(X) → K⁻ⁿ(A) → K⁻ⁿ⁺¹(X,A) → ⋯

### 证明
利用映射锥或 Puppe 序列。
-/ 

/-- 相对K-群 -/
def RelativeKGroup (n : ℤ) (A : Set X) : Type u :=
  sorry -- K̃ⁿ(X/A) 或等价定义

/-- 商空间 -/
def QuotientSpace (A : Set X) : Type u :=
  sorry

/-- 正合性 -/
def Exact {A B C : Type*} (f : A → B) (g : B → C) : Prop :=
  ∀ b : B, g b = 0 ↔ ∃ a : A, f a = b

/-- K-理论的长正合序列 -/
theorem ktheory_long_exact {A : Set X} (hA : IsClosed A) (n : ℤ) :
    let i : RelativeKGroup (n + 1) X A → HigherK (n + 1) X := sorry
    let j : HigherK (n + 1) X → HigherK (n + 1) A := sorry
    let ∂ : HigherK (n + 1) A → RelativeKGroup n X A := sorry
    Exact i j ∧ Exact j ∂ := by
  -- 证明框架（长正合序列）：
  
  -- 步骤1: 构造相对K-群
  -- K⁰(X,A) = K̃⁰(X/A)
  -- 其中X/A是商空间（A坍缩为一点）
  
  -- 步骤2: 利用Puppe序列
  -- A → X → X/A → SA → SX → ...
  -- 其中S是纬悬（suspension）
  
  -- 步骤3: 应用K-理论函子
  -- K-理论是广义上同调理论，将cofiber序列映为正合序列
  
  -- 步骤4: 利用Bott周期性连接不同维数
  sorry

/-
## 指标定理的K-理论表述

Atiyah-Singer指标定理可以用K-理论表述。

### 符号类
椭圆算子D : Γ(E) → Γ(F)有符号σ(D)，
定义了K⁰(T*X)中的类（T*X的余切丛）。

### 指标公式
index(D) = π_!(σ(D))
其中π_! : K⁰(T*X) → K⁰(pt) = ℤ是推进（Gysin映射）。
-/ 

/-- 椭圆算子 -/
structure EllipticOperator (E F : VectorBundle ℂ (Fin n → ℂ) X) where
  /-- 算子本身 -/
  operator : Section E → Section F
  /-- 椭圆性条件：符号处处非零 -/
  elliptic : ∀ x, Symbol operator x ≠ 0

/-- 截面 -/
def Section {n : ℕ} (E : VectorBundle ℂ (Fin n → ℂ) X) : Type _ :=
  sorry

/-- 符号 -/
def Symbol {n : ℕ} {E F : VectorBundle ℂ (Fin n → ℂ) X}
    (D : EllipticOperator E F) : VectorBundleHom
      (PullbackBundle (CotangentBundle X) E)
      (PullbackBundle (CotangentBundle X) F) :=
  sorry

/-- 向量丛同态 -/
structure VectorBundleHom {n m : ℕ}
    (E : VectorBundle ℂ (Fin n → ℂ) X) (F : VectorBundle ℂ (Fin m → ℂ) X) where
  hom : ∀ x, (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ)

/-- 拉回丛 -/
def PullbackBundle {n : ℕ}
    (E : VectorBundle ℂ (Fin n → ℂ) X) {m : ℕ}
    {F : VectorBundle ℂ (Fin m → ℂ) X} :
    VectorBundle ℂ (Fin m → ℂ) X :=
  sorry

/-- 余切丛 -/
def CotangentBundle (X : Type u) [TopologicalSpace X] : Type u :=
  sorry

/-- 解析指标 -/
def AnalyticIndex {E F : VectorBundle ℂ (Fin n → ℂ) X}
    (D : EllipticOperator E F) : ℤ :=
  let ker_dim := sorry -- dim ker D.operator
  let coker_dim := sorry -- dim coker D.operator
  ker_dim - coker_dim

/-- 拓扑指标（K-理论版本） -/
def TopologicalIndexK {E F : VectorBundle ℂ (Fin n → ℂ) X}
    (D : EllipticOperator E F) : ℤ :=
  let symbol_class := sorry -- [σ(D)] ∈ K⁰(T*X)
  let thom_iso := ThomIsomorphism sorry -- 利用Thom同构
  let pushforward := thom_iso.symm symbol_class
  sorry -- PushforwardToPoint pushforward

/-
## Atiyah-Singer指标定理

**定理**：AnalyticIndex(D) = TopologicalIndex(D)

### 证明思路
1. 利用K-理论的Thom同构
2. 将符号类从T*X推送到X
3. 利用Todd类调整（Chern特征不保持推进）
4. 最终得到拓扑指标公式

### 应用
- 证明Riemann-Roch定理
- 证明Hirzebruch符号定理
- 数学物理中的反常消去
-/ 

theorem atiyah_singer_index_theorem_k {E F : VectorBundle ℂ (Fin n → ℂ) X}
    (D : EllipticOperator E F) :
    AnalyticIndex D = TopologicalIndexK D := by
  -- 证明框架（Atiyah-Singer指标定理）：
  
  -- 步骤1: 符号类的构造
  -- σ(D) ∈ K⁰(T*X)，在无穷远处支集
  -- 利用Thom同构K⁰(T*X) ≅ K⁰(X)
  
  -- 步骤2: 拓扑指标的定义
  -- ind_t(D) = π_!(σ(D)) ∈ K⁰(pt) = ℤ
  -- 其中π : T*X → X是投影
  
  -- 步骤3: 解析指标的同伦不变性
  -- 若D_t是椭圆算子的连续族，则index(D_t)是常数
  -- 利用Fredholm算子的开性
  
  -- 步骤4: 证明等式
  -- - 对于Dirac型算子，直接验证
  -- - 利用K-理论的生成性，对一般算子成立
  
  -- 步骤5: 具体公式（紧Lie群情形）
  -- index(D) = ∫_X ch(E) ∧ td(TX) ∧ ...（依赖于具体算子）
  sorry

/-
## 代数K-理论

对于环R，K₀(R)是有限生成投射R-模的Grothendieck群。

### 定义
- 对象：有限生成投射R-模
- 运算：[P] + [Q] = [P ⊕ Q]
- 等价关系：同构
-/ 

/-- 有限生成投射模的同构类 -/
structure ProjectiveModuleClass (R : Type u) [Ring R] where
  /-- 模 -/
  module : Type v
  /-- 是有限生成投射模 -/
  is_projective : sorry -- Module.Finite R module ∧ Module.Projective R module

/-- 代数K₀ -/
def AlgebraicK0 (R : Type u) [Ring R] : Type _ :=
  GrothendieckGroup (ProjectiveModuleClass R)

/-
## 投影模与向量丛的对应

交换环的Spec上的向量丛对应投射模。

### Swan定理
设X紧Hausdorff，C(X)是连续函数环，则：
K⁰(X) ≅ K₀(C(X))

### 几何意义
拓扑K-理论与代数K-理论通过Serre-Swan定理联系。
-/ 

theorem swan_theorem {R : Type u} [CommRing R] (hX : X ≃ PrimeSpectrum R) :
    K0 X ≃ AlgebraicK0 R := by
  -- 证明框架（Swan定理）：
  
  -- 步骤1: 构造对应
  -- 向量丛E → X ↦ Γ(E)：连续截面的模
  -- 利用局部平凡性，Γ(E)是有限生成投射C(X)-模
  
  -- 步骤2: 逆对应
  -- 投射模P ↦ 向量丛E_P
  -- 利用Serre定理：投射模是自由模的直和项
  
  -- 步骤3: 验证函子性
  -- 直和对应直和
  -- 张量积对应张量积
  
  -- 步骤4: 证明是群同构
  -- 保持Grothendieck群结构
  sorry

/-- 素谱 -/
def PrimeSpectrum (R : Type u) [CommRing R] : Type u :=
  sorry

/-
## Milnor K-理论

Kₙ^M(k) = (k*)^{⊗n} / Steinberg关系

### Steinberg关系
对于a, 1-a ∈ k*，有{a, 1-a} = 0。

### 重要性
- 与Galois上同调的联系（Bloch-Kato猜想）
- 代数循环和高阶Chow群
- motivic上同调
-/ 

/-- Milnor K-群 -/
def MilnorK (k : Type u) [Field k] (n : ℕ) : Type u :=
  (kˣ)⊗[ℤ]^[n] ⧸
    (subgroup_generated_by {t | ∃ a ≠ 0, a ≠ 1, t = a ⊗ (1 - a)})

/-- 由集合生成的子群 -/
def subgroup_generated_by {G : Type*} [AddGroup G] (S : Set G) : Subgroup G :=
  sorry

/-- 张量幂 -/
notation:max M "⊗[ℤ]^[" n "]" => TensorPower M n

/-- 张量幂定义 -/
def TensorPower (M : Type*) [AddCommGroup M] (n : ℕ) : Type* :=
  match n with
  | 0 => ℤ
  | n + 1 => M ⊗[ℤ] TensorPower M n

/-
## Bloch-Kato猜想（现为Voevodsky定理）

**定理**：Kₙ^M(k)/m ≅ Hⁿ_{ét}(k, μ_m^{⊗n})

### 称为Norm Residue同构
- 左端：Milnor K-群（代数构造）
- 右端：Galois上同调（算术构造）

### 证明历史
- n=1：Hilbert第90定理
- n=2：Tate, Merkurjev-Suslin（1982）
- 一般n：Voevodsky（2003），Fields奖工作
-/ 

/-- Galois上同调 -/
def GaloisCohomology (k : Type u) [Field k] (n : ℕ) (M : Type*) : Type _ :=
  sorry

/-- μ_m^{⊗n} -/
def MuMToThe (n m : ℕ) : Type _ :=
  sorry

theorem norm_residue_isomorphism (k : Type u) [Field k] (n m : ℕ)
    (hm : m ≠ 0) (h_char : m.Coprime (ringChar k)) :
    MilnorK k n ⧸ (m • ⊤) ≃
    GaloisCohomology k n (MuMToThe n m) := by
  -- 证明框架（Bloch-Kato/Voevodsky定理）：
  
  -- 基本情况n=1：
  -- K₁^M(k) = k*
  -- H¹(k, μ_m) = k*/(k*)^m（Hilbert 90）
  -- 显然同构
  
  -- 基本情况n=2：
  -- Merkurjev-Suslin定理
  -- 利用Brauer群和循环代数
  
  -- 归纳步骤（Voevodsky的证明）：
  -- 步骤1: 构造motivic上同调
  -- H^m(k, ℤ(n))作为目标理论
  
  -- 步骤2: 证明 motivic 到 étale 的变换是同构
  -- 利用Beilinson-Lichtenbaum猜想
  -- （已证明，等价于Bloch-Kato）
  
  -- 步骤3: 计算 motivic 上同调
  -- H^n(k, ℤ(n)) = Kₙ^M(k)
  -- 由定义或Suslin的工作
  
  -- 步骤4: 结合得到同构
  -- Kₙ^M(k)/m → Hⁿ_{ét}(k, μ_m^{⊗n})
  sorry

/-
## 辅助定义 -/

/-- 直和 -/
def DirectSum {ι : Type*} (β : ι → Type*) : Type _ :=
  sorry

/-- 上同调群 -/
def CohomologyGroup (X : Type u) [TopologicalSpace X] (n : ℕ) (R : Type v)
    [Ring R] : Type _ :=
  sorry

end KTheory
