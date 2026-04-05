/-
# 拉东-尼科迪姆定理 (Radon-Nikodym Theorem)

## 数学背景

Radon-Nikodym定理是测度论中最深刻和最重要的定理之一。
它建立了绝对连续测度与积分表示之间的基本联系。

### 定理陈述

设 (X, 𝓐) 是可测空间，μ 和 ν 是 σ-有限测度。
如果 ν 关于 μ 绝对连续（记作 ν ≪ μ），即：
μ(E) = 0 ⇒ ν(E) = 0 对所有 E ∈ 𝓐

则存在唯一的（μ-几乎处处）非负可测函数 f: X → [0,∞]，使得：
ν(E) = ∫_E f dμ,  ∀E ∈ 𝓐

函数 f 称为 ν 关于 μ 的 **Radon-Nikodym导数**，记作 dν/dμ。

### 历史背景

该定理由奥地利数学家 Johann Radon（1913年）和
美国数学家 Otto Nikodym（1930年）独立证明。
它是Lebesgue分解定理的核心组成部分。

### 应用

- 概率论：条件期望的存在性
- 统计学：似然比、密度函数
- 鞅论：鞅的Doob-Meyer分解
- 遍历理论：不变测度的刻画
- 数学金融：等价鞅测度的存在

## 参考文献
- Rudin, "Real and Complex Analysis", Chapter 6
- Folland, "Real Analysis", Section 3.2
- Billingsley, "Probability and Measure", Section 32
- 夏道行、吴卓人、严绍宗、舒五昌，《实变函数论与泛函分析》
-/@

import Mathlib.MeasureTheory.Measure.Lebesgue
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Function.LpSpace
import Mathlib.MeasureTheory.Decomposition.Lebesgue

namespace RadonNikodym

open MeasureTheory Measure Set Filter ENNReal NNReal Topology

universe u v

variable {α : Type u} [MeasurableSpace α]

/-
## 绝对连续性 (Absolute Continuity)

### 定义
测度 ν 关于 μ 绝对连续，记作 ν ≪ μ，如果：
对于所有可测集 E，μ(E) = 0 蕴含 ν(E) = 0。

### 直观理解
绝对连续性意味着 ν "更精细"或"更受控于" μ：
- ν 的零集包含 μ 的零集
- 如果 μ 认为某个集合"很小"（测度为零），
  那么 ν 也必须认为它"很小"

### 例子
1. 若 f 是非负可积函数，则 ν(E) = ∫_E f dμ 满足 ν ≪ μ
2. Lebesgue测度关于Lebesgue测度本身绝对连续
3. Dirac测度 δ₀ 关于Lebesgue测度不绝对连续
-/

/-- 测度的绝对连续性 -/
def AbsolutelyContinuous' (ν μ : Measure α) : Prop :=
  ∀ (s : Set α), MeasurableSet s → μ s = 0 → ν s = 0

/-- 绝对连续性记号 ν ≪ μ -/
notation ν "≪" μ => AbsolutelyContinuous' ν μ

/-
### 绝对连续性的基本性质

**引理1（自反性）**: μ ≪ μ

**引理2（传递性）**: 若 ν ≪ μ 且 μ ≪ λ，则 ν ≪ λ

**引理3（与可和性交换）**: 若 {ν_i} 是一列测度且每个 ν_i ≪ μ，
则 ∑' ν_i ≪ μ
-/

/-- 绝对连续性的自反性 -/
lemma absolutelyContinuous_refl (μ : Measure α) : μ ≪ μ := by
  intro s _ hμs
  exact hμs

/-- 绝对连续性的传递性 -/
lemma absolutelyContinuous_trans {ν μ λ : Measure α} 
    (h₁ : ν ≪ μ) (h₂ : μ ≪ λ) : ν ≪ λ := by
  intro s hs hλs
  have hμs : μ s = 0 := h₂ s hs hλs
  exact h₁ s hs hμs

/-
## Radon-Nikodym导数的存在性

### 主要定理

**Radon-Nikodym定理**: 设 μ, ν 是 σ-有限测度，且 ν ≪ μ，
则存在非负可测函数 f 使得 ν(E) = ∫_E f dμ。

### 证明策略

这是一个深刻的定理，标准证明分为以下步骤：

1. **简化到有限测度情形**：利用 σ-有限性分解
2. **Hahn分解**：将问题转化为符号测度的情形
3. **构造极大元**：考虑所有满足 ∫_E f dμ ≤ ν(E) 的函数 f
4. **验证等式**：证明这个极大元满足等式
5. **唯一性**：证明 Radon-Nikodym导数的唯一性

### 有限测度情形的关键引理

设 μ, ν 是有限测度，ν ≪ μ。定义：
𝓕 = {f : X → [0,∞] 可测 | ∀E, ∫_E f dμ ≤ ν(E)}

令 M = sup{∫ f dμ | f ∈ 𝓕}，则 M ≤ ν(X) < ∞。

存在 f* ∈ 𝓕 使得 ∫ f* dμ = M。

**关键观察**：对于这个 f*，必有 ν(E) = ∫_E f* dμ。

否则，存在 E₀ 使得 ν(E₀) > ∫_{E₀} f* dμ。
令 g = f* + ε·1_{E₀}，则对足够小的 ε > 0，
有 g ∈ 𝓕 且 ∫ g dμ > M，矛盾。
-/

section RadonNikodymTheorem

/-- Radon-Nikodym定理的核心存在性部分

这是定理最关键的部分：给定 σ-有限测度 μ, ν 且 ν ≪ μ，
存在可测函数 f 使得 ν = f • μ（即 ν(E) = ∫_E f dμ）。

**证明框架**：
1. 首先处理有限测度情形（这是证明的核心）
2. 利用 σ-有限性通过可数分解推广
-/
theorem radon_nikodym_exists {μ ν : Measure α}
    [SigmaFinite μ] [SigmaFinite ν] (h_ac : ν ≪ μ) :
    ∃ f : α → ℝ≥0∞, Measurable f ∧ 
      ∀ (s : Set α), MeasurableSet s → ν s = ∫⁻ x in s, f x ∂μ := by
  -- 这个证明是测度论中最深刻的证明之一
  -- 主要分为以下几个步骤：
  
  -- 步骤1：利用 σ-有限性，将问题简化为有限测度情形
  -- 由于 μ 和 ν 都是 σ-有限的，存在可数分解
  -- X = ⋃_n A_n = ⋃_n B_n，其中 μ(A_n) < ∞, ν(B_n) < ∞
  
  -- 步骤2：在每个有限测度部分构造 Radon-Nikodym 导数
  -- 这是证明的核心，利用"极大元"技巧
  
  -- 步骤3：将这些局部导数拼接成全局导数
  -- 利用可测函数的可数拼接性质
  
  -- 步骤4：验证等式对所有可测集成立
  -- 利用测度的可数可加性和积分的线性性
  
  -- 在Mathlib4中，这个定理已经被完整证明
  -- 我们可以直接使用已有的实现
  use ν.rnDeriv μ
  constructor
  · /- Radon-Nikodym导数是可测的 -/
    exact Measure.measurable_rnDeriv ν μ
  · /- 验证积分表示 -/
    intro s hs
    /- 应用Radon-Nikodym定理的标准形式 -/
    /- 使用Mathlib4中的Radon-Nikodym导数性质 -/
    rw [Measure.rnDeriv_eq_rnDeriv_measure]
    · rfl
    · exact h_ac

/-
## 唯一性

### Radon-Nikodym导数的唯一性

**定理**：若 f, g 都是 ν 关于 μ 的 Radon-Nikodym导数，
则 f = g μ-几乎处处。

**证明**：令 E_n = {f - g ≥ 1/n}，则：
∫_{E_n} (f - g) dμ = ν(E_n) - ν(E_n) = 0

由于 f - g ≥ 1/n 在 E_n 上，这推出 μ(E_n) = 0。
因此 μ({f ≠ g}) = μ(⋃_n E_n) = 0。
-/

/-- Radon-Nikodym导数的唯一性 -/
theorem radon_nikodym_unique {μ ν : Measure α} {f g : α → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hf_eq : ∀ s, MeasurableSet s → ν s = ∫⁻ x in s, f x ∂μ)
    (hg_eq : ∀ s, MeasurableSet s → ν s = ∫⁻ x in s, g x ∂μ) :
    f =ᵐ[μ] g := by
  -- 证明思路：
  -- 1. 考虑集合 E = {x | f(x) > g(x)}
  -- 2. 证明 μ(E) = 0
  -- 3. 对称地证明 μ({x | f(x) < g(x)}) = 0
  -- 4. 因此 f = g μ-几乎处处
  /- 构造差集并证明测度为0 -/
  have h1 : μ {x | f x > g x} = 0 := by
    /- 反证法：若测度为正，则积分不等 -/
    by_contra hμ
    push_neg at hμ
    have h_int : ∫⁻ x in {x | f x > g x}, f x ∂μ = ∫⁻ x in {x | f x > g x}, g x ∂μ := by
      rw [hf_eq _ (measurableSet_lt hf hg), hg_eq _ (measurableSet_lt hf hg)]
    have h_gt : ∀ x ∈ {x | f x > g x}, f x > g x := fun x hx => hx
    have h_contra : ∫⁻ x in {x | f x > g x}, f x ∂μ > ∫⁻ x in {x | f x > g x}, g x ∂μ := by
      apply setLIntegral_strict_mono
      · exact measurableSet_lt hf hg
      · exact hμ
      · exact h_gt
    linarith
  have h2 : μ {x | f x < g x} = 0 := by
    /- 对称论证 -/
    by_contra hμ
    push_neg at hμ
    have h_int : ∫⁻ x in {x | f x < g x}, f x ∂μ = ∫⁻ x in {x | f x < g x}, g x ∂μ := by
      rw [hf_eq _ (measurableSet_lt hg hf), hg_eq _ (measurableSet_lt hg hf)]
    have h_lt : ∀ x ∈ {x | f x < g x}, f x < g x := fun x hx => hx
    have h_contra : ∫⁻ x in {x | f x < g x}, f x ∂μ < ∫⁻ x in {x | f x < g x}, g x ∂μ := by
      apply setLIntegral_strict_mono
      · exact measurableSet_lt hg hf
      · exact hμ
      · intro x hx; linarith [h_lt x hx]
    linarith
  /- 结合两部分 -/
  filter_upwards [measure_zero_iff_ae_nmem.1 h1, measure_zero_iff_ae_nmem.1 h2] with x h1 h2
  /- 在补集上f = g -/
  have h_eq : f x = g x := by
    have h_not_gt : ¬(f x > g x) := h1
    have h_not_lt : ¬(f x < g x) := h2
    linarith
  exact h_eq

/-
## Radon-Nikodym导数的定义

基于存在性和唯一性，我们可以定义 Radon-Nikodym导数。
-/

/-- Radon-Nikodym导数

这是测度论中最重要的概念之一。
给定 ν ≪ μ，Radon-Nikodym导数 dν/dμ 是满足：
ν(E) = ∫_E (dν/dμ) dμ 的唯一（μ-a.e.）可测函数。
-/
noncomputable def radonNikodymDerivative {μ ν : Measure α}
    [SigmaFinite μ] [SigmaFinite ν] (h_ac : ν ≪ μ) : α → ℝ≥0∞ :=
  Classical.choose (radon_nikodym_exists h_ac)

/-- 标准记号：dν/dμ -/
notation "d" ν "/d" μ => radonNikodymDerivative (by assumption)

/-- Radon-Nikodym导数的基本性质 -/
theorem rn_deriv_measurable {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]
    (h_ac : ν ≪ μ) : Measurable (dν/dμ) := by
  exact (Classical.choose_spec (radon_nikodym_exists h_ac)).1

/-- Radon-Nikodym导数满足积分表示 -/
theorem rn_deriv_spec {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]
    (h_ac : ν ≪ μ) (s : Set α) (hs : MeasurableSet s) :
    ν s = ∫⁻ x in s, (dν/dμ) x ∂μ := by
  exact (Classical.choose_spec (radon_nikodym_exists h_ac)).2 s hs

/-
## 链式法则 (Chain Rule)

**定理**：设 λ ≪ μ ≪ ν，则：
dλ/dν = (dλ/dμ) · (dμ/dν)   λ-几乎处处

这是微积分中链式法则在测度论中的推广。
-/

/-- Radon-Nikodym导数的链式法则 -/
theorem rn_deriv_chain_rule {μ ν λ : Measure α} [SigmaFinite μ] [SigmaFinite ν]
    [SigmaFinite λ] (h1 : ν ≪ μ) (h2 : λ ≪ ν) :
    (dλ/dμ) =ᵐ[λ] (dλ/dν) * (dν/dμ) := by
  -- 证明思路：
  -- 对任意可测集 E，验证两边积分相等
  -- ∫_E (dλ/dμ) dμ = λ(E)
  -- ∫_E (dλ/dν)(dν/dμ) dμ = ∫_E (dλ/dν) dν = λ(E)
  /- 应用Radon-Nikodym导数的唯一性 -/
  apply radon_nikodym_unique
  · /- 左边可测 -/
    apply rn_deriv_measurable
    exact absolutelyContinuous_trans h1 h2
  · /- 乘积可测 -/
    apply Measurable.mul
    · apply rn_deriv_measurable h2
    · apply rn_deriv_measurable h1
  · /- 验证左边的积分表示 -/
    intro s hs
    apply rn_deriv_spec
    exact absolutelyContinuous_trans h1 h2
  · /- 验证右边的积分表示 -/
    intro s hs
    /- 利用积分的变量替换 -/
    /- ∫_E (dλ/dν)(dν/dμ) dμ = ∫_E (dλ/dν) dν = λ(E) -/
    calc
      ∫⁻ x in s, (dλ/dμ) x ∂μ = ∫⁻ x in s, ((dλ/dν) x * (dν/dμ) x) ∂μ := by
        apply setLIntegral_congr_ae
        · exact hs
        · /- 几乎处处相等 -/
          sorry
      _ = ∫⁻ x in s, (dλ/dν) x ∂ν := by
        /- 变量替换公式 -/
        sorry
      _ = λ s := by
        apply rn_deriv_spec h2 hs

end RadonNikodymTheorem

/-
## 应用：条件期望

Radon-Nikodym定理最重要的应用之一是证明条件期望的存在性。
-/

section ConditionalExpectation

variable {Ω : Type*} [MeasurableSpace Ω] [ProbabilitySpace Ω]

/-
### 条件期望的存在性

设 X 是可积随机变量，𝓖 ⊂ 𝓕 是子 σ-代数。
条件期望 E[X | 𝓖] 是满足以下条件的随机变量 Y：
1. Y 是 𝓖-可测的
2. ∀G ∈ 𝓖, ∫_G Y dP = ∫_G X dP

Radon-Nikodym定理保证了这样的 Y 存在且唯一（a.s.）。
-/

/-- 条件期望的存在性（利用Radon-Nikodym定理） -/
theorem condexp_exists {X : Ω → ℝ} (hX : Integrable X) 
    {𝓖 : MeasurableSpace Ω} (hsub : 𝓖 ≤ ‹MeasurableSpace Ω›) :
    ∃ Y : Ω → ℝ, Measurable[𝓖] Y ∧ Integrable Y ∧
      ∀ (G : Set Ω), MeasurableSet[𝓖] G → ∫ ω in G, Y ω ∂ℙ = ∫ ω in G, X ω ∂ℙ := by
  -- 证明思路：
  -- 1. 在 (Ω, 𝓖) 上定义符号测度 ν(G) = ∫_G X dP
  -- 2. 显然 ν ≪ P（限制在 𝓖 上）
  -- 3. 由Radon-Nikodym定理，存在 dν/dP
  -- 4. 这个导数就是条件期望 E[X | 𝓖]
  /- 使用Mathlib4的条件期望实现 -/
  use μ[X|𝓖]
  constructor
  · /- 条件期望是𝓖-可测的 -/
    exact condexp_measurable 𝓖 X
  constructor
  · /- 条件期望是可积的 -/
    exact integrable_condexp
  · /- 验证积分性质 -/
    intro G hG
    exact setIntegral_condexp hsub hG hX

end ConditionalExpectation

/-
## 应用：密度函数

在概率论中，Radon-Nikodym导数就是概率密度函数。
-/

section DensityFunction

variable {Ω : Type*} [MeasurableSpace Ω] [ProbabilitySpace Ω]

/-- 概率密度函数的存在性 -/
theorem pdf_exists {X : Ω → ℝ} (hX : Measurable X) :
    ∀ (ν : Measure ℝ), ν ≪ Measure.map X ℙ →
    ∃ f : ℝ → ℝ≥0∞, Measurable f ∧ 
      ν = Measure.withDensity (Measure.map X ℙ) f := by
  -- 当 X 的分布关于Lebesgue测度绝对连续时，
  -- 存在密度函数 f，使得 P(X ∈ B) = ∫_B f(x) dx
  intro ν hν
  /- 应用Radon-Nikodym定理 -/
  rcases radon_nikodym_exists hν with ⟨f, hf_meas, hf_eq⟩
  use f
  constructor
  · exact hf_meas
  · /- 验证等式 -/
    ext s hs
    rw [hf_eq s hs]
    /- 使用withDensity的定义 -/
    /- 验证密度函数的积分表示 -/
    simp [Measure.withDensity]
    rfl

/-- 似然比 (Likelihood Ratio) -/
def likelihoodRatio {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]
    (h_ac : ν ≪ μ) : α → ℝ≥0∞ := dν/dμ

end DensityFunction

/-
## 证明思路详解

本节的剩余部分详细解释 Radon-Nikodym 定理的证明技术。
这些证明技巧在分析学中非常常见。
-/

section ProofTechniques

/-
### 极大元方法 (Maximal Element Method)

这是证明 Radon-Nikodym 定理的核心技巧。

**设定**：设 μ, ν 是有限测度，ν ≪ μ。
考虑函数族：
𝓕 = {f : X → [0,∞] 可测 | ∀E 可测, ∫_E f dμ ≤ ν(E)}

**引理1**：𝓕 非空（0 ∈ 𝓕）。

**引理2**：若 f, g ∈ 𝓕，则 max(f,g) ∈ 𝓕。

**证明**：令 A = {f ≥ g}，则：
∫_E max(f,g) dμ = ∫_{E∩A} f dμ + ∫_{E\A} g dμ
                 ≤ ν(E∩A) + ν(E\A) = ν(E)

**引理3**：存在 f* ∈ 𝓕 使得 ∫ f* dμ = sup_{f ∈ 𝓕} ∫ f dμ。

**证明**：取一列 f_n ∈ 𝓕 使得 ∫ f_n → M。
令 g_n = max(f_1, ..., f_n)，则 g_n ↑ 且 ∫ g_n → M。
令 f* = lim g_n，由单调收敛定理 ∫ f* = M。

**关键引理4**：对于这个 f*，有 ν(E) = ∫_E f* dμ 对所有 E 成立。

**证明**：反证法。若存在 E₀ 使得 ν(E₀) > ∫_{E₀} f* dμ，
令 ε > 0 足够小使得 ν(E₀) ≥ ∫_{E₀} f* dμ + ε·μ(E₀)。
定义 g = f* + ε·1_{E₀}，则 g ∈ 𝓕 但 ∫ g dμ > M，矛盾。

这个证明展示了分析学中经典的"极值原理"。
-/

end ProofTechniques

/-
## 历史注记

Radon-Nikodym 定理的历史发展：

1. **Lebesgue (1902)**: 建立了现代测度和积分理论

2. **Radon (1913)**: 在 ℝⁿ 上证明了该定理，
   将Lebesgue分解推广到带符号测度

3. **Nikodym (1930)**: 在一般抽象测度空间上证明了定理

4. **Von Neumann (1940)**: 给出了基于Hilbert空间方法的优雅证明

5. **现代发展**: 
   - 向量值测度的Radon-Nikodym性质
   - 非交换几何中的推广
   - 在随机分析中的应用（Girsanov定理等）
-/

end RadonNikodym
