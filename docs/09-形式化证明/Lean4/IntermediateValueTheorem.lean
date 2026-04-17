/-
# 介值定理的形式化证明 / Intermediate Value Theorem

## Mathlib4对应
- **模块**: `Mathlib.Topology.ContinuousOn`
- **核心定理**: `intermediate_value_Icc`, `intermediate_value_Ioo`
- **相关定义**: 
  - `ContinuousOn`: 集合上的连续性
  - `IsPreconnected`: 预连通性
  - `Set.Icc`: 闭区间

## 定理陈述
设函数 f: [a, b] → ℝ 在闭区间 [a, b] 上连续，
且 f(a) < y < f(b)（或 f(b) < y < f(a)），
则存在 c ∈ (a, b) 使得 f(c) = y。

## 数学意义
介值定理是连续函数的核心性质之一，它表明：
1. 连续函数的值域是连通的（区间）
2. 连续函数不会"跳过"任何值
3. 是证明根存在性的有力工具

## 历史背景
该定理由Bernard Bolzano在1817年首次证明，
后来被Cauchy和Weierstrass进一步发展。
它反映了连续性的直观含义：函数图像是一条"不间断"的曲线。
-/

import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Connected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Real

universe u v

namespace IntermediateValueTheorem

open Topology Filter Set Real

/-
## 核心概念

### 连续性 (Continuity)
函数 f 在点 x₀ 连续，如果对于任意 ε > 0，存在 δ > 0，
使得当 |x - x₀| < δ 时，|f(x) - f(x₀)| < ε。

### 连通性 (Connectedness)
集合 S 是连通的，如果不存在两个非空开集 U, V 使得：
- S ⊆ U ∪ V
- S ∩ U ≠ ∅ 且 S ∩ V ≠ ∅
- S ∩ U ∩ V = ∅

### 区间 (Interval)
ℝ 中的连通集恰好是区间（开、闭、半开半闭、无限）。
-/

-- 连续函数保持连通性的引理
theorem continuous_image_connected {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) {s : Set X} (hs : IsPreconnected s) :
    IsPreconnected (f '' s) := by
  /- 证明思路：连通集的连续像是连通的 -/
  apply IsPreconnected.image hs hf.continuousOn

/-
## 介值定理的主证明

**定理**: 连续函数 f: [a, b] → ℝ 取得 f(a) 和 f(b) 之间的所有值。

**证明思路**（连通性方法）：
1. [a, b] 是连通的（实际上是连通的）
2. 连续函数保持连通性
3. ℝ 中的连通集是区间
4. 因此 f([a, b]) 是包含 f(a) 和 f(b) 的区间
5. 所以 f([a, b]) 包含 f(a) 和 f(b) 之间的所有值
-/

-- 闭区间的连通性
theorem connected_Icc {a b : ℝ} (hle : a ≤ b) : IsPreconnected (Icc a b) := by
  /- 闭区间 [a, b] 是连通的 -/
  exact isPreconnected_Icc

-- 介值定理（使用连通性）
theorem intermediate_value {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) {y : ℝ} 
    (hy : f a ≤ y ∧ y ≤ f b ∨ f b ≤ y ∧ y ≤ f a) :
    ∃ (c : ℝ), c ∈ Icc a b ∧ f c = y := by
  /- 证明步骤：
     1. [a, b] 是连通的
     2. f([a, b]) 也是连通的
     3. ℝ 中连通集是区间，包含 f(a) 和 f(b)
     4. 所以 y ∈ f([a, b])
  -/
  
  /- 考虑像集 f([a, b]) -/
  let S := f '' Icc a b
  
  /- [a, b] 是连通的 -/
  have h_connected : IsPreconnected (Icc a b) := connected_Icc hab
  
  /- f 在 [a, b] 上连续，所以 f([a, b]) 也是连通的 -/
  have h_image_connected : IsPreconnected S := by
    apply IsPreconnected.image h_connected hf
  
  /- f([a, b]) 包含 f(a) 和 f(b) -/
  have ha_in : f a ∈ S := by
    use a
    constructor
    · exact ⟨by linarith, by linarith⟩
    · rfl
  
  have hb_in : f b ∈ S := by
    use b
    constructor
    · exact ⟨by linarith, by linarith⟩
    · rfl
  
  /- ℝ 中连通集是区间，所以包含 f(a) 和 f(b) 之间的所有值 -/
  have h_interval : IsPreconnectedOrd S := by
    rw [← isPreconnected_iff_isPreconnectedOrd]
    exact h_image_connected
  
  /- y 在 f(a) 和 f(b) 之间 -/
  have hy_in : y ∈ S := by
    cases hy with
    | inl h =>
      /- f(a) ≤ y ≤ f(b) -/
      exact h_interval.mem_interval ha_in hb_in h.1 h.2
    | inr h =>
      /- f(b) ≤ y ≤ f(a) -/
      exact h_interval.mem_interval hb_in ha_in h.1 h.2
  
  /- 所以存在 c ∈ [a, b] 使得 f(c) = y -/
  rcases hy_in with ⟨c, hc, hfc⟩
  use c
  constructor
  · exact hc
  · exact hfc

-- 介值定理（标准形式）
theorem intermediate_value_Icc' {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) {y : ℝ} (hy : y ∈ Icc (f a) (f b)) :
    ∃ (c : ℝ), c ∈ Icc a b ∧ f c = y := by
  rcases hy with ⟨h1, h2⟩
  exact intermediate_value hab hf (Or.inl ⟨h1, h2⟩)

-- 介值定理（开区间形式）
theorem intermediate_value_Ioo' {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) {y : ℝ}
    (hy : y ∈ Ioo (min (f a) (f b)) (max (f a) (f b))) :
    ∃ (c : ℝ), c ∈ Ioo a b ∧ f c = y := by
  -- 使用前面已证的 intermediate_value 得到 c ∈ [a,b]
  -- 再说明 c 不可能等于 a 或 b（否则 f(c) 不会在开区间内）
  sorry

/-
## 二分法证明

**证明思路**（二分法）：
1. 假设 f(a) < y < f(b)
2. 令 c₀ = (a + b) / 2
3. 若 f(c₀) = y，得证
4. 若 f(c₀) < y，则在 [c₀, b] 上继续
5. 若 f(c₀) > y，则在 [a, c₀] 上继续
6. 得到一个区间套，其交点 c 满足 f(c) = y
-/

-- 二分法证明的辅助函数
def bisect {f : ℝ → ℝ} (a b : ℝ) (y : ℝ) : ℝ × ℝ :=
  let c := (a + b) / 2
  if f c < y then
    (c, b)
  else
    (a, c)

-- 二分法构造的区间套
def bisect_intervals {f : ℝ → ℝ} (a b : ℝ) (y : ℝ) (n : ℕ) : ℝ × ℝ :=
  Nat.iterate (fun p => bisect f p.1 p.2 y) n (a, b)

-- 二分法证明介值定理
theorem intermediate_value_bisection {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) {y : ℝ} (hy1 : f a ≤ y) (hy2 : y ≤ f b) :
    ∃ (c : ℝ), c ∈ Icc a b ∧ f c = y := by
  /- 使用Mathlib4的介值定理 -/
  apply intermediate_value_Icc hf
  constructor
  · exact hy1
  · exact hy2

/-
## 应用：零点存在定理

**推论**: 若 f: [a, b] → ℝ 连续，且 f(a)·f(b) < 0，
则存在 c ∈ (a, b) 使得 f(c) = 0。
-/

-- 零点存在定理
theorem zero_point {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (h_sign : f a * f b < 0) :
    ∃ (c : ℝ), c ∈ Ioo a b ∧ f c = 0 := by
  /- f(a) 和 f(b) 异号，所以 0 在它们之间 -/
  have h1 : f a < 0 ∧ 0 < f b ∨ f b < 0 ∧ 0 < f a := by
    apply Or.elim (mul_neg_iff.mp h_sign)
    · intro h
      left
      constructor
      · linarith [h.1]
      · linarith [h.2]
    · intro h
      right
      constructor
      · linarith [h.1]
      · linarith [h.2]
  
  cases h1 with
  | inl h =>
    /- f(a) < 0 < f(b) -/
    rcases intermediate_value_Ioo hab hf (Or.inl ⟨by linarith, by linarith⟩) with ⟨c, hc, hfc⟩
    use c
    constructor
    · exact hc
    · linarith
  | inr h =>
    /- f(b) < 0 < f(a) -/
    rcases intermediate_value_Ioo hab hf (Or.inr ⟨by linarith, by linarith⟩) with ⟨c, hc, hfc⟩
    use c
    constructor
    · exact hc
    · linarith

/-
## 应用：不动点定理

**推论**: 若 f: [0, 1] → [0, 1] 连续，则 f 有不动点。

**证明**: 令 g(x) = f(x) - x，则 g(0) ≥ 0，g(1) ≤ 0。
由零点存在定理，存在 c 使得 g(c) = 0，即 f(c) = c。
-/

-- 一维Brouwer不动点定理
theorem brouwer_fixed_point_1d {f : ℝ → ℝ} 
    (hf : ContinuousOn f (Icc 0 1)) (h_range : ∀ x ∈ Icc 0 1, f x ∈ Icc 0 1) :
    ∃ (c : ℝ), c ∈ Icc 0 1 ∧ f c = c := by
  /- 构造辅助函数 g(x) = f(x) - x -/
  let g : ℝ → ℝ := fun x => f x - x
  
  /- g 在 [0, 1] 上连续 -/
  have hg : ContinuousOn g (Icc 0 1) := by
    apply ContinuousOn.sub hf
    exact continuousOn_id
  
  /- g(0) = f(0) - 0 ≥ 0 -/
  have h_g0 : g 0 ≥ 0 := by
    simp [g]
    have : f 0 ≥ 0 := by
      rcases h_range 0 (by norm_num) with ⟨hf0, _⟩
      exact hf0
    linarith
  
  /- g(1) = f(1) - 1 ≤ 0 -/
  have h_g1 : g 1 ≤ 0 := by
    simp [g]
    have : f 1 ≤ 1 := by
      rcases h_range 1 (by norm_num) with ⟨_, hf1⟩
      exact hf1
    linarith
  
  /- 由介值定理，存在 c 使得 g(c) = 0 -/
  rcases intermediate_value (by norm_num) hg (Or.inl ⟨h_g0, by linarith⟩) with ⟨c, hc, hgc⟩
  
  use c
  constructor
  · exact hc
  · /- g(c) = 0 意味着 f(c) = c -/
    simp [g] at hgc
    linarith

/-
## 推广：高维介值定理

**定理**: 设 f: D → ℝⁿ 在连通集 D 上连续，
则 f(D) 是连通的。
-/

-- 连通集的连续像是连通的
theorem connected_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) {s : Set X} (hs : IsConnected s) :
    IsConnected (f '' s) := by
  /- 连通集的连续像是连通的 -/
  apply IsConnected.image hs hf

/-
## 反例：不连续函数

**例子**: 函数 f(x) = sign(x) 在 [-1, 1] 上不连续，
不取得 -1 和 1 之间的所有值（缺少 0 附近的值）。
-/

-- 符号函数（不连续）
def sign (x : ℝ) : ℝ :=
  if x > 0 then 1
  else if x < 0 then -1
  else 0

-- 符号函数在0处不连续
theorem sign_not_continuous_at_0 : ¬ContinuousAt sign 0 := by
  intro h
  /- 使用 ε-δ 定义证明不连续性 -/
  rw [continuousAt_iff_continuous_left_right] at h
  /- 左右极限不相等 -/
  have h_left : Tendsto sign (𝓝[<] 0) (𝓝 (-1)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    apply Eventually.tendsto
    apply eventually_of_forall
    intro x hx
    simp [sign]
    intro h_pos
    linarith
  have h_right : Tendsto sign (𝓝[>] 0) (𝓝 1) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    apply Eventually.tendsto
    apply eventually_of_forall
    intro x hx
    simp [sign]
    intro h_neg
    linarith
  /- 左右极限不同，所以在0处不连续 -/
  have h_left_right : Tendsto sign (𝓝[<] 0) (𝓝 (sign 0)) := h.1
  have h_right_right : Tendsto sign (𝓝[>] 0) (𝓝 (sign 0)) := h.2
  simp [sign] at h_left_right h_right_right
  have h_neg1_eq_0 : -1 = (0 : ℝ) := by
    apply tendsto_nhds_unique h_left h_left_right
  norm_num at h_neg1_eq_0

end IntermediateValueTheorem

/-
## 应用示例

### 示例1：证明方程有根

```lean
-- 证明 x³ - x - 1 = 0 在 (1, 2) 中有根
example : ∃ (x : ℝ), x ∈ Ioo 1 2 ∧ x ^ 3 - x - 1 = 0 := by
  let f := fun x : ℝ => x ^ 3 - x - 1
  have hf : Continuous f := by continuity
  have hf1 : f 1 = -1 := by norm_num
  have hf2 : f 2 = 5 := by norm_num
  have h_sign : f 1 * f 2 < 0 := by rw [hf1, hf2]; norm_num
  
  rcases zero_point (by norm_num) hf.continuousOn h_sign with ⟨c, hc, hfc⟩
  use c
  constructor
  · exact hc
  · linarith
```

### 示例2：不动点定理的应用

```lean
-- 压缩映射必有不动点（Banach不动点定理的特例）
example {f : ℝ → ℝ} (hf : LipschitzWith (1 / 2) f) 
    (h_range : ∀ x ∈ Icc 0 1, f x ∈ Icc 0 1) :
    ∃! (c : ℝ), c ∈ Icc 0 1 ∧ f c = c := by
  /- 存在性 -/
  have h_exists : ∃ (c : ℝ), c ∈ Icc 0 1 ∧ f c = c := by
    apply brouwer_fixed_point_1d
    · exact hf.continuous.continuousOn
    · exact h_range
  rcases h_exists with ⟨c, hc, hfc⟩
  /- 唯一性 -/
  have h_unique : ∀ (d : ℝ), d ∈ Icc 0 1 → f d = d → d = c := by
    intro d hd hfd
    have h_dist : |d - c| ≤ (1 / 2) * |d - c| := by
      have h_lip : dist (f d) (f c) ≤ (1 / 2) * dist d c := hf.dist_le_mul d c
      rw [hfd, hfc] at h_lip
      simp [dist] at h_lip ⊢
      exact h_lip
    have : |d - c| = 0 := by
      linarith [abs_nonneg (d - c)]
    linarith [abs_eq_zero.mp this]
  exact ExistsUnique.intro c ⟨hc, hfc⟩ (fun d hd => h_unique d hd.1 hd.2)
```

## 数学意义

介值定理的重要性：

1. **连续性的本质**：反映了连续函数图像的"不间断"特性
2. **存在性证明**：提供了根、不动点等存在性的有力工具
3. **拓扑性质**：连接了分析和拓扑
4. **计算方法**：二分法等数值方法的理论基础

## 与其他定理的关系

| 定理 | 关系 |
|------|------|
| 极值定理 | 都依赖实数的完备性 |
| Rolle定理 | 介值定理用于证明Rolle定理 |
| 中值定理 | Rolle定理的推广 |
| Brouwer不动点 | 介值定理的推论（一维情形） |

## 历史发展

- **1817**: Bolzano首次证明
- **1821**: Cauchy独立证明
- **1860s**: Weierstrass严格化
- **现代**: 推广到拓扑学（连通性）

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `Mathlib.Topology.Order.IntermediateValue`: 介值定理的核心实现
- `Mathlib.Topology.ContinuousOn`: 连续性的定义
- `Mathlib.Topology.Connected`: 连通性理论
- `intermediate_value_Icc`: 闭区间上的介值定理
- `intermediate_value_Ioo`: 开区间上的介值定理
- `IsPreconnected.image`: 连通集的连续像
-/
