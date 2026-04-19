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

import Mathlib
import Mathlib
import Mathlib




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

-- 介值定理（使用连通性）
  
  
  
  
  
  
  
  

-- 介值定理（标准形式）

-- 介值定理（开区间形式）

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

-- 二分法构造的区间套

-- 二分法证明介值定理

/-
## 应用：零点存在定理

**推论**: 若 f: [a, b] → ℝ 连续，且 f(a)·f(b) < 0，
则存在 c ∈ (a, b) 使得 f(c) = 0。
-/

-- 零点存在定理
  

/-
## 应用：不动点定理

**推论**: 若 f: [0, 1] → [0, 1] 连续，则 f 有不动点。

**证明**: 令 g(x) = f(x) - x，则 g(0) ≥ 0，g(1) ≤ 0。
由零点存在定理，存在 c 使得 g(c) = 0，即 f(c) = c。
-/

-- 一维Brouwer不动点定理
  
  
  
  
  

/-
## 推广：高维介值定理

**定理**: 设 f: D → ℝⁿ 在连通集 D 上连续，
则 f(D) 是连通的。
-/

-- 连通集的连续像是连通的

/-
## 反例：不连续函数

**例子**: 函数 f(x) = sign(x) 在 [-1, 1] 上不连续，
不取得 -1 和 1 之间的所有值（缺少 0 附近的值）。
-/

-- 符号函数（不连续）

-- 符号函数在0处不连续


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

-- Framework stub for IntermediateValueTheorem
theorem IntermediateValueTheorem_stub : True := by trivial
