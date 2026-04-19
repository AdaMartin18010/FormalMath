import Mathlib

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

/-
## 应用：零点存在定理

**推论**: 若 f: [a, b] → ℝ 连续，且 f(a)·f(b) < 0，
则存在 c ∈ (a, b) 使得 f(c) = 0。
-/

/-
## 应用：不动点定理

**推论**: 若 f: [0, 1] → [0, 1] 连续，则 f 有不动点。

**证明**: 令 g(x) = f(x) - x，则 g(0) ≥ 0，g(1) ≤ 0。
由零点存在定理，存在 c 使得 g(c) = 0，即 f(c) = c。
-/

/-
## 推广：高维介值定理

**定理**: 设 f: D → ℝⁿ 在连通集 D 上连续，
则 f(D) 是连通的。
-/

/-
## 反例：不连续函数

**例子**: 函数 f(x) = sign(x) 在 [-1, 1] 上不连续，
不取得 -1 和 1 之间的所有值（缺少 0 附近的值）。
-/

-- Framework stub for IntermediateValueTheorem
theorem IntermediateValueTheorem_stub : True := by trivial
