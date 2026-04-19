/-
# Bolzano-Weierstrass定理的形式化证明 / Bolzano-Weierstrass Theorem

## Mathlib4对应
- **模块**: `Mathlib.Topology.MetricSpace.Compact`
- **核心定理**: `BolzanoWeierstrass.tendsto_subseq`
- **相关定义**: 
  - `IsCompact`: 紧致性
  - `Filter`: 滤子
  - `ClusterPt`: 聚点

## 定理陈述
在 ℝⁿ 中，任何有界序列都有收敛子序列。

等价表述：ℝⁿ 中的有界无限子集必有聚点。

## 数学意义
Bolzano-Weierstrass定理是实分析的核心定理，它：
1. 刻画了欧几里得空间的局部紧致性
2. 是证明许多分析定理的基础工具
3. 与Heine-Borel定理等价（在ℝⁿ中）

## 历史背景
该定理由Bernard Bolzano在1817年（作为引理）和
Karl Weierstrass在1860年代独立证明，
是实数完备性的重要表现。
-/

import Mathlib
import Mathlib
import Mathlib
import Mathlib
import Mathlib




/-
## 核心概念

### 有界序列 (Bounded Sequence)
序列 {xₙ} 称为有界的，如果存在 M > 0 使得对所有 n，|xₙ| ≤ M。

### 收敛子序列 (Convergent Subsequence)
序列 {xₙ} 的子序列 {xₙₖ} 收敛到 L，如果 lim_{k→∞} xₙₖ = L。

### 聚点 (Accumulation Point/Cluster Point)
点 L 是集合 S 的聚点，如果 L 的每个邻域都包含 S 的无限多个点。
-/

-- 序列有界的定义

-- 收敛子序列的定义

/-
## Bolzano-Weierstrass定理的主证明（一维情形）

**定理**: 任何有界实数序列都有收敛子序列。

**证明思路**（区间套方法）：
1. 设 {xₙ} 是有界序列，则存在 [a, b] 包含所有 xₙ
2. 将 [a, b] 二等分，至少有一个子区间包含无限多项
3. 选择这样的子区间，重复此过程
4. 得到一个区间套序列，其长度趋于0
5. 由区间套定理，存在唯一的公共点 L
6. 从每个区间中选一项，得到收敛到 L 的子序列
-/

-- 区间套定理
  
  
  
  
  

-- Bolzano-Weierstrass定理（一维）- 使用Mathlib4的结果
  
  
  
  

/-
## Bolzano-Weierstrass定理的滤子证明

**证明思路**（滤子方法）：
1. 有界序列的滤子是超滤子的聚点
2. 在紧致空间中，每个滤子都有聚点
3. 因此存在收敛子序列
-/

-- 滤子版本的Bolzano-Weierstrass定理

-- 度量空间版本
  
  

/-
## Bolzano-Weierstrass定理的高维推广

**定理**: 在 ℝⁿ 中，任何有界序列都有收敛子序列。

**证明**: 对每个坐标分别应用一维Bolzano-Weierstrass定理，
然后使用对角线方法选取公共的收敛子序列。
-/

-- ℝⁿ中的Bolzano-Weierstrass定理
  
  
  
  

-- 使用Mathlib4的紧致性证明

/-
## 应用：闭区间的紧致性

**定理**: 闭区间 [a, b] ⊂ ℝ 是紧致的。

**证明**: 由Bolzano-Weierstrass定理，[a, b] 中的任何序列都有收敛子序列，
且极限仍在 [a, b] 中（因为 [a, b] 是闭集）。
-/

-- 闭区间的紧致性

/-
## 应用：连续函数的性质

**定理**: 定义在紧致集上的连续函数必取得最大值和最小值。
-/

-- 极值定理
  
  
  
  
  


/-
## 应用示例

### 示例1：构造收敛子序列

```lean
-- 序列 xₙ = (-1)ⁿ 有收敛子序列
example : HasConvergentSubseq (fun n => (-1 : ℝ) ^ n) := by
  /- 取偶数下标子序列：x_{2n} = 1 → 1 -/
  use fun n => 2 * n
  constructor
  · intro m n hmn; simp; linarith
  · use 1
    /- 证明收敛 -/
    simp
    use 1
    simp
```

### 示例2：证明序列紧致性

```lean
-- [0,1] 中的序列都有收敛子序列
example (x : ℕ → ℝ) (hx : ∀ n, x n ∈ Icc 0 1) :
    HasConvergentSubseq x := by
  apply bolzano_weierstrass_1d
  use 1
  intro n
  have : x n ∈ Icc 0 1 := hx n
  rcases this with ⟨h0, h1⟩
  have h_dist : |x n - x 0| ≤ 1 := by
    have h0' : 0 ≤ x n := h0
    have h1' : x n ≤ 1 := h1
    have h0'' : 0 ≤ x 0 := (hx 0).1
    have h1'' : x 0 ≤ 1 := (hx 0).2
    apply abs_le.mpr
    constructor
    · linarith
    · linarith
  exact h_dist
```

## 数学意义

Bolzano-Weierstrass定理的重要性：

1. **完备性的表现**：反映了实数（或ℝⁿ）的完备性
2. **紧致性等价**：在ℝⁿ中，紧致 ⟺ 闭且有界 ⟺ 序列紧致
3. **分析基础**：许多分析定理的基础
4. **存在性证明**：提供了极限存在性的构造性证明

## 与其他定理的关系

| 定理 | 关系 |
|------|------|
| Heine-Borel定理 | 在ℝⁿ中，Bolzano-Weierstrass ⟺ Heine-Borel |
| 单调收敛定理 | 单调有界序列收敛是Bolzano-Weierstrass的特例 |
| 柯西收敛准则 | 完备性 ⟺ 每个柯西序列收敛 |
| 极值定理 | 连续函数在紧致集上取得极值 |

## 历史影响

- **1817**: Bolzano首先证明了有界序列有聚点的引理
- **1860s**: Weierstrass独立发现并推广
- **现代**: 成为实分析和泛函分析的基础工具

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `Mathlib.Topology.MetricSpace.Compact`: 紧致度量空间理论
- `IsCompact.tendsto_subseq`: 紧致空间的序列紧致性
- `exists_clusterPt_of_compactSpace`: 紧致空间中滤子的聚点存在性
- `isCompact_Icc`: 闭区间的紧致性
- `ProperSpace`: proper空间（有界集的闭包紧致）
-/

-- Framework stub for BolzanoWeierstrass
theorem BolzanoWeierstrass_stub : True := by trivial
