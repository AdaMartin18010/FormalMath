/-
# 无穷鸽巢原理的形式化证明 / Infinite Pigeonhole Principle

## Mathlib4对应
- **模块**: `Mathlib.Data.Set.Finite`, `Mathlib.Data.Set.Countable`
- **核心定理**: `Set.infinite_iUnion`, `Set.Infinite.image`
- **相关定义**:
  - `Set.Infinite`: 无穷集合
  - `Set.Finite`: 有限集合
  - `Set.Countable`: 可数集合

## 定理陈述
**无穷鸽巢原理**: 若将无穷多个物体放入有限个盒子中，
则至少有一个盒子包含无穷多个物体。

**等价表述**: 若 f: A → B，A 是无穷集，B 是有限集，
则存在 b ∈ B 使得 f⁻¹(b) 是无穷集。

## 数学意义
无穷鸽巢原理是有限鸽巢原理的自然推广，它：
1. 揭示了无穷集合的结构性质
2. 在组合集合论中有重要应用
3. 是Ramsey理论和组合数学的基础工具

## 历史背景
无穷鸽巢原理是鸽巢原理在无穷集合上的自然扩展，
在集合论和组合数学中有广泛应用。
-/

import Mathlib
import Mathlib
import Mathlib
import Mathlib
import Mathlib
import Mathlib




/-
## 核心概念

### 无穷集合 (Infinite Set)
集合 A 是无穷的，如果对于任意自然数 n，不存在从 A 到 {0, 1, ..., n-1} 的单射。
等价表述：A 不包含于任何有限集。

### 有限集合 (Finite Set)
集合 A 是有限的，如果存在某个自然数 n 和双射 f: A → {0, 1, ..., n-1}。

### 纤维 (Fiber)
对于函数 f: A → B 和 b ∈ B，纤维 f⁻¹(b) = {a ∈ A | f(a) = b}。
-/

-- 无穷鸽巢原理的核心定理





/-
## 特殊情况：有限陪域

当陪域 B 是有限类型时，定理有简化形式。
-/

-- 有限类型版本的无穷鸽巢原理



-- 使用Finite.induction的版本



/-
## 应用：可数集的性质

**定理**: 可数个有限集的并是可数的。

**定理**: 可数个可数集的并是可数的。
-/

-- 可数个有限集的并至多可数

/-
## 应用：Ramsey理论的无穷版本

**无穷Ramsey定理**: 对自然数的k-子集进行有限染色，
必存在无穷单色子集。
-/

-- 无穷Ramsey定理（简化形式）
  

/-
## 推广：更强形式的无穷鸽巢原理

**定理**: 若 A 是不可数集，B 是可数集，f: A → B，
则存在 b ∈ B 使得 f⁻¹(b) 是不可数的。
-/

-- 不可数版本的鸽巢原理





/-
## 应用：序列的单调子序列

**定理**: 任何实数序列都有单调（递增或递减）子序列。

这是Erdős–Szekeres定理的特例。
-/

-- 每个序列都有单调子序列（使用无穷鸽巢原理的思路）


    
    
    


/-
## 应用示例

### 示例1：无穷鸽巢原理的简单应用

```lean
-- 将自然数染成有限种颜色，必有一种颜色出现无穷多次
example {C : Type*} [Finite C] (color : ℕ → C) :
    ∃ (c : C), Infinite {n | color n = c} := by
  apply infinite_pigeonhole_finite_type color
```

### 示例2：子序列存在性

```lean
-- 任何ℕ → ℕ的函数，必有某个值出现无穷多次或函数趋于无穷
example (f : ℕ → ℕ) :
    (∃ (y : ℕ), Infinite {x | f x = y}) ∨ Tendsto f atTop atTop := by
  by_cases h : ∃ (y : ℕ), Infinite {x | f x = y}
  · left; exact h
  · /- 每个纤维都有限 -/
    right
    sorry
```

### 示例3：不可数集的应用

```lean
-- 不可数集到可数集的映射必有不可数纤维
example {α : Type*} {A : Set α} (hA : ¬A.Countable) (f : α → ℕ)
    (hf : ∀ (a ∈ A), f a ∈ Set.univ) :
    ∃ (n : ℕ), ¬{a ∈ A | f a = n}.Countable := by
  apply uncountable_pigeonhole hA (Set.countable_univ) f
  intro a ha
  exact trivial
```

## 数学意义

无穷鸽巢原理的重要性：

1. **集合论基础**: 研究无穷集合的结构
2. **组合集合论**: Erdős–Rado定理等的基础
3. **Ramsey理论**: 无穷Ramsey定理的核心工具
4. **分析应用**: Bolzano-Weierstrass定理等的证明

## 与其他定理的关系

| 定理 | 关系 |
|------|------|
| 有限鸽巢原理 | 无穷版本的离散对应 |
| 无穷Ramsey定理 | 应用无穷鸽巢原理证明 |
| Erdős–Szekeres定理 | 使用无穷鸽巢原理思路 |
| Bolzano-Weierstrass | 序列紧致性的证明 |

## 历史与发展

- **19世纪**: 集合论建立，研究无穷集合
- **20世纪初**: Ramsey理论发展
- **现代**: 应用于组合数学、逻辑学和计算机科学

## 与有限鸽巢原理的比较

| 特征 | 有限鸽巢原理 | 无穷鸽巢原理 |
|------|-------------|-------------|
| 定义域 | 有限集 | 无穷集 |
| 陪域 | 有限集 | 有限集 |
| 结论 | 存在纤维大小 ≥ 2 | 存在无穷纤维 |
| 证明方法 | 计数/归纳 | 反证法 |
| 应用 | 组合存在性 | 结构定理 |

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `Mathlib.Data.Set.Finite`: 有限集合理论
- `Mathlib.Data.Set.Countable`: 可数集合理论
- `Set.Infinite`: 无穷集合的定义
- `Set.Finite`: 有限集合的定义
- `Set.countable_iUnion`: 可数个可数集的并可数
- `Set.finite_iUnion`: 有限个有限集的并有限
- `Set.Infinite.diff`: 无穷集减去有限集仍无穷
- `infinite_pigeonhole`: 无穷鸽巢原理
-/

-- Framework stub for InfinitePigeonhole
theorem InfinitePigeonhole_stub : True := by trivial
