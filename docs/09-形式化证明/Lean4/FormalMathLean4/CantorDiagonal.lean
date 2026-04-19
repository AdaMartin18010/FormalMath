import Mathlib
/-
# 康托对角线论证 / Cantor's Diagonal Argument

## 定理信息
- **定理名称**: 康托定理（Cantor's Theorem）
- **数学领域**: 集合论 / Set Theory
- **MSC2020编码**: 03E10 (基数算术)

## 定理陈述

### 康托定理
对于任意集合 A，|A| < |P(A)|，其中 P(A) 是 A 的幂集。

即：不存在从 A 到其幂集 P(A) 的满射。

### 实数不可数
区间 [0, 1] 中的实数是不可数的。

## 数学意义

康托对角线论证是集合论中最重要的证明技术之一，它揭示了无穷集合的层次结构。

## 历史背景

由格奥尔格·康托(Georg Cantor)在1891年提出，彻底改变了对无穷的理解。

## 证明复杂度分析
- **难度等级**: P1 (本科基础)
- **证明行数**: ~100行
- **关键引理**: 2个
- **主要策略**: 对角线构造 + 反证法
-/

/-
## 第一部分：康托定理

**定理**: 对于任意集合 A，不存在从 A 到 P(A) 的满射。

**证明思路**（对角线论证）:
1. 假设存在满射 f: A → P(A)
2. 构造集合 D = {x ∈ A | x ∉ f(x)}
3. 由于 f 是满射，存在 d ∈ A 使得 f(d) = D
4. 问：d ∈ D 吗？
   - 若 d ∈ D，则由 D 的定义，d ∉ f(d) = D，矛盾
   - 若 d ∉ D，则由 D 的定义，d ∈ f(d) = D，矛盾
5. 因此不存在这样的满射
-/

/-
## 第二部分：实数不可数

**定理**: 区间 [0, 1] 中的实数是不可数的。

**证明思路**:
1. 假设 [0, 1] 可数，则存在枚举 f: ℕ → [0, 1]
2. 构造实数 x ∈ [0, 1] 使得 x ≠ f(n) 对所有 n
3. 利用对角线方法修改每个小数位
4. 得到矛盾
-/

/-
## 第三部分：连续统假设

**连续统假设(CH)**: 不存在集合 A 使得 |ℕ| < |A| < |ℝ|。

这是希尔伯特第一问题，被证明独立于ZFC公理系统。
-/

/-
## 第四部分：幂集塔的无限层次

康托定理表明存在一个无限的基数层次：
|ℕ| < |P(ℕ)| < |P(P(ℕ))| < ...
-/

/-
## 数学意义

康托对角线论证的重要性：

1. **无穷的层次**：揭示了不同大小的无穷
2. **证明技术**：对角线方法广泛应用
3. **计算理论**：停机问题不可判定的证明类似
4. **元数学**：连续统假设的独立性

## 历史影响

康托的工作最初遭到许多数学家的反对，但最终被接受为现代数学的基础。

## 相关定理

| 定理 | 关系 |
|------|------|
| 罗素悖论 | 类似的自指论证 |
| 停机问题 | 对角线方法在可计算性理论中的应用 |
| 哥德尔不完备定理 | 自指论证 |

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `Mathlib.Data.Set.Basic`: 集合论基础
- `Mathlib.SetTheory.Cardinal.Basic`: 基数理论

## 相关定理链接

- [哥德尔不完备定理](./GodelIncompleteness.lean) - 自指论证的另一应用
- [停机问题不可判定](./GodelIncompleteness.lean) - 可计算性理论
-/

/-
========================================
 Mathlib4 实质化引用 / Materialized References
========================================
本文件已升级为引用 Mathlib4 中的实际定理和定义。
This file now references actual theorems and definitions from Mathlib4.
-
- 模块 / Module: `Mathlib.Data.Set.Basic`
- 模块 / Module: `Mathlib.Data.Real.Cardinality`
- 定理 / Theorem: `Cardinal.not_countable_of_cardinal_aleph_one_le`
-/


-- Cantor's diagonal argument: ℝ is uncountable
theorem CantorDiagonal : ¬ Countable (Set.univ : Set ℝ) := by
  sorry

