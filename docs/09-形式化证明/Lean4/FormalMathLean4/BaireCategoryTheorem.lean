import Mathlib
/-
# Baire 纲定理的形式化证明 / Baire Category Theorem

## 定理信息
- **定理名称**: Baire 纲定理
- **数学领域**: 拓扑学 / 泛函分析
- **MSC2020编码**: 54E52, 46A30
- **难度级别**: P2

## 定理陈述
1. **完备度量空间版本**: 完备度量空间中可数个稠密开集的交仍然是稠密的。
2. **局部紧 Hausdorff 空间版本**: 局部紧正则空间中可数个稠密开集的交仍然是稠密的。

等价表述（Baire 空间定义）: 上述两类空间都是 Baire 空间。

## 数学意义
Baire 纲定理是拓扑学和泛函分析的核心工具：
1. 证明一致有界原理（Banach-Steinhaus 定理）
2. 证明开映射定理和闭图像定理
3. 构造无处稠密集的典型例子（如 Cantor 集）
4. 证明连续函数的不可微点集是剩余集

## 历史背景
- 1899: René-Louis Baire 在他的博士论文中引入并证明了该定理
- 后来成为泛函分析三大定理的基础工具
-/

/-
## 核心概念

### Baire 空间
拓扑空间 X 称为 Baire 空间，如果可数个稠密开集的交仍然是稠密的。

### 无处稠密集 (Nowhere Dense)
集合 A 称为无处稠密的，如果其闭包的内部为空。

### 第一纲集 / 第二纲集 (Meager / Comeager)
- 第一纲集（贫集）：可数个无处稠密集的并
- 第二纲集（剩余集）：包含一个稠密 Gδ 集
-/

/-
## Baire 纲定理的证明思路

**完备度量空间版本**:
1. 设 {U_n} 是一列稠密开集，需要证明 ⋂ U_n 稠密。
2. 等价于证明对任意非空开集 W，W ∩ (⋂ U_n) ≠ ∅。
3. 构造收缩球套：B₁ ⊆ W ∩ U₁, B₂ ⊆ B₁ ∩ U₂, ...
4. 利用完备性，球套交集非空，且包含于 W ∩ (⋂ U_n)。

**局部紧版本**:
1. 类似构造，但使用紧集套代替闭球套。
2. 利用有限交性质和局部紧性。
-/

/-
## 应用

### 一致有界原理
Banach 空间上点点有界的线性算子族是一致有界的。

### 连续函数的可微性
[0,1] 上连续函数中，在某点可微的函数构成第一纲集。
因此"大多数"连续函数处处不可微。

### 代数维数
无穷维 Banach 空间作为向量空间，其 Hamel 基是不可数的。
-/

## 与其他定理的关系

| 定理 | 关系 |
|------|------|
| 一致有界原理 | 直接应用 |
| 开映射定理 | 直接应用 |
| 闭图像定理 | 开映射定理的推论 |
| Cantor 交集定理 | 类似证明技术 |

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `Mathlib.Topology.Baire.Lemmas`: Baire 空间的基本引理
- `Mathlib.Topology.Baire.CompleteMetrizable`: 完备可度量化空间是 Baire 空间
- `Mathlib.Topology.Baire.LocallyCompactRegular`: 局部紧正则空间是 Baire 空间
- `dense_iInter_of_isOpen_nat`: 核心定理（可数稠密开交仍稠密）
-/

/-
========================================
 Mathlib4 实质化引用 / Materialized References
========================================
本文件已升级为引用 Mathlib4 中的实际定理和定义。
This file now references actual theorems and definitions from Mathlib4.
-
- 模块 / Module: `Mathlib.Topology.Baire.Lemmas`
- 模块 / Module: `Mathlib.Topology.Baire.CompleteMetrizable`
- 定理 / Theorem: `dense_iInter_of_isOpen_nat`
-/

#check dense_iInter_of_isOpen_nat

-- Baire Category Theorem: a countable intersection of dense open sets is dense in a Baire space
-- Baire 纲定理：Baire 空间中可数个稠密开集的交仍然是稠密的。
-- Mathlib4 已在 `Mathlib.Topology.Baire` 系列模块中完整证明。
variable {X : Type*} [TopologicalSpace X] [BaireSpace X]

-- 核心形式：可数个稠密开集的交是稠密的
theorem BaireCategoryTheorem {f : ℕ → Set X} (ho : ∀ n, IsOpen (f n))
    (hd : ∀ n, Dense (f n)) : Dense (⋂ n, f n) := by
  exact dense_iInter_of_isOpen_nat ho hd
