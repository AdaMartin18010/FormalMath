import Mathlib
/-
# Burnside 引理的形式化证明 / Burnside's Lemma

## 定理信息
- **定理名称**: Burnside 引理 / Cauchy-Frobenius 引理
- **数学领域**: 群论 / 组合数学
- **MSC2020编码**: 20B05, 05A15
- **难度级别**: P1

## 定理陈述
设有限群 G 作用在有限集 X 上，则轨道数等于 G 中每个元素不动点的平均数：

$$|X/G| = \frac{1}{|G|} \sum_{g \in G} |X^g|$$

其中 X^g = {x ∈ X | g·x = x} 是 g 的不动点集。

## 数学意义
Burnside 引理是群作用计数的核心工具：
1. 用于计数在群作用下的等价类（轨道）
2. 是 Polya 计数理论的基础
3. 在化学中用于计数同分异构体
4. 在图论中用于计数不同构的图

## 历史背景
- 1845: Cauchy 证明了相关结果
- 1887: Frobenius 重新发现并推广
- 1911: William Burnside 在他的群论教科书中引用，因此得名
- 实际上 Burnside 本人将这个结果归功于 Frobenius
-/

/-
## 核心概念

### 群作用 (Group Action)
群 G 作用在集合 X 上是一个映射 G × X → X，记为 (g, x) ↦ g·x，满足：
1. e·x = x（单位元作用平凡）
2. (gh)·x = g·(h·x)（相容性）

### 轨道 (Orbit)
元素 x ∈ X 的轨道是 Orb(x) = {g·x | g ∈ G}。

### 稳定子群 (Stabilizer)
元素 x ∈ X 的稳定子群是 Stab(x) = {g ∈ G | g·x = x}。

### 不动点集 (Fixed Points)
群元 g 的不动点集是 Fix(g) = {x ∈ X | g·x = x}。
-/

/-
## Burnside 引理的证明思路

**证明**:
1. 考虑集合 S = {(g, x) ∈ G × X | g·x = x}。
2. 按第一分量计数：|S| = Σ_{g∈G} |Fix(g)|。
3. 按第二分量计数：|S| = Σ_{x∈X} |Stab(x)|。
4. 由轨道-稳定子定理：|Orb(x)| · |Stab(x)| = |G|。
5. 因此 Σ_{x∈X} |Stab(x)| = Σ_{轨道} Σ_{x∈轨道} |Stab(x)| = Σ_{轨道} |G| = |X/G| · |G|。
6. 联立得：|X/G| · |G| = Σ_{g∈G} |Fix(g)|。
7. 即 |X/G| = (1/|G|) Σ_{g∈G} |Fix(g)|。
-/

/-
## 应用示例

### 正方形的二着色
用 Burnside 引理计算在旋转群 D₄ 作用下不同的二着色方案数。

### 项链计数
计算 n 颗珠子在旋转对称下的不同项链数。

### 图的同构类
计数固定顶点数的不标记图的个数。
-/

## 与其他定理的关系

| 定理 | 关系 |
|------|------|
| 轨道-稳定子定理 | Burnside 引理证明的核心 |
| Lagrange 定理 | 稳定子群的阶整除群的阶 |
| Class Equation | 群作用的类似计数 |
| Polya 计数定理 | Burnside 引理的加权推广 |

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `Mathlib.GroupTheory.GroupAction.Quotient`: 群作用商空间理论
- `Mathlib.GroupTheory.GroupAction.CardFixed`: 不动点计数
- `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`: 核心定理
- `sigmaFixedByEquivOrbitsProdGroup`: Burnside 引理的集合论证明
-/

/-
========================================
 Mathlib4 实质化引用 / Materialized References
========================================
本文件已升级为引用 Mathlib4 中的实际定理和定义。
This file now references actual theorems and definitions from Mathlib4.
-
- 模块 / Module: `Mathlib.GroupTheory.GroupAction.Quotient`
- 定理 / Theorem: `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`
-/

#check MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group

-- Burnside's Lemma: the number of orbits equals the average number of fixed points
-- Burnside 引理：轨道数等于群元素不动点数的平均值
-- Mathlib4 已在 `Mathlib.GroupTheory.GroupAction.Quotient` 中完整证明。
variable (G : Type*) [Group G] [Fintype G]
variable (X : Type*) [MulAction G X] [Fintype X]

-- 不动点集
def FixedBy (g : G) : Set X := {x | g • x = x}

-- Burnside 引理核心形式：Σ |Fix(g)| = |X/G| · |G|
-- 这里使用 Mathlib4 中已有的等价形式
theorem BurnsideLemma
    [Fintype (MulAction.orbitRel.Quotient G X)]
    [∀ g : G, Fintype {x : X | g • x = x}] :
    (∑ g : G, Fintype.card {x : X | g • x = x}) = Fintype.card (MulAction.orbitRel.Quotient G X) * Fintype.card G := by
  exact MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X
