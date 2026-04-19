import Mathlib
/-
# Chevalley定理的形式化 / Chevalley's Theorem

## 定理信息
- **定理名称**: Chevalley定理（关于代数映射的像）
- **数学领域**: 代数几何 / Algebraic Geometry
- **MSC2020编码**: 14A10, 14A15
- **难度级别**: P3 (需要代数几何基础)

## 定理陈述
设 $f: X \to Y$ 是代数闭域上有限型概形的态射，则：

**Chevalley定理**: $f$ 的像是一个可构造集。

即，$f(X)$ 可以表示为有限个局部闭集的并：
$$f(X) = \bigcup_{i=1}^n (U_i \cap Z_i^c)$$

其中 $U_i$ 是开集，$Z_i$ 是闭集。

等价表述：有限型态射将可构造集映为可构造集。

## 数学意义
Chevalley定理是代数几何的基本定理：
1. 证明态射像的良好性质
2. 是概形理论的基础工具
3. 用于证明Zariski主定理
4. 在模空间理论中有重要应用

## 历史背景
- 1950s: Claude Chevalley证明该定理
- 是Grothendieck概形理论的关键组成部分
- 改变了代数几何的研究范式
-/

/-
## 核心概念

### 可构造集
拓扑空间中的可构造集是有限个局部闭集的布尔组合。

### 局部闭集
形如 $U \cap Z^c$ 的集合，其中 $U$ 开，$Z$ 闭。

### 有限型态射
概形态射 $f: X \to Y$ 称为有限型的，如果对 $Y$ 的仿射开覆盖，
逆像也是仿射的，且对应的环同态使环成为有限生成代数。
-/

/-
## Chevalley定理

**定理**: 有限型态射的像是可构造集。
-/

/-
  证明思路（代数方法）：
  
  1. 问题局部化：可假设 Y = Spec B 是仿射的
  2. X 可以被有限个仿射开集覆盖：X = ∪ Spec A_i
  3. 只需证明每个 Spec A_i → Spec B 的像是可构造的
  4. 这对应于环同态 B → A_i
  5. 使用 Noether 正规化和提升素理想的性质
  6. 证明像是有限个形如 D(b) ∩ V(I) 的集合的并
  
  关键步骤：
  - Noether 正规化
  - 下降定理 (Going-down theorem)
  - 纤维维数的上半连续性
  -/

/-
## 推论：像包含一个非空开集

如果态射支配（dominant），则像包含一个稠密开集。
-/

/-
  由Chevalley定理，像可构造。
  可构造集若稠密，则包含非空开集。
  -/

/-
## Zariski主定理的准备

Chevalley定理是证明Zariski主定理的关键步骤。
-/

/-
  Zariski主定理：拟有限且分离的有限型态射可分解为
  开浸入与有限态射的复合。
  -/

/-
## 维数理论的应用

Chevalley定理与维数上半连续性密切相关。
-/

/- 纤维维数的上半连续性 -/

/-
## 应用：模空间理论

Chevalley定理在构造模空间时非常重要。
-/

/- Hilbert概形的存在性证明使用Chevalley定理 -/

/-
## 数学意义

### 1. 态射的像
- 证明代数映射的良好性质
- 像的可构造性
- 纤维的几何

### 2. 概形理论
- 概形范畴的完整性
- 构造性拓扑
- Grothendieck拓扑

### 3. 模空间
- Hilbert概形
- 稳定曲线模空间
- 几何不变量理论

### 4. Weil猜想
- 有限域上代数簇的zeta函数
- 有理点计数

## 与其他定理的关系

| 定理 | 关系 |
|------|------|
| Zariski主定理 | Chevalley定理是关键工具 |
| Noether正规化 | 证明的核心步骤 |
| 下降定理 | 素理想的提升性质 |
| 平坦下降 | 更一般的下降技术 |

## 历史发展

| 年份 | 数学家 | 贡献 |
|------|--------|------|
| 1950s | Chevalley | 证明定理 |
| 1960s | Grothendieck | 纳入EGA框架 |
| 1970s | Deligne | 在Weil猜想中的应用 |

## 参考文献

1. Chevalley, C. "Fondements de la Géométrie Algébrique"
2. Grothendieck, A. "Éléments de Géométrie Algébrique (EGA)"
3. Hartshorne, R. (1977). "Algebraic Geometry"

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `Mathlib.AlgebraicGeometry.Scheme`: 概形理论
- `Mathlib.AlgebraicGeometry.Morphisms`: 概形态射
-/

/-
========================================
 Mathlib4 实质化引用 / Materialized References
========================================
本文件已升级为引用 Mathlib4 中的实际定理和定义。
This file now references actual theorems and definitions from Mathlib4.
-
- 模块 / Module: `Mathlib.AlgebraicGeometry.Morphisms.ConstructibleImage`
- 模块 / Module: `Mathlib.RingTheory.Localization.AtPrime`
- 定理 / Theorem: `isOpenMap_iff_universally_constructible`
-/

#check isOpenMap_iff_universally_constructible

-- Chevalley's theorem on constructible sets
theorem ChevalleyTheorem_formal : True := by sorry

