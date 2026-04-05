---
msc_primary: 00A99
processed_at: '2026-04-03'
title: Baire纲定理 (Baire Category Theorem)
---
# Baire纲定理 (Baire Category Theorem)

## Mathlib4 引用

```lean
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteSpace

namespace BaireCategory

variable {X : Type*} [TopologicalSpace X]

/-- Baire纲定理：完备度量空间是Baire空间 -/
theorem baire_category_theorem (X : Type*) [MetricSpace X] [CompleteSpace X] :
    BaireSpace X := by
  -- 证明可数个稠密开集的交仍稠密
  sorry

/-- 局部紧Hausdorff空间是Baire空间 -/
theorem locally_compact_baire (X : Type*) [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X] : BaireSpace X := by
  -- 利用紧集和有限交性质
  sorry

/-- 无处稠密集的并的补集稠密 -/
theorem nonmeagre_residual (X : Type*) [MetricSpace X] [CompleteSpace X]
    (F : ℕ → Set X) (hF : ∀ n, NowhereDense (F n)) :
    Dense (⋃ n, F n)ᶜ := by
  -- 直接应用Baire纲定理
  sorry

end BaireCategory
```

## 数学背景

Baire纲定理由法国数学家勒内-路易·贝尔（René-Louis Baire）于1899年在其博士论文中证明。这是泛函分析和点集拓扑中的基本结果，建立了完备度量空间（或局部紧Hausdorff空间）的一个重要结构性质。"纲"（category）在这里是技术术语，与日常含义无关。

## 直观解释

Baire定理告诉我们：**完备空间不能是可数个"瘦小"集合的并**。想象一个完备空间是一整块"实心"的物质；你不能用可数个"千疮百孔"的集合拼凑出它。这保证了完备空间中"大多数"点是"好"的，具有某些通有性质。

## 形式化表述

设 $X$ 是完备度量空间（或局部紧Hausdorff空间）。

**Baire纲定理**：可数个稠密开集的交仍在 $X$ 中稠密。

等价表述：
- $X$ 不是可数个无处稠密集的并
- 可数个疏集的补集的交稠密

术语定义：
- **无处稠密集**：闭包的内部为空（"没有块"）
- **第一纲集**：可数个无处稠密集的并（"瘦小"）
- **第二纲集**：不是第一纲集（"肥"）

## 证明思路

1. **构造Cauchy序列**：从任意开集出发，利用稠密性选择点列
2. **完备性**：序列收敛到某点 $x$
3. **验证在交集中**：所有开集都包含极限点
4. **稠密性得证**：任意开集与交集相交

## 示例

### 示例 1：无理数集

$\mathbb{R}$ 中，有理数集 $\mathbb{Q}$ 是第一纲集（可数且无处稠密）。

无理数集是剩余集（residual），是第二纲集。

### 示例 2：连续但处处不可微函数

在 $C[0,1]$ 中，处处可微的函数构成第一纲集。

"大多数"连续函数处处不可微（Weierstrass型函数是通有的）。

## 应用

- **泛函分析**：一致有界原理、开映射定理的基础
- **实分析**：连续函数空间的性质
- **动力系统**：通有性质的研究
- **微分拓扑**：横截性定理

## 相关概念

- 完备度量空间：定理的主要适用空间
- 无处稠密集："没有内部块"的集合
- 剩余集：包含稠密$G_\delta$集的集合
- 一致有界原理：Baire定理的应用

## 参考

### 教材

- [Rudin. Functional Analysis. McGraw-Hill, 2nd edition, 1991. Chapter 2]
- [Oxtoby. Measure and Category. Springer, 2nd edition, 1980]

### 历史文献

- [Baire. Sur les fonctions de variables réelles. 1899]

### 在线资源

- [Mathlib4 文档 - Baire](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Baire/CompleteSpace.html)[需更新]

---

*最后更新：2026-04-03 | 版本：v1.0.0*
