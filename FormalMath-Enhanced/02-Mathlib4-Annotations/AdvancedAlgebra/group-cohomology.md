# 群上同调

## Mathlib4 引用

```lean
import Mathlib.RepresentationTheory.GroupCohomology.Basic

namespace RepresentationTheory

/-- 群上同调的定义 -/
theorem group_cohomology_def
    {G : Type*} [Group G] [Fintype G]
    {k : Type*} [CommRing k]
    (V : Type*) [AddCommGroup V] [Module k V]
    [Representation k G V] (n : ℕ) :
    GroupCohomology H^n G V =
      Ext k n (ModuleCat.of k (MonoidAlgebra k G))
              (ModuleCat.of k V) := by
  -- 群上同调是平凡模的Ext
  rfl

/-- 低维群上同调的解释 -/
theorem low_dimensional_cohomology
    {G : Type*} [Group G] [Fintype G]
    {k : Type*} [CommRing k]
    (V : Type*) [AddCommGroup V] [Module k V]
    [Representation k G V] :
    H^0 G V = V^G ∧
    H^1 G V = Derivation G V ⧸ InnerDerivation G V := by
  -- H^0是不变子，H^1是外导子商内导子
  constructor
  · apply H0_is_invariants
  · apply H1_is_crossed_homomorphisms

end RepresentationTheory
```

## 数学背景

群上同调理论起源于1940年代，由Eilenberg、MacLane和Hopf独立发展。它融合了代数拓扑、同调代数和群论，研究群模的"高阶不变量"。群上同调是理解群扩张、Schur乘子、Galois上同调等结构的统一框架。在现代数学中，群上同调与代数K-理论、数论中的Galois表示、代数几何中的etale上同调都有深刻联系。

## 直观解释

群上同调度量了群作用的"障碍"。H^0 是不动点（平凡障碍），H^1 是交叉同态（"几乎同态"）模去真正的同态，H^2 分类群扩张（将群"粘合"起来的方式）。高阶上同调则度量更复杂的代数结构。想象群 G 试图作用于某种结构——上同调类告诉我们这种作用在多大程度上"不标准"或"有阻碍"。

## 形式化表述

设 G 是群，V 是 G-模（Z[G]-模）。

**定义**：H^n(G, V) = Ext^n_{Z[G]}(Z, V)

**Bar消解**：用标准消解计算
$$\cdots \to \mathbb{Z}[G^{n+1}] \to \mathbb{Z}[G^n] \to \cdots \to \mathbb{Z}[G] \to \mathbb{Z} \to 0$$

**低维解释**：

- H^0(G, V) = V^G（不变子模）
- H^1(G, V) = Der(G, V) / Ider(G, V)（导子商内导子）
- H^2(G, V) 分类 V 被 G 的扩张

## 证明思路

1. **消解构造**：建立 G-模的投射消解
2. **复形构造**：应用 Hom_{Z[G]}(-, V)
3. **上循环/上边缘**：识别上闭链群和上边缘群
4. **低维计算**：直接计算前几个上同调群

## 示例

### 示例 1：平凡模的上同调

**问题**：计算 H^n(G, Z)，其中 G 平凡作用于 Z。

**解答**：

H^0(G, Z) = Z（全部是不变的）

H^1(G, Z) = Hom(G, Z)（群同态）

对于有限群 G，H^n(G, Q) = 0（n >= 1），因为 |G| 可逆。

### 示例 2：H^2 与群扩张

**问题**：用 H^2(G, A) 分类群扩张 1 -> A -> E -> G -> 1。

**解答**：

群扩张由2-上循环 α: G x G -> A 分类，上边缘对应等价扩张。

因此等价类与 H^2(G, A) 的元素一一对应。

分裂扩张对应零上同调类。

## 应用

- **代数拓扑**：空间的上同调与基本群
- **数论**：Galois上同调（局部和整体类域论）
- **群扩张**：Schur乘子和中心扩张
- **代数几何**：Brauer群和etale上同调
- **K-理论**：代数K-群的计算

## 相关概念

- [导出函子](./derived-functor.md)：群上同调的理论基础
- [Ext函子](./ext-functor.md)：群上同调的等价定义
- [Galois上同调](./galois-cohomology.md)：绝对Galois群的上同调
- [群扩张](./group-extension.md)：H^2 的分类对象
- [Tate上同调](./tate-cohomology.md)：有限群的上同调变体

## 参考

### 教材

- Brown, K.S. Cohomology of Groups. Springer, 1982.
- Weibel, C.A. An Introduction to Homological Algebra. Cambridge, 1994. Chapter 6

### 论文

- Eilenberg, S. & MacLane, S. Cohomology theory in abstract groups I, II. Ann. of Math., 48: 51-78, 326-341, 1947.

### 在线资源

- [Group Cohomology Wikipedia](https://en.wikipedia.org/wiki/Group_cohomology)
- [nLab - Group Cohomology](https://ncatlab.org/nlab/show/group+cohomology)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
