---
msc_primary: 00A99
processed_at: '2026-04-03'
title: 诱导表示
---
# 诱导表示

## Mathlib4 引用

```lean
import Mathlib.RepresentationTheory.InducedRepresentation

namespace RepresentationTheory

/-- 诱导表示的构造 -/
theorem induced_representation 
    {k G H : Type*} [Field k] [Group G] [Group H]
    (φ : H →* G) (W : Rep k H) :
    InducedRepresentation φ W = 
      (MonoidAlgebra k G) ⊗[MonoidAlgebra k H] W := by
  -- 诱导表示是张量积构造
  rfl

/-- 诱导表示的泛性质 -/
theorem induced_representation_universal 
    {k G H : Type*} [Field k] [Group G] [Group H]
    (φ : H →* G) (W : Rep k H) (V : Rep k G) :
      (InducedRepresentation φ W ⟶ V) ≃ 
      (W ⟶ RestrictedRepresentation φ V) := by
  -- Frobenius互反律的同构
  apply frobeniusReciprocity

end RepresentationTheory
```

## 数学背景

诱导表示是群表示论中的核心构造，由Frobenius在1898年系统引入。给定群 $G$ 的子群 $H$ 的一个表示，诱导构造产生 $G$ 的一个表示。这一过程如同"扩张"局部信息到整体，是研究群表示的强有力工具。Mackey的诱导理论、Clifford理论以及Langlands纲领都建立在诱导表示的基础之上。诱导表示也是调和分析中傅里叶变换的群论类比。

## 直观解释

诱导表示如同将一个"小舞台"（子群 $H$）上的"剧本"（表示 $W$）扩展为"大舞台"（群 $G$）上的"大戏"。对每个 $H$ 的陪集，我们放置一个 $W$ 的副本，然后 $G$ 通过左乘作用在这些副本上。这种构造保证了 $H$ 的作用与原来的表示一致，同时定义了在整个 $G$ 上的作用。诱导表示的维数等于 $[G:H] \cdot \dim(W)$，反映了"扩张"的几何。

## 形式化表述

设 $H \leq G$，$W$ 是 $H$ 的表示。

**定义**：诱导表示 $\text{Ind}_H^G W$ 是
$$k[G] \otimes_{k[H]} W$$

**具体实现**：作为向量空间，
$$\text{Ind}_H^G W = \bigoplus_{g \in G/H} g \cdot W$$

其中 $G$ 作用为 $g' \cdot (g \otimes w) = (g'g) \otimes w$。

**特征标公式**（Frobenius）：
$$\chi_{\text{Ind}_H^G W}(g) = \frac{1}{|H|} \sum_{\substack{x \in G \\ x^{-1}gx \in H}} \chi_W(x^{-1}gx)$$

## 证明思路

1. **张量积构造**：定义 $k[G] \otimes_{k[H]} W$
2. **验证表示结构**：验证 $G$-作用的良定义性
3. **维数计算**：$\dim(\text{Ind}_H^G W) = [G:H] \cdot \dim(W)$
4. **泛性质**：验证Frobenius互反律

## 示例

### 示例 1：正则表示

**问题**：证明 $G$ 的正则表示是平凡表示从平凡子群的诱导。

**解答**：

$\text{Ind}_{\{e\}}^G \mathbf{1} = k[G] \otimes_k k \cong k[G]$ 作为 $G$-模。

这正是正则表示——基由 $G$ 的元素标记，$G$ 通过左乘作用。

### 示例 2：置换表示

**问题**：设 $G$ 作用在集合 $X$ 上，$H$ 是 $x_0 \in X$ 的稳定子群。描述诱导表示。

**解答**：

$\text{Ind}_H^G \mathbf{1} = k[G] \otimes_{k[H]} k \cong k[X]$，以 $X$ 为基的置换表示。

这对应于 $G$ 在 $X$ 上的置换作用。

## 应用

- **有限群表示**：不可约表示的构造
- **Lie群表示**：主系列表示
- **自守形式**：Eisenstein级数
- **物理学**：对称性诱导的能级
- **组合数学**：排列表示的分解

## 相关概念

- [Frobenius互反律](./frobenius-reciprocity.md)：诱导的伴随性质
- [Mackey定理](./mackey-theorem.md)：诱导与限制的交互
- [限制表示](./restricted-representation.md)：诱导的反向操作
- [特征标诱导](./character-induction.md)：诱导的特征标公式
- [诱导特征标表](./induced-character-table.md)：实际计算工具

## 参考

### 教材

- Serre, J.P. Linear Representations of Finite Groups. Springer, 1977. Chapter 7
- Fulton, W. & Harris, J. Representation Theory. Springer, 1991. Chapter 3

### 论文

- Frobenius, G. Über Relationen zwischen den Charakteren einer Gruppe und denen ihrer Untergruppen. Sitzungsberichte der Königlich Preußischen Akademie der Wissenschaften, 501-515, 1898.
- Mackey, G.W. On induced representations of groups. Amer. J. Math., 73: 576-592, 1951.

### 在线资源

- [Induced Representation Wikipedia](https://en.wikipedia.org/wiki/Induced_representation)
- [Groupprops - Induced Representation](https://groupprops.subwiki.org/wiki/Induced_representation)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
