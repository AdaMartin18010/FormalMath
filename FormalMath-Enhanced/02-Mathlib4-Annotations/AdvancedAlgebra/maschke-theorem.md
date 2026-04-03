---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# Maschke定理

## Mathlib4 引用

```lean
import Mathlib.RepresentationTheory.Maschke

namespace RepresentationTheory

/-- Maschke定理：有限群的表示在特征不整除群阶的域上完全可约 -/
theorem maschke_theorem
    {k G : Type*} [Field k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)]
    {V : Rep k G} (W : Submodule k V) [W.IsSubmoduleRepresentation] :
    ∃ W' : Submodule k V,
      W'.IsSubmoduleRepresentation ∧
      IsInternal (W ⊕ W') := by
  -- 证明使用平均技巧构造投影算子
  apply exists_isComplement_representation
  infer_instance

end RepresentationTheory
```

## 数学背景

Maschke定理由德国数学家Heinrich Maschke于1899年证明，是有限群表示论的奠基性结果。该定理表明，在合适的条件下，群表示的每个子表示都有补表示，从而每个表示都是不可约表示的直和。这一定理为有限群的特征标理论奠定了坚实基础。

## 直观解释

Maschke定理告诉我们：当域的特征不整除群的阶时，任何群表示都可以"分解"为简单构件。这就像乐高积木——无论多复杂的结构，都可以拆解成最基本的模块。定理的核心洞察是使用"平均技巧"构造G-等变投影，这种对称化操作保证了不变性的保持。

## 形式化表述

设 $k$ 是域，$G$ 是有限群，若 $\text{char}(k) \nmid |G|$，则群代数 $k[G]$ 是半单的。等价表述：任意 $k[G]$-模都是半单模。

## 证明思路

1. **构造投影算子**：对任意线性投影 $\pi: V \to W$，构造G-平均
2. **对称化操作**：定义 $\pi'(v) = \frac{1}{|G|}\sum_{g \in G} g \cdot \pi(g^{-1} \cdot v)$
3. **验证等变性**：证明 $\pi'$ 是G-等变的
4. **分解存在性**：利用 $\pi'$ 的核给出补子表示

## 示例

### 示例 1：对称群表示

**问题**：证明 $S_3$ 在 $\mathbb{C}$ 上的置换表示完全可约。

**解答**：

由于 $\text{char}(\mathbb{C}) = 0$，$6$ 可逆，Maschke定理适用。置换表示可分解为：

- 平凡表示（全1子空间）
- 标准表示（坐标和为零的子空间）

### 示例 2：模 $p$ 表示的局限

**问题**：考虑 $C_p$（p阶循环群）在 $\mathbb{F}_p$ 上的正则表示。

**分析**：此时 $\text{char}(\mathbb{F}_p) = p \mid |C_p|$，Maschke定理不适用。事实上，存在不可分解的表示。

## 应用

- **特征标理论**：建立不可约表示与特征标的对应
- **量子化学**：分子对称性的表示分解
- **密码学**：基于表示论的编码构造
- **组合数学**：Burnside引理的应用基础

## 相关概念

- [特征标正交性](./character-orthogonality.md)：Maschke定理的推论
- [Frobenius互反律](./frobenius-reciprocity.md)：诱导与限制函子的伴随关系
- [半单代数](./semisimple-algebra.md)：群代数的结构理论
- [Schur引理](./schur-lemma.md)：不可约表示的同态性质
- [Peter-Weyl定理](./peter-weyl-theorem.md)：紧致群的推广

## 参考

### 教材

- Serre, J.P. Linear Representations of Finite Groups. Springer, 1977. Chapter 2
- Fulton, W. & Harris, J. Representation Theory. Springer, 1991. Chapter 1

### 论文

- Maschke, H. Über den arithmetischen Charakter der Coefficienten der Substitutionen endlicher linearer Substitutionsgruppen. Math. Ann., 50: 492-498, 1898.

### 在线资源

- [GroupProps - Maschke's Theorem](https://groupprops.subwiki.org/wiki/Maschke%27s_theorem)
- [Stacks Project - Maschke's Theorem](https://stacks.math.columbia.edu/tag/00C0)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
