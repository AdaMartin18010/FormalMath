---
title: "轨道-稳定子定理 自然语言与 Lean4 对照"
msc_primary: 68V20
level: "silver"
target_courses:
  - "MIT 18.701"
review_status: completed
---

## 定理陈述

**自然语言**：设群 $G$ 作用于集合 $X$。对任意 $x \in X$，定义
- **轨道**：$G \cdot x = \{g \cdot x : g \in G\} \subseteq X$；
- **稳定子**：$G_x = \{g \in G : g \cdot x = x\} \leq G$（$G$ 的子群）。

**轨道-稳定子定理**断言：轨道 $G \cdot x$ 与左陪集空间 $G / G_x$ 之间存在自然的双射。从而当 $G$ 是有限群时，
\[
|G \cdot x| = [G : G_x] = \frac{|G|}{|G_x|}.
\]

**Lean4**：

```lean
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Coset
import Mathlib.SetTheory.Cardinal.Finite

namespace OrbitStabilizerTheorem
open MulAction Subgroup

variable {G X : Type*} [Group G] [MulAction G X]

-- 轨道与 G/stabilizer 双射
theorem orbit_stabilizer (x : X) :
    Nonempty (orbit G x ≃ G ⧸ stabilizer G x) := by
  use orbitEquivQuotientStabilizer G x

-- 有限群版本：|轨道| = |G| / |稳定子|
theorem orbit_stabilizer_card [Fintype G] [Fintype X] [DecidableEq X] (x : X) :
    Fintype.card (orbit G x) = Fintype.card G / Fintype.card (stabilizer G x) := by
  have h := Fintype.card_congr (orbitEquivQuotientStabilizer G x)
  rw [h]
  rw [Subgroup.index_eq_card (stabilizer G x)]
  symm
  exact Eq.symm (Lagrange.index_mul_card (stabilizer G x))
end OrbitStabilizerTheorem
```

## 证明思路

**自然语言**：
1. 定义映射 $\phi: G / G_x \to G \cdot x$ 为 $\phi(g G_x) = g \cdot x$。
2. **良定性**：若 $g G_x = h G_x$，则 $h^{-1} g \in G_x$，即 $(h^{-1} g) \cdot x = x$，从而 $h \cdot x = g \cdot x$。
3. **单射**：若 $g \cdot x = h \cdot x$，则 $(h^{-1} g) \cdot x = x$，即 $h^{-1} g \in G_x$，故 $g G_x = h G_x$。
4. **满射**：对任意 $y \in G \cdot x$，存在 $g \in G$ 使得 $y = g \cdot x = \phi(g G_x)$。
5. 因此 $\phi$ 是双射。当 $G$ 有限时，由拉格朗日定理 $|G| = [G : G_x] \cdot |G_x|$，即得计数公式。

**Lean4**：Mathlib4 的 `orbitEquivQuotientStabilizer G x` 直接构造了上述双射，返回类型为 `orbit G x ≃ G ⧸ stabilizer G x`（即两个类型之间的等价）。有限群版本则结合 `Fintype.card_congr`（等价类型基数相同）和拉格朗日定理 `Lagrange.index_mul_card` 得到计数等式。

## 关键 tactic/概念 教学

- `MulAction G X`：群 $G$ 在集合 $X$ 上的群作用类型类。
- `orbit G x`：元素 $x$ 的轨道，是 $X$ 的子类型。
- `stabilizer G x`：元素 $x$ 的稳定子群。
- `G ⧸ H`：子群 $H$ 的左陪集空间（商集）。
- `orbitEquivQuotientStabilizer`：轨道-稳定子定理的标准双射构造。
- `Fintype.card_congr`：等价类型具有相同的有限基数。

## 练习

1. 考虑 $S_3$ 通过置换作用于集合 $\{1, 2, 3\}$。取 $x = 1$，写出轨道 $S_3 \cdot 1$ 和稳定子 $(S_3)_1$，并验证轨道-稳定子定理。
2. 设 $D_4$（正方形的对称群，阶为 8）作用于正方形的四个顶点。计算每个顶点的轨道大小和稳定子群的阶。
3. 利用轨道-稳定子定理和类方程证明：任何 $p$-群（阶为 $p^n$ 的群）的中心非平凡。
---
**参考文献**

1. 相关教材与学术论文。
