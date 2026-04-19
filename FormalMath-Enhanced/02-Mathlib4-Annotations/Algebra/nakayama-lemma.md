---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: Nakayama 引理 (Nakayama's Lemma)
---
# Nakayama 引理 (Nakayama's Lemma)

## Mathlib4 引用

```lean
import Mathlib.RingTheory.Ideal.LocalRing
import Mathlib.RingTheory.Noetherian

namespace RingTheory

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (I : Ideal R) (hI : I ≤ Jacobson R)

/-- Nakayama 引理：若 M = I M 且 M 有限生成，则 M = 0 -/
theorem nakayama (hM : Module.Finite R M) (h : Submodule.span R (Set.image (fun i => i • m) I) = ⊤) :
    M = 0 := by
  -- 利用 Jacobson 根中元素的拟可逆性和行列式技巧证明
  sorry

end RingTheory
```

## 数学背景

Nakayama 引理是交换代数中最基本、使用最频繁的引理之一，由日本数学家中岛喜久雄（Tadashi Nakayama）在20世纪50年代系统阐述并推广。该引理断言：设 $R$ 是交换环，$I$ 是包含在 Jacobson 根中的理想，$M$ 是有限生成 $R$-模。如果 $M = IM$（即 $M$ 被 $I$ 中元素的作用生成），那么 $M = 0$。Nakayama 引理的一个常用等价形式是：若 $N \subseteq M$ 且 $M/N = I(M/N)$，则 $M = N$。这个引理在局部环上的模论、代数几何中的切空间计算和奇点理论中具有不可替代的作用。

## 直观解释

Nakayama 引理提供了一个强大的工具来判断有限生成模何时为零。直观上，如果一个模 $M$ 可以被包含在 Jacobson 根中的理想 $I$ 所生成，那么 $M$ 实际上必须是零模。为什么？因为 Jacobson 根中的元素在某种意义上是接近于零的——它们在所有极大理想中都存在，因此在局部化后变得很小。如果 $M = IM$，这意味着 $M$ 的每个元素都可以表示为 $I$ 中元素与 $M$ 中元素的乘积之和。由于 $I$ 在 Jacobson 根中，这种自引用的结构迫使 $M$ 坍缩为零。等价形式则告诉我们：如果 $N$ 和 $M$ 的差可以被 $I$ 吸收，那么 $N$ 实际上就等于 $M$——这是一种局部到整体的原理。

## 形式化表述

设 $R$ 是含幺交换环，$J(R)$ 是 $R$ 的 Jacobson 根，$M$ 是有限生成 $R$-模，$I \subseteq J(R)$ 是理想。若 $M = IM$（即 $M$ 的每个元素都可以写成 $\sum i_k m_k$ 的形式，其中 $i_k \in I$, $m_k \in M$），则：

$$M = 0$$

等价形式：

1. 若 $N \subseteq M$ 且 $M = N + IM$，则 $M = N$
2. 若 $M$ 有限生成，$m_1, \dots, m_n \in M$ 在 $M/IM$ 中的像生成 $M/IM$，则 $m_1, \dots, m_n$ 生成 $M$
3. 局部环版本：若 $(R, \mathfrak{m})$ 是局部环，$M$ 有限生成且 $M = \mathfrak{m}M$，则 $M = 0$

其中：

- Jacobson 根 $J(R)$ 是所有极大理想的交
- 局部环是指有唯一极大理想的环
- 条件 $M = IM$ 是等式，不是包含关系

## 证明思路

1. **Cayley-Hamilton 定理**：对有限生成模，考虑恒等自同态 $\text{id}_M$。由于 $M = IM$，可以写出 $\text{id}_M = \sum i_k \phi_k$（$i_k \in I$, $\phi_k \in \text{End}_R(M)$）
2. **行列式技巧**：将上式视为矩阵方程，得到 $\det(\text{id} - A) = 0$，其中 $A$ 的元在 $I$ 中
3. **Jacobson 根性质**：$\det(\text{id} - A) = 1 + a$（$a \in I$）。由于 $I \subseteq J(R)$，$1 + a$ 可逆
4. **矛盾**：但 $\det(\text{id} - A)$ 同时消没 $M$，故 $M = 0$

核心洞察在于 Jacobson 根中元素的拟幂零性使得 $1 + a$ 总是可逆元。

## 示例

### 示例 1：局部环上的生成元提升

设 $(R, \mathfrak{m})$ 是局部环，$M$ 是有限生成 $R$-模。若 $\bar{m}_1, \dots, \bar{m}_n \in M/\mathfrak{m}M$ 构成 $R/\mathfrak{m}$-向量空间的一组基，则由 Nakayama 引理，$m_1, \dots, m_n$ 生成 $M$。这常用于证明自由模的秩的唯一性。

### 示例 2：切空间的计算

在代数几何中，概形 $X$ 在点 $x$ 处的 Zariski 切空间为 $T_x X = (\mathfrak{m}_x / \mathfrak{m}_x^2)^*$。Nakayama 引理保证了：如果 $\mathfrak{m}_x / \mathfrak{m}_x^2 = 0$，则 $\mathfrak{m}_x = 0$，即 $x$ 是孤立点。

### 示例 3：正则局部环的维数理论

正则局部环的维数等于其极大理想模平方的维数。Nakayama 引理在这里起到关键作用，确保了极小生成元集的大小与环的维数相等。

## 应用

- **交换代数**：局部环上模的生成元和基的判定
- **代数几何**：概形的切空间、光滑性和维数理论
- **同调代数**：投射覆盖和投射分解的构造
- **数论**：完备化、形式群和类域论
- **奇点理论**：奇点的嵌入维数和可解性研究

## 相关概念

- Jacobson 根 (Jacobson Radical)：所有极大理想的交
- 局部环 (Local Ring)：有唯一极大理想的交换环
- 有限生成模 (Finitely Generated Module)：存在有限生成元集的模
- Cayley-Hamilton 定理：模自同态满足其特征多项式
- 正则局部环 (Regular Local Ring)：维数等于嵌入维数的局部环

## 参考

### 教材

- [M. F. Atiyah, I. G. Macdonald. Introduction to Commutative Algebra. Addison-Wesley, 1969. Chapter 2]
- [H. Matsumura. Commutative Ring Theory. Cambridge, 1986. Chapter 1]

### 在线资源

- [Mathlib4 - LocalRing](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/LocalRing.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*