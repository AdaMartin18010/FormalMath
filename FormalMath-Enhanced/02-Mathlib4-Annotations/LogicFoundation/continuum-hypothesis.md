# 连续统假设

## Mathlib4 引用

```lean
import Mathlib.SetTheory.Cardinal.Continuum

namespace SetTheory

/-- 连续统假设 -/
def ContinuumHypothesis : Prop :=
  ℵ₁ = 𝔠

/-- 广义连续统假设 -/
def GeneralizedContinuumHypothesis : Prop :=
  ∀ (κ : Cardinal), ℵ₀ ≤ κ → 2^κ = κ⁺

/-- CH的独立性 -/
theorem ch_independence :
  Consistent ZFC (¬ ContinuumHypothesis) ∧
  Consistent ZFC (ContinuumHypothesis) := by
  -- Cohen和Gödel的结果
  sorry

end SetTheory
```

## 数学背景

连续统假设（CH）由Georg Cantor在1878年提出，是集合论中最著名的问题。CH断言：在可数无穷 $ℵ_0$ 和连续统 $𝔠 = 2^{ℵ_0}$ 之间不存在其他基数。即 $ℵ_1 = 𝔠$。Kurt Gödel在1940年证明CH与ZFC一致（相对一致性），Paul Cohen在1963年用他发明的力迫法证明$\neg$CH也与ZFC一致。CH的独立性是20世纪数学最重要的发现之一，Cohen因此获得Fields奖。

## 直观解释

连续统假设询问：实数集的"大小"是否是紧接在可数集之后的无穷？想象所有实数——它们显然比自然数多。CH断言：任何实数的无限子集要么可数，要么与全体实数一样多，没有中间大小。这与我们的直觉可能有冲突——实数集非常丰富，很难相信它与下一个无穷基数相等。事实上，许多集合论学家认为CH是"错误"的（虽然这在ZFC中不可证）。

## 形式化表述

**连续统假设（CH）**：$2^{\aleph_0} = \aleph_1$

**等价表述**：

- 任何实数的无限子集要么可数，要么与 $\mathbb{R}$ 等势
- 不存在基数 $\kappa$ 使得 $\aleph_0 < \kappa < 2^{\aleph_0}$

**广义连续统假设（GCH）**：对所有无限基数 $\kappa$，$2^\kappa = \kappa^+$

**独立性结果**：

- Gödel（1940）：$\text{Con}(ZFC) \Rightarrow \text{Con}(ZFC + CH)$
- Cohen（1963）：$\text{Con}(ZFC) \Rightarrow \text{Con}(ZFC + \neg CH)$

## 证明思路

1. **可构成宇宙**：Gödel构造 $L$，在其中CH成立
2. **力迫法**：Cohen构造泛型扩张，使 $2^{\aleph_0} > \aleph_1$
3. **相对一致性**：证明两种扩展保持ZFC的一致性
4. **绝对性**：某些命题在 $L$ 和 $V$ 中相同
5. **大基数**：大基数假设可以"决定"CH的某些变体

## 示例

### 示例 1：可构成集

**问题**：证明在可构成宇宙 $L$ 中CH成立。

**解答**：

Gödel证明：$L$ 满足GCH。

关键：$L$ 中的实数都是"可定义的"，数量有限。

具体地，$|\mathbb{R}^L| = \aleph_1^L$，而 $\aleph_1^L \leq \aleph_1$。

### 示例 2：添加Cohen实数

**问题**：用力迫法使 $2^{\aleph_0} = \aleph_2$。

**解答**：

Cohen力迫：$\mathbb{P} = \text{Fn}(\aleph_2 \times \omega, 2)$。

在泛型扩张 $M[G]$ 中，添加了 $\aleph_2^M$ 个新的Cohen实数。

通过cc.c.性质，$\aleph_1$ 和 $\aleph_2$ 保持，故 $2^{\aleph_0} \geq \aleph_2$。

## 应用

- **集合论**：大基数和决定性公理的研究
- **描述集合论**：射影集合的结构
- **拓扑学**：实数集的子集性质
- **测度论**：不可测集的存在性
- **模型论**：饱和模型的基数

## 相关概念

- [力迫法](./forcing.md)：证明CH独立性的工具
- [可构成宇宙](./constructible-universe.md)：Gödel构造的内模型
- [基数算术](./cardinal-arithmetic.md)：CH的表述语言
- [大基数](./large-cardinal.md)：可能"决定"CH的公理
- [决定性公理](./axiom-of-determinacy.md)：与CH互斥的替代公理

## 参考

### 教材

- Kunen, K. Set Theory. College Publications, 2011.
- Jech, T. Set Theory. Springer, 2003. Chapter 15

### 论文

- Cantor, G. Ein Beitrag zur Mannigfaltigkeitslehre. J. Reine Angew. Math., 84: 242-258, 1878.
- Gödel, K. The consistency of the axiom of choice and of the generalized continuum hypothesis. Proc. Nat. Acad. Sci. USA, 24: 556-557, 1938.
- Cohen, P.J. The independence of the continuum hypothesis. Proc. Nat. Acad. Sci. USA, 50: 1143-1148, 1963.

### 在线资源

- [Continuum Hypothesis Wikipedia](https://en.wikipedia.org/wiki/Continuum_hypothesis)
- [nLab - Continuum Hypothesis](https://ncatlab.org/nlab/show/continuum+hypothesis)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
