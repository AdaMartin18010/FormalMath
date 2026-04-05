---
msc_primary: 00A99
processed_at: '2026-04-03'
title: Burnside引理 (Burnside's Lemma)
---
# Burnside引理 (Burnside's Lemma)

## Mathlib4 引用

```lean
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Index

namespace BurnsideLemma

variable {α : Type*} [Finite α] (G : Type*) [Group G] [MulAction G α] [Finite G]

/-- Burnside引理 -/
theorem burnside_lemma :
    Fintype.card (Quotient (MulAction.orbitRel G α)) =
    (1 / Fintype.card G) * ∑ g : G, Fintype.card (fixedPoints g) := by
  -- 利用轨道-稳定子定理和Fubini原理
  sorry

/-- Cauchy-Frobenius引理（同一定理的另一命名）-/
theorem cauchy_frobenius_lemma :
    Fintype.card (Quotient (MulAction.orbitRel G α)) =
    (1 / Fintype.card G) * ∑ g : G, Fintype.card {x : α | g • x = x} := by
  -- 等价表述
  sorry

/-- 轨道计数 -/
theorem orbit_count (h : Fintype.card G ≠ 0) :
    Nat.card (Quotient (MulAction.orbitRel G α)) =
    (∑ g : G, Nat.card (MulAction.fixedPoints g)) / Fintype.card G := by
  -- 整数除法版本
  sorry

end BurnsideLemma
```

## 数学背景

Burnside引理（也称为Cauchy-Frobenius引理或Burnside计数定理）是群作用下计数轨道数的基本工具。虽然以William Burnside命名，但他将其归功于Frobenius，而Frobenius又指出Cauchy早已知晓此结果。这一定理是Pólya计数理论的基础，在化学（分子结构计数）、组合学和物理学中有广泛应用。

## 直观解释

Burnside引理告诉我们：**群作用下不等价对象的个数，等于群元素不动点数的平均值**。想象一群人围坐一圈传礼物（群作用），Burnside引理说：不等价的礼物配置数，等于每个人"看起来"礼物没动的次数的平均。这巧妙地将复杂的轨道计数转化为简单的平均。

## 形式化表述

设有限群 $G$ 作用在有限集 $X$ 上。则轨道数（不等价类的个数）为：

$$|X/G| = \frac{1}{|G|} \sum_{g \in G} |X^g|$$

其中 $X^g = \{x \in X : g \cdot x = x\}$ 是 $g$ 的不动点集。

等价表述：轨道数 = 群元素不动点数的平均值。

## 证明思路

1. **轨道-稳定子定理**：$|G| = |G_x| \cdot |Gx|$，其中 $G_x$ 是稳定子群
2. **计数对**：计算 $\{(g, x) : g \cdot x = x\}$ 的元素数
3. **Fubini原理**：
   - 按群元素计数：$\sum_{g \in G} |X^g|$
   - 按集合元素计数：$\sum_{x \in X} |G_x| = \sum_{x \in X} \frac{|G|}{|Gx|}$
4. **轨道求和**：$\sum_{x \in X} \frac{1}{|Gx|} = \sum_{\text{轨道 } O} \sum_{x \in O} \frac{1}{|O|} = |X/G|$

## 示例

### 示例 1：项链计数

用 $k$ 种颜色给 $n$ 个珠子的项链染色，考虑旋转等价。

群：$G = \mathbb{Z}/n\mathbb{Z}$（循环群）

轨道数：$\frac{1}{n} \sum_{d|n} \varphi(d) k^{n/d}$

### 示例 2：立方体染色

用 $k$ 种颜色给立方体的面染色，考虑旋转等价。

群：$G = S_4$，阶为24

轨道数：$\frac{1}{24}(k^6 + 3k^4 + 12k^3 + 8k^2)$

### 示例 3：分子结构

烷烃 $C_n H_{2n+2}$ 的同分异构体计数。

利用对称群作用下的轨道计数。

## 应用

- **组合计数**：染色问题、配置计数
- **化学**：分子同分异构体计数
- **物理学**：统计力学中的状态计数
- **图论**：非同构图计数
- **编码理论**：等价码的计数

## 相关概念

- [群作用](./group-action.md)：数学结构
- [轨道-稳定子定理](./orbit-stabilizer-theorem.md)：群论基本定理
- [Pólya计数定理](./polya-counting-theorem.md)：Burnside引理的推广
- [对称群](./symmetric-group.md)：常见的作用群

## 参考

### 教材

- [Dummit & Foote. Abstract Algebra. Wiley, 3rd edition, 2004. Chapter 4]
- [van Lint & Wilson. A Course in Combinatorics. Cambridge, 2001. Chapter 14]

### 历史文献

- [Burnside. Theory of Groups of Finite Order. 1897]

### 在线资源

- [Mathlib4 文档 - Group Action](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/GroupAction/Basic.html)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
