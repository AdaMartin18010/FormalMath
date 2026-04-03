# 西罗定理 (Sylow's Theorems)

## Mathlib4 引用

```lean
import Mathlib.GroupTheory.Sylow

namespace Sylow

variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]

/-- 西罗第一定理：若 $p^k \mid |G|$，则存在阶为 $p^k$ 的子群 -/
theorem exists_subgroup_card_pow_prime (k : ℕ) (hk : p ^ k ∣ Nat.card G) :
    ∃ H : Subgroup G, Nat.card H = p ^ k := by
  classical
  have := Fact.mk ‹Fact p.Prime›.out
  exact exists_subgroup_card_pow_prime_of_le_card k 
    (Nat.le_of_dvd (Nat.card_pos) hk)

/-- 西罗第二定理：所有西罗 $p$-子群共轭 -/
theorem isConj_of_isPGroup_of_index_eq (P Q : Sylow p G) :
    IsConj (P : Subgroup G) (Q : Subgroup G) := by
  classical
  exact exists_conjugate_eq P Q

/-- 西罗第三定理：西罗 $p$-子群个数满足同余条件 -/
theorem card_sylow_modeq_one : Nat.card (Sylow p G) ≡ 1 [MOD p] :=
  card_sylow_modEq_one

end Sylow
```

## 数学背景

西罗定理由挪威数学家彼得·路德维希·梅德尔·西罗（Peter Ludwig Mejdell Sylow）于1872年证明，是有限群论的核心结果。这些定理对素数幂阶子群的存在性、共轭性和数量给出了深刻约束，为有限群的分类和研究提供了强大工具。

## 直观解释

西罗定理告诉我们关于群"素数幂结构"的三件事：

1. **存在性**：如果素数幂 $p^k$ 整除群的阶，则存在阶为 $p^k$ 的子群
2. **共轭性**：所有最大的这种子群（西罗 $p$-子群）彼此共轭
3. **数量约束**：西罗 $p$-子群的个数模 $p$ 余 1，且整除群的阶

想象群是一个复杂的建筑，西罗定理告诉我们特定大小的"房间"（$p$-子群）如何分布在整个建筑中。

## 形式化表述

设 $G$ 是有限群，$p$ 是素数，$|G| = p^k \cdot m$，其中 $p \nmid m$。

### 第一定理（存在性）
对任意 $0 \leq i \leq k$，存在阶为 $p^i$ 的子群。

### 第二定理（共轭性）
所有西罗 $p$-子群（阶为 $p^k$ 的子群）彼此共轭。

### 第三定理（数量）
设 $n_p$ 是西罗 $p$-子群的个数，则：
- $n_p \equiv 1 \pmod{p}$
- $n_p \mid m$

## 证明思路

### 第一定理的证明要点：
1. 使用群作用在 $p$-子集的集合上
2. 应用轨道-稳定子定理
3. 通过计数论证证明存在不动点

### 第二定理的证明要点：
1. 让西罗 $p$-子群作用在另一西罗 $p$-子群的陪集上
2. 利用轨道计数证明共轭关系

### 第三定理的证明要点：
1. 让 $G$ 通过共轭作用在西罗 $p$-子群的集合上
2. 利用西罗 $p$-子群的正规化子的性质
3. 轨道计数导出同余条件

## 示例

### 示例 1：阶为 15 的群

设 $|G| = 15 = 3 \cdot 5$。

- $n_3 \equiv 1 \pmod{3}$ 且 $n_3 \mid 5$：$n_3 = 1$
- $n_5 \equiv 1 \pmod{5}$ 且 $n_5 \mid 3$：$n_5 = 1$

唯一的西罗 3-子群和西罗 5-子群都正规，故 $G \cong \mathbb{Z}_{15}$（循环群）。

### 示例 2：阶为 12 的群

设 $|G| = 12 = 2^2 \cdot 3$。

- $n_2 \equiv 1 \pmod{2}$ 且 $n_2 \mid 3$：$n_2 = 1$ 或 $3$
- $n_3 \equiv 1 \pmod{3}$ 且 $n_3 \mid 4$：$n_3 = 1$ 或 $4$

若 $n_3 = 4$，则 $G$ 有 8 个 3 阶元素，剩余 4 个元素构成唯一的西罗 2-子群。

### 示例 3：$S_4$ 的西罗 2-子群

$|S_4| = 24 = 2^3 \cdot 3$。

西罗 2-子群的阶为 8，同构于二面体群 $D_4$。

$n_2 = 3$（验证：$3 \equiv 1 \pmod{2}$ 且 $3 \mid 3$）。

## 应用

- **群分类**：用于分类小阶群（阶 < 100）
- **单群研究**：判断群是否单群
- **伽罗瓦理论**：分析域扩张的自同构群
- **组合设计**：区组设计中的群作用

## 相关概念

- [西罗 $p$-子群 (Sylow p-Subgroup)](./sylow-p-subgroup.md)：最大 $p$-子群
- [$p$-群 (p-Group)](./p-group.md)：阶为素数幂的群
- [共轭类 (Conjugacy Class)](./conjugacy-class.md)：共轭元素的集合
- [正规化子 (Normalizer)](./normalizer.md)：保持子群不变的元素
- [群作用 (Group Action)](./group-action.md)：群在集合上的作用

## 参考

### 教材

- [Dummit & Foote. Abstract Algebra. Wiley, 3rd edition, 2004. Section 4.5]
- [Rotman. An Introduction to the Theory of Groups. Springer, 4th edition, 1995. Chapter 5]

### 历史文献

- [Sylow. Théorèmes sur les groupes de substitutions. Mathematische Annalen, 1872]

### 在线资源

- [Mathlib4 文档 - Sylow](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Sylow.html)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
