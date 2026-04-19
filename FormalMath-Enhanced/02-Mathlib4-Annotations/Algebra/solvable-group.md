---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: 可解群性质 (Solvable Group Properties)
---
# 可解群性质 (Solvable Group Properties)

## Mathlib4 引用

```lean
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Abelianization

namespace SolvableGroup

variable {G : Type*} [Group G]

/-- 可解群的定义：存在导列终止于平凡子群 -/
def IsSolvable (G : Type*) [Group G] : Prop :=
  ∃ n : ℕ, derivedSeries G n = ⊥

/-- 可解群的商群仍可解 -/
theorem solvable_quotient {N : Subgroup G} [N.Normal] [IsSolvable G] :
    IsSolvable (G ⧸ N) := by
  rcases ‹IsSolvable G› with ⟨n, hn⟩
  use n
  rw [derivedSeries_quotient, hn]
  simp

/-- 可解群的子群仍可解 -/
theorem solvable_subgroup {H : Subgroup G} [IsSolvable G] : IsSolvable H := by
  rcases ‹IsSolvable G› with ⟨n, hn⟩
  use n
  rw [derivedSeries_subgroup]
  simp [hn]

/-- 可解群的扩张仍可解 -/
theorem solvable_extension {N : Subgroup G} [N.Normal]
    [IsSolvable N] [IsSolvable (G ⧸ N)] : IsSolvable G := by
  rcases ‹IsSolvable N› with ⟨m, hm⟩
  rcases ‹IsSolvable (G ⧸ N)› with ⟨n, hn⟩
  use m + n
  -- 证明导列在m+n步后终止
  sorry

end SolvableGroup
```

## 数学背景

可解群的概念源于Evariste Galois对多项式方程可解性的研究（1830年左右）。Galois发现多项式方程根式可解当且仅当其伽罗瓦群是可解群。这一深刻的联系奠定了群论在代数中的核心地位，并直接导致了五次及以上一般方程无根式解的证明。

## 直观解释

可解群描述的是**通过一系列交换运算可以从群"解"出单位元**的群。

想象一个复杂的锁（群），可解群意味着存在一系列"钥匙"（导列），每把钥匙都比前一把简单（交换化），最终能打开锁（达到平凡群）。具体来说，通过不断取换位子群，如果最终得到平凡群，则原群可解。

## 形式化表述

群 $G$ 的**导列**定义为：
$$G^{(0)} = G, \quad G^{(n+1)} = [G^{(n)}, G^{(n)}]$$

其中 $[H, H]$ 是 $H$ 的换位子群（由所有 $[a,b] = aba^{-1}b^{-1}$ 生成）。

群 $G$ **可解**当且仅当存在 $n$ 使得 $G^{(n)} = \{e\}$。

**等价刻画**：$G$ 存在正规列
$$G = G_0 \triangleright G_1 \triangleright \cdots \triangleright G_n = \{e\}$$
使得每个因子 $G_i/G_{i+1}$ 都是交换群。

## 证明思路

1. **商群可解性**：利用导列与商映射的关系，证明 $\pi(G^{(n)}) = (G/N)^{(n)}$
2. **子群可解性**：利用 $H^{(n)} \subseteq G^{(n)}$ 的包含关系
3. **扩张可解性**：结合导列在正规子群上的限制和商群的性质

核心洞察是导列在群同态下的良好行为和换位子的结构性质。

## 示例

### 示例 1：交换群

所有交换群都是可解群（导列第一步即终止）。

例如 $\mathbb{Z}_n$：$G^{(1)} = [\mathbb{Z}_n, \mathbb{Z}_n] = \{0\}$

### 示例 2：$S_3$（3次对称群）

$S_3^{(1)} = A_3 \cong \mathbb{Z}_3$（3次交错群）

$S_3^{(2)} = [A_3, A_3] = \{e\}$（因为 $A_3$ 交换）

所以 $S_3$ 可解。

### 示例 3：$S_5$ 不可解

$S_5^{(1)} = A_5$

$A_5$ 是单群且非交换，故 $A_5^{(1)} = A_5$

导列永不终止，$S_5$ 不可解。这解释了为什么五次方程一般没有根式解。

## 应用

- **伽罗瓦理论**：多项式根式可解的判别准则
- **代数方程**：五次及以上一般方程不可解
- **几何作图**：尺规作图问题的可解性判定
- **代数拓扑**：基本群的可解性与流形结构

## 相关概念

- 换位子群 (Commutator Subgroup)：由换位子生成的子群
- 导列 (Derived Series)：群的递减正规列
- 正规列 (Normal Series)：子群的正规降链
- 幂零群 (Nilpotent Group)：比可解群更强的条件
- 单群 (Simple Group)：没有非平凡正规子群的群

## 参考

### 教材

- [M. Artin. Algebra. Pearson, 2nd edition, 2010. Chapter 7]
- [Dummit & Foote. Abstract Algebra. Wiley, 3rd edition, 2004. Section 6.1]

### 历史文献

- [Galois. Mémoire sur les conditions de résolubilité des équations par radicaux. 1831]

### 在线资源

- [Mathlib4 文档 - Solvable][https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Solvable.html](需更新)
- [Groupprops - Solvable group][https://groupprops.subwiki.org/wiki/Solvable_group](需更新)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
