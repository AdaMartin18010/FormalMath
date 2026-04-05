---
msc_primary: 00A99
processed_at: '2026-04-03'
title: Ramsey定理 (Ramsey's Theorem)
---
# Ramsey定理 (Ramsey's Theorem)

## Mathlib4 引用

```lean
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring

namespace RamseyTheorem

/-- Ramsey数 -/
def ramseyNumber (s t : ℕ) : ℕ :=
  sInf {n : ℕ | ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
    Fintype.card V = n → ∃ S : Finset V, G.IsClique S ∧ S.card = s ∨
    G.IsIndependent S ∧ S.card = t}

/-- Ramsey定理：对角形式 -/
theorem ramsey_diagonal (k n : ℕ) :
    ∃ N : ℕ, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      Fintype.card V ≥ N →
      ∃ S : Finset V, (G.IsClique S ∨ G.IsIndependent S) ∧ S.card = n := by
  -- 利用归纳法和鸽巢原理
  sorry

/-- Ramsey定理：一般形式 -/
theorem ramsey_general (colors : ℕ) (sizes : Fin colors → ℕ) :
    ∃ N : ℕ, ∀ (V : Type*) [Fintype V] (edgeColoring : (V → V → ℕ)),
      Fintype.card V ≥ N →
      ∃ c : Fin colors, ∃ S : Finset V, S.card = sizes c ∧
      ∀ x y ∈ S, x ≠ y → edgeColoring x y = c := by
  -- 多色Ramsey定理
  sorry

/-- Ramsey数上界 -/
theorem ramsey_bound (s t : ℕ) (hs : 2 ≤ s) (ht : 2 ≤ t) :
    ramseyNumber s t ≤ Nat.choose (s + t - 2) (s - 1) := by
  -- Erdős–Szekeres上界
  sorry

end RamseyTheorem
```

## 数学背景

Ramsey定理由英国数学家Frank P. Ramsey于1930年在其研究数理逻辑的论文中证明。这一定理是组合数学中最深刻的结果之一，揭示了"完全无序是不可能的"——在任何足够大的结构中，必然存在某种有序的子结构。Ramsey理论已成为组合数学的一个重要分支。

## 直观解释

Ramsey定理告诉我们：**在任何足够大的聚会中，必有至少 $s$ 人互相认识，或至少 $t$ 人互不认识**。想象社交网络中，无论关系如何复杂，只要网络足够大，就一定会出现"紧密小团体"或"互不相识群体"。这是"完全无序不可能存在"的数学表述。

## 形式化表述

**图论版本**：对任意正整数 $s, t \geq 2$，存在最小整数 $R(s, t)$ 使得：

任何 $R(s, t)$ 个顶点的完全图，用红蓝两色染边后，必含红色 $K_s$ 或蓝色 $K_t$。

**超图版本**：对任意 $r$-一致超图的边染色，存在单色完全子超图。

**无限版本**：可数无限集的 $k$-子集任意有限染色，存在无限单色子集。

## 证明思路

1. **归纳法**：对 $s + t$ 归纳
2. **鸽巢原理**：考虑某顶点 $v$，其红边邻居或蓝边邻居足够多
3. **递归估计**：$R(s, t) \leq R(s-1, t) + R(s, t-1)$
4. **上界**：$R(s, t) \leq \binom{s+t-2}{s-1}$
5. **存在性**：归纳保证Ramsey数有限

## 示例

### 示例 1：$R(3, 3) = 6$

6个人中必有3人互相认识或3人互不认识。

$K_5$ 可以避免：五边形的边染红，五角星的边染蓝。

### 示例 2：$R(4, 3) = 9$

9个人中必有4人互相认识或3人互不认识。

### 示例 3：已知Ramsey数

- $R(3, 3) = 6$
- $R(4, 4) = 18$
- $R(5, 5)$ 未知（在43到48之间）

## 应用

- **数论**：算术级数存在性（van der Waerden定理）
- **几何**：Erdős–Szekeres定理（凸多边形存在性）
- **理论计算机科学**：通信复杂度下界
- **逻辑**：Paris-Harrington定理（不可证命题）
- **几何图论**：点集的组合性质

## 相关概念

- [鸽巢原理](./pigeonhole-principle.md)：证明工具
- [van der Waerden定理](./vanderwaerden-theorem.md)：算术级数版本
- [Erdős–Szekeres定理](./erdos-szekeres-theorem.md)：几何Ramsey理论
- [图的团](./graph-clique.md)：完全子图

## 参考

### 教材

- [Graham, Rothschild, Spencer. Ramsey Theory. Wiley, 2nd edition, 1990]
- [Diestel. Graph Theory. Springer, 5th edition, 2017. Chapter 9]

### 历史文献

- [Ramsey. On a problem of formal logic. 1930]

### 在线资源

- [Mathlib4 文档 - Simple Graph](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Basic.html)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
