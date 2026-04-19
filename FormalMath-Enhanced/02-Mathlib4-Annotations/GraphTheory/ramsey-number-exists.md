---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: Ramsey 数存在性 (Ramsey Number Existence)
---
# Ramsey 数存在性 (Ramsey Number Existence)

## Mathlib4 引用

```lean
import Mathlib.Combinatorics.SimpleGraph.Ramsey

namespace SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Ramsey 数存在性：对任意正整数 s, t，Ramsey 数 R(s, t) 存在且有限 -/
theorem ramsey_number_exists (s t : ℕ) (hs : 0 < s) (ht : 0 < t) :
    ∃ N : ℕ, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      N ≤ Fintype.card V →
      (∃ S : Finset V, S.card = s ∧ G.IsClique S) ∨
      (∃ T : Finset V, T.card = t ∧ G.IsAntiClique T) := by
  -- 通过对 s + t 归纳证明
  sorry

end SimpleGraph
```

## 数学背景

Ramsey 理论起源于20世纪20年代末英国数学家弗兰克·拉姆齐（Frank P. Ramsey）的开创性工作。1930年，Ramsey 证明了著名的 Ramsey 定理，其核心思想是：在足够大的结构中，必然会出现某种有序的子结构。Ramsey 数 R(s, t) 是组合数学的基石之一，深刻揭示了大系统中"完全无序是不可能的"。

## 直观解释

Ramsey 定理有一个著名的通俗表述：在一个足够大的聚会中，必然存在 s 个人互相都认识，或者 t 个人互相都不认识。无论人们之间的认识关系如何复杂，只要人数超过某个阈值，这种有序结构就不可避免。这体现了大系统中局部的必然有序性。

## 形式化表述

对任意正整数 $s, t$，存在最小的正整数 $R(s, t)$，使得任意具有 $N \geq R(s, t)$ 个顶点的图 $G$ 满足：

$$G \text{ 包含 } K_s \text{ 或 } G \text{ 包含独立集 } I_t$$

其中：

- $R(s, t)$ 表示 Ramsey 数
- $K_s$ 表示 $s$ 个顶点的完全子图（团）
- $I_t$ 表示 $t$ 个顶点的独立集（无边连接）

Ramsey 数满足递推关系：$R(s, t) \leq R(s-1, t) + R(s, t-1)$。

## 证明思路

1. **归纳假设**：假设对所有满足 $s' + t' < s + t$ 的正整数对，Ramsey 数存在\n2. **递推构造**：证明 $R(s, t) \leq R(s-1, t) + R(s, t-1)$\n3. **计数论证**：任取一顶点 $v$，其邻居集或非邻居集必有一个足够大，从而应用归纳假设\n4. **有限性结论**：由归纳法知对所有正整数 $s, t$，$R(s, t)$ 为有限正整数

核心洞察在于鸽巢原理在图结构中的深刻应用。

## 示例

### 示例 1：$R(3, 3) = 6$

在任意 6 个人的聚会中，必有 3 人互相认识或 3 人互不认识。$K_5$ 的一个 5-圈可以构造出反例说明 $R(3, 3) > 5$。

### 示例 2：$R(3, 4) = 9$

任意 9 个顶点的图必含三角形或 4 个顶点的独立集。而 $K_8$ 的某个特定图可以既无三角形也无 4 顶点独立集。

### 示例 3：已知精确值

目前已知的精确 Ramsey 数极少：$R(1, t) = 1$, $R(2, t) = t$, $R(3, 3) = 6$, $R(3, 4) = 9$, $R(3, 5) = 14$, $R(4, 4) = 18$。$R(5, 5)$ 的确切值至今未知，只知道在 43 到 48 之间。

## 应用

- **组合数学**：极值组合和结构 Ramsey 理论的核心工具
- **逻辑与计算机科学**：证明复杂性和自动定理证明中的应用
- **数论**：Schur 定理、van der Waerden 定理等算术 Ramsey 结果
- **几何**：Erdős–Szekeres 定理关于凸多边形

## 相关概念

- Ramsey 数 (Ramsey Number)：保证某种子结构存在的最小顶点数
- 团 (Clique)：两两相邻的顶点集
- 独立集 (Independent Set)：两两不相邻的顶点集
- 鸽巢原理 (Pigeonhole Principle)：Ramsey 理论的基本工具
- Erdős–Szekeres 定理：Ramsey 理论在几何中的经典应用

## 参考

### 教材

- [R. L. Graham, B. L. Rothschild, J. H. Spencer. Ramsey Theory. Wiley, 1990]
- [J. Fox. Lecture Notes on Graph Ramsey Theory]

### 论文

- [F. P. Ramsey. On a problem of formal logic. Proc. London Math. Soc., 1930]

### 在线资源

- [Mathlib4 - Ramsey](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Ramsey.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*
