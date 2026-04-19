---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: 容斥原理 (Inclusion-Exclusion Principle)
---
# 容斥原理 (Inclusion-Exclusion Principle)

## Mathlib4 引用

```lean
import Mathlib.Data.Finset.Basic\nimport Mathlib.Data.Set.Card\n\nnamespace Combinatorics\n\nvariable {α : Type*} [DecidableEq α] {s : Finset α} {f : α → Set β}\n\n/-- 容斥原理：有限个有限集合的并集大小 -/\ntheorem inclusion_exclusion {I : Finset α} (hfin : ∀ i ∈ I, (f i).Finite)\n    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (f i) (f j)) :\n    (⋃ i ∈ I, f i).ncard = ∑ t ∈ I.powerset, (-1 : ℤ)^(t.card + 1) * (⋂ i ∈ t, f i).ncard := by\n  -- 利用特征函数的加性和积性，或对集合归纳证明\n  sorry\n\nend Combinatorics
```

## 数学背景

容斥原理是组合数学和离散数学中最基本、最强大的计数原理之一，其历史可以追溯到17世纪的棣莫弗（De Moivre）和18世纪的西尔维斯特（Sylvester）。该原理提供了一种计算多个集合的并集大小的方法：当你想计算属于至少一个集合的元素个数时，可以先简单地将各集合的大小相加，然后减去两两交集的大小（因为这部分被重复计算了），再加上三个集合交集的大小（因为这部分被减多了），依此类推。形式化地，对有限集合 $A_1, A_2, \dots, A_n$：

$$\left| \bigcup_{{i=1}}^n A_i \right| = \sum_{{i}} |A_i| - \sum_{{i<j}} |A_i \cap A_j| + \sum_{{i<j<k}} |A_i \cap A_j \cap A_k| - \cdots + (-1)^{{n+1}} |A_1 \cap \cdots \cap A_n|$$

容斥原理在组合计数、数论（如计算与给定整数互素的数的个数）、概率论和算法分析中无处不在。

## 直观解释

容斥原理解决了一个非常常见的计数问题：当我们需要计算满足至少一个条件的对象数量时，如何避免重复计数？想象你要计算一个班级中至少会一种外语的学生人数。你知道会英语的有 20 人，会法语的有 15 人，会德语的有 10 人。如果直接把这三个数字相加，那些会两种语言的学生就被算了两次，会三种语言的甚至被算了三次！容斥原理教你如何修正这种重复：先减去会两种语言的人数（把重复的部分去掉），但这样会三种语言的学生被减多了，所以最后还要加回会三种语言的人数。这个"加、减、加、减..."的模式就是容斥原理的精髓。

## 形式化表述

设 $A_1, A_2, \dots, A_n$ 是有限集合，$U$ 是全集。则这些集合的并集大小为：

$$\left| \bigcup_{{i=1}}^n A_i \right| = \sum_{{k=1}}^n (-1)^{{k+1}} \sum_{{1 \leq i_1 < i_2 < \cdots < i_k \leq n}} \left| A_{{i_1}} \cap A_{{i_2}} \cap \cdots \cap A_{{i_k}} \right|$$

补集形式（计算不满足任何条件的元素数）：

$$\left| U \setminus \bigcup_{{i=1}}^n A_i \right| = |U| - \sum_{{i}} |A_i| + \sum_{{i<j}} |A_i \cap A_j| - \cdots + (-1)^n |A_1 \cap \cdots \cap A_n|$$

概率形式：对事件 $E_1, \dots, E_n$：

$$P\left( \bigcup_{{i=1}}^n E_i \right) = \sum_{{k=1}}^n (-1)^{{k+1}} \sum_{{i_1 < \cdots < i_k}} P(E_{{i_1}} \cap \cdots \cap E_{{i_k}})$$

其中：

- 公式中的 $(-1)^{{k+1}}$ 保证了第 $k$ 层交集的符号交替变化
- 该原理可以推广到测度论和抽象代数中的赋值

## 证明思路

1. **归纳法**：对 $n = 2$，$|A \cup B| = |A| + |B| - |A \cap B|$ 显然成立。假设对 $n-1$ 个集合成立，利用并的结合律和 $n=2$ 的情况推导 $n$ 的情况
2. **特征函数法**：对每个元素 $x \in U$，考虑它在左右两边的贡献。利用恒等式 $\mathbf{1}_{{\cup A_i}} = 1 - \prod (1 - \mathbf{1}_{{A_i}})$ 展开即得容斥公式
3. **Möbius 反演**：在子集格上定义 Möbius 函数，容斥原理是 Möbius 反演在布尔格上的特例
4. **生成函数法**：对分配格上的计数问题，容斥对应于生成函数中的对数-指数关系

核心洞察在于通过系统地在各阶交集之间切换来精确修正重复计数。

## 示例

### 示例 1：错排数

计算 $n$ 个元素的排列中没有任何元素保持原位（derangement）的个数。设 $A_i$ 为第 $i$ 个元素在原位的排列集合。由容斥原理：

$$D_n = n! \sum_{{k=0}}^n \frac{(-1)^k}{k!} \approx \frac{n!}{e}$$

### 示例 2：欧拉函数

$\varphi(n)$ 计数了不超过 $n$ 且与 $n$ 互素的正整数的个数。若 $n = p_1^{{a_1}} \cdots p_r^{{a_r}}$，由容斥原理：

$$\varphi(n) = n \prod_{{p|n}} \left(1 - \frac{1}{p}\right)$$

### 示例 3：染色多项式

图的染色多项式 $P_G(k)$ 可以用容斥原理表示：对每条边 $e$，设 $A_e$ 为 $e$ 的两个端点同色的染色方案集合。则合法染色数为 $|U| - |\cup A_e|$，展开后即得染色多项式。

## 应用

- **组合计数**：排列、组合和分配问题中的重复计数修正
- **数论**：欧拉函数、Möbius 反演和筛法
- **概率论**：多个事件并集的概率计算
- **图论**：染色多项式、匹配计数和网络可靠性
- **计算机科学**：算法分析、哈希碰撞概率和布尔满足性问题

## 相关概念

- 错排 (Derangement)：无不动点的排列
- Möbius 反演 (Möbius Inversion)：偏序集上的广义容斥
- 欧拉函数 (Euler's Totient Function)：与 $n$ 互素的整数个数
- 特征函数 (Indicator Function)：集合的 0-1 值函数
- 筛法 (Sieve Method)：数论中基于容斥的素数计数技术

## 参考

### 教材

- [R. P. Stanley. Enumerative Combinatorics, Vol. 1. Cambridge, 1997. Chapter 2]
- [M. Aigner. Combinatorial Theory. Springer, 1979. Chapter IV]

### 在线资源

- [Mathlib4 - Finset](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Basic.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*
