---
msc_primary: 00A99
processed_at: '2026-04-15'
title: Burnside 引理 (Burnside's Lemma)
---
# Burnside 引理 (Burnside's Lemma)

## Mathlib4 引用

```lean
import Mathlib.GroupTheory.GroupAction.Basic\nimport Mathlib.Data.Set.Card\n\nnamespace GroupTheory\n\nvariable {G α : Type*} [Group G] [MulAction G α] [Finite G] [Finite α]\n\n/-- Burnside 引理：轨道数等于群中每个元素的不动点数的平均值 -/\ntheorem burnside_lemma :\n    (orbitSet G α).ncard = (1 / Fintype.card G) * ∑ g : G, (fixedPoints g).ncard := by\n  -- 利用轨道-稳定子定理和计数轨道中元素对 (g, x) 的双重计数证明\n  sorry\n\nend GroupTheory
```

## 数学背景

Burnside 引理（也称为 Burnside 计数定理或 Cauchy-Frobenius 引理）是群论和组合数学中的经典结果，尽管以英国数学家威廉·伯恩赛德（William Burnside）命名，但实际上是由法国数学家奥古斯丁-路易·柯西（Cauchy）和德国数学家费迪南德·弗罗贝尼乌斯（Ferdinand Frobenius）更早证明的。该引理提供了一个计算群作用下轨道数目的高效方法：轨道数等于群中每个元素的不动点数的平均值。形式化地，若有限群 $G$ 作用在有限集合 $X$ 上，则：

$$|X/G| = \frac{1}{|G|} \sum_{{g \in G}} |X^g|$$

其中 $X/G$ 是轨道集合，$X^g = \{x \in X : g \cdot x = x\}$ 是元素 $g$ 的不动点集。Burnside 引理是 Polya 计数定理的基础，在化学（分子同构计数）、物理学（晶体学中的对称性分类）和计算机科学（算法的不等价分类）中具有广泛应用。

## 直观解释

Burnside 引理提供了一个巧妙的方法来计算群作用下不同轨道的数量。想象你有一串珠子，可以用不同颜色来染色，但旋转后相同的染色方案被认为是等价的。直接数有多少种不等价的染色方案可能很困难，但 Burnside 引理告诉我们：你可以先考虑每一种对称操作（旋转、翻转），计算在该操作下保持不变的染色方案数，然后把这些数取平均。这个平均值就是不等价染色方案的总数！这就像要计算一个房间里有多少盏不同的灯，你不是直接数灯，而是对每种开关组合，数有多少盏灯的状态保持不变，然后取平均。之所以这个平均能给出正确答案，是因为每个轨道的贡献被精确地平衡了。

## 形式化表述

设 $G$ 是有限群，$X$ 是有限集合，$G$ 作用在 $X$ 上。则轨道数目为：

$$|X/G| = \frac{1}{|G|} \sum_{{g \in G}} |\text{Fix}(g)|$$

其中：

- $|X/G|$ 表示 $X$ 在 $G$ 作用下的轨道数
- $|G|$ 是群 $G$ 的阶（元素个数）
- $\text{Fix}(g) = \{x \in X : g \cdot x = x\}$ 是群元素 $g$ 的不动点集
- 求和遍历群 $G$ 中的所有元素

等价表述（按共轭类求和）：

$$|X/G| = \sum_{{C}} \frac{|C|}{|G|} |\text{Fix}(g_C)|$$

其中 $C$ 遍历 $G$ 的共轭类，$g_C$ 是共轭类 $C$ 的代表元。由于同一共轭类中的元素有相同的不动点数，这个形式在计算上往往更方便。

Polya 计数定理是 Burnside 引理的进一步推广，它不仅计数轨道数，还引入了生成函数来记录轨道中颜色分布的详细信息。

## 证明思路

1. **双重计数**：考虑集合 $S = \{(g, x) \in G \times X : g \cdot x = x\}$。一方面，对固定的 $g$，满足条件的 $x$ 有 $|\text{Fix}(g)|$ 个，故 $|S| = \sum_{{g \in G}} |\text{Fix}(g)|$。另一方面，对固定的 $x$，满足条件的 $g$ 构成稳定子群 $G_x$，由轨道-稳定子定理 $|G_x| = |G|/|G \cdot x|$\n2. **按轨道分类**：$|S| = \sum_{{x \in X}} |G_x| = \sum_{{\text{轨道 } O}} \sum_{{x \in O}} \frac{|G|}{|O|} = \sum_{{\text{轨道 } O}} |G| = |G| \cdot |X/G|$\n3. **等式两边比较**：$|G| \cdot |X/G| = \sum_{{g \in G}} |\text{Fix}(g)|$，两边除以 $|G|$ 即得 Burnside 引理\n4. **Polya 推广**：引入循环指标多项式，将不动点计数推广到带权重的计数

核心洞察在于通过交换求和顺序（先对 $g$ 求和 vs 先对 $x$ 求和），将轨道数与不动点数联系起来。

## 示例

### 示例 1：二面体群作用下的项链计数

用 $k$ 种颜色给 $n$ 颗珠子的项链染色，考虑旋转和翻转等价。二面体群 $D_n$ 有 $2n$ 个元素。由 Burnside 引理，不等价的项链数为：

$$N = \frac{1}{2n} \left( \sum_{{\text{旋转}}} k^{{\gcd(r,n)}} + \sum_{{\text{翻转}}} k^{{\lfloor (n+1)/2 \rfloor}} \right)$$

### 示例 2：立方体的面染色

用 $k$ 种颜色给立方体的 6 个面染色，考虑立方体的旋转群（同构于 $S_4$，24 个元素）。由 Burnside 引理，不等价的染色方案数为：

$$N = \frac{1}{24}(k^6 + 3k^4 + 12k^3 + 8k^2)$$

### 示例 3：分子同构计数

在化学中，计算具有给定分子式的不同有机分子的数目可以转化为在置换群作用下对图染色的轨道计数问题，Burnside 引理和 Polya 定理是标准工具。

## 应用

- **组合数学**：轨道计数、图枚举和不等价构型的分类
- **化学**：分子同构体、晶体结构和分子对称性的计数
- **物理学**：统计力学中的配分函数和对称性破缺
- **计算机科学**：算法等价类、数据结构规范和编译优化
- **音乐理论**：对称音阶和调式等价类的分类

## 相关概念

- 轨道 (Orbit)：群作用下元素的等价类
- 稳定子群 (Stabilizer)：保持某点不动的群元素子集
- 轨道-稳定子定理 (Orbit-Stabilizer Theorem)：$|G| = |G \cdot x| \cdot |G_x|$
- Polya 计数定理 (Pólya Enumeration Theorem)：Burnside 引理的生成函数推广
- 共轭类 (Conjugacy Class)：群中相互共轭的元素集合

## 参考

### 教材

- [M. Aigner. Combinatorial Theory. Springer, 1979. Chapter V]
- [J. H. van Lint, R. M. Wilson. A Course in Combinatorics. Cambridge, 1992. Chapter 35]

### 在线资源

- [Mathlib4 - GroupAction](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/GroupAction/Basic.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*
