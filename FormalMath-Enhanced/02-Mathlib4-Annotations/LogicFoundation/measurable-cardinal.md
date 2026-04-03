# 可测基数理论

## Mathlib4 引用

```lean
import Mathlib.SetTheory.Cardinal.Measurable

namespace SetTheory

/-- 可测基数的定义 -/
theorem measurable_cardinal_def
    {κ : Cardinal} :
    IsMeasurable κ ↔
      ∃ (μ : Set κ → Prop),
        IsNonprincipalUltrafilter μ ∧
        IsKappaComplete μ κ := by
  -- 可测基数存在κ-完全非主超滤
  rfl

/-- 可测基数蕴含不可达性 -/
theorem measurable_implies_inaccessible
    {κ : Cardinal} (hκ : IsMeasurable κ) :
    IsInaccessible κ := by
  -- 可测基数是不可达基数
  sorry

end SetTheory
```

## 数学背景

可测基数是第一个被研究的大基数，起源于测度论问题：是否存在定义在集合所有子集上的非平凡测度？Stanislaw Ulam在1930年证明这与基数理论密切相关——这样的测度存在的基数必须是"大"的（可测的）。可测基数位于大基数层级的底部，但已经超越了ZFC可证明存在性的范围。它是内模型理论的起点，也是决定公理（AD）研究的核心对象。可测基数的存在性为集合论宇宙提供了丰富的结构。

## 直观解释

可测基数是"大到可以被测量"的基数。想象一个无限集合——我们通常只能用可数可加测度来"测量"它。但对可测基数 $\kappa$，存在一个 $\kappa$-完全的非主超滤（等价于 $\{0,1\}$-值测度），可以区分 $\kappa$ 的几乎所有子集。这就像有一个"完美的天平"，能够精确判断任何子集是否"大"。可测基数的存在意味着集合论宇宙在非常高的层次上有丰富的对称性和结构。

## 形式化表述

**定义**：不可数基数 $\kappa$ 是**可测的**，若存在 $\kappa$-完全的非主超滤 $U$ 在 $\kappa$ 上。

**等价表述**：存在非平凡的 $\kappa$-可加 $\{0,1\}$-值测度 $\mu: \mathcal{P}(\kappa) \to \{0,1\}$。

**初等嵌入**：存在非平凡初等嵌入 $j: V \to M$，其中 $M$ 是传递类，且 $\kappa$ 是临界值（最小的使 $j(\alpha) \neq \alpha$ 的序数）。

**性质**：

- 可测基数是不可达的（正则且强极限）
- 可测基数是Mahlo的
- $L$ 中存在可测基数当且仅当 $0^\#$ 存在

## 证明思路

1. **超滤构造**：从测度构造超滤，反之亦然
2. **不可达性证明**：证明可测基数正则且强极限
3. **初等嵌入**：用超幂构造 $j: V \to \text{Ult}(V, U)$
4. **Los定理**：验证超幂的初等性
5. **一致性强度**：证明可测基数超越ZFC

## 示例

### 示例 1：不可测的基数

**问题**：证明 $\aleph_1$ 不是可测基数。

**解答**：

假设 $U$ 是 $\omega_1$-完全非主超滤。

对每个 $\alpha < \omega_1$，$\{\alpha\} \notin U$（非主）。

由 $\omega_1$-完全性：$\bigcup_{\alpha < \omega_1} \{\alpha\} = \omega_1 \notin U$。

矛盾！因此 $\omega_1$ 不可测。

### 示例 2：可测基数与决定性

**问题**：描述可测基数与射影决定性（PD）的关系。

**解答**：

Martin证明：可测基数蕴含 $\Pi^1_1$-决定性。

更高阶的射影决定性需要更大的大基数（如Woodin基数）。

大基数层级与描述集合论的确定性层级平行。

## 应用

- **内模型理论**：可测基数的典范内模型
- **描述集合论**：决定性公理的证明
- **实数正则性**：Lebesgue可测性和Baire性质
- **组合集合论**：划分关系
- **代数**：自由群的子群结构

## 相关概念

- [大基数层级](./large-cardinal-hierarchy.md)：可测基数的位置
- [超滤](./ultrafilter.md)：可测基数的定义工具
- [初等嵌入](./elementary-embedding.md)：可测基数的内省视角
- [不可达基数](./inaccessible-cardinal.md)：可测基数的必要条件
- [决定性公理](./axiom-of-determinacy.md)：可测基数的推论

## 参考

### 教材

- Kanamori, A. The Higher Infinite. Springer, 2003.
- Jech, T. Set Theory. Springer, 2003. Chapter 10

### 论文

- Ulam, S. Zur Maßtheorie in der allgemeinen Mengenlehre. Fund. Math., 16: 140-150, 1930.
- Scott, D. Measurable cardinals and constructible sets. Bull. Acad. Polon. Sci., 9: 521-524, 1961.

### 在线资源

- [Measurable Cardinal Wikipedia](https://en.wikipedia.org/wiki/Measurable_cardinal)
- [nLab - Measurable Cardinal](https://ncatlab.org/nlab/show/measurable+cardinal)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
