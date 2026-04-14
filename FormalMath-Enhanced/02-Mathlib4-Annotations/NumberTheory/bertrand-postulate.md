---
msc_primary: 00A99
processed_at: '2026-04-15'
title: Bertrand 假设 (Bertrand's Postulate)
---
# Bertrand 假设 (Bertrand's Postulate)

## Mathlib4 引用

```lean
import Mathlib.NumberTheory.Bertrand

namespace BertrandPostulate

/-- Bertrand 假设：对任意 n > 1，n 与 2n 之间必存在素数 -/
theorem bertrand (n : ℕ) (hn : 1 < n) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p < 2 * n := by
  -- 基于切比雪夫估计和中心二项式系数分析的经典证明
  sorry

end BertrandPostulate
```

## 数学背景

Bertrand 假设由法国数学家约瑟夫·贝特朗（Joseph Bertrand）于1845年通过数值验证提出猜想。俄罗斯数学家帕夫努季·切比雪夫（Pafnuty Chebyshev）于1850年首次给出了严格证明，因此该假设有时也被称为**切比雪夫定理**。尽管素数定理的渐进结果已经蕴含了 Bertrand 假设（对充分大的 $n$），但切比雪夫的初等证明仍然具有重要的教学价值。保罗·埃尔德什在1932年以极其简洁的初等方法重新证明了这一定理，震惊了整个数学界。

## 直观解释

Bertrand 假设断言：**对于任意大于 1 的整数 $n$，在 $n$ 和 $2n$ 之间总存在至少一个素数**。

这意味着素数的分布不会过于稀疏——素数之间的间隙永远不会超过它自身的大小。想象在数轴上散步，每当你走到某个位置 $n$，你都不需要担心前方 $2n$ 处的"沙漠"太长，因为保证会有一颗"素数绿洲"藏在 $n$ 和 $2n$ 之间。这一结果虽然看起来直观，但在 $n$ 很大时，$2n$ 相比于 $n$ 只"远了一倍"，要证明其间必有素数却需要精妙的数论技巧。

## 形式化表述

对任意整数 $n > 1$，存在素数 $p$ 使得：

$$n < p < 2n$$

### 等价表述

对任意整数 $n \\ge 1$，存在素数 $p$ 使得 $n < p \\le 2n$。

## 证明思路

埃尔德什的初等证明堪称经典：

1. **中心二项式系数**：考虑 $\\binom{2n}{n}$，证明它在 $n$ 很大时具有足够多的素因子
2. **素数幂次估计**：对 $\\binom{2n}{n}$ 的素因数分解中每个素数的幂次进行上界估计
3. **反证法**：假设 $n$ 与 $2n$ 之间没有素数，则 $\\binom{2n}{n}$ 的所有素因子都不超过 $n$
4. **矛盾导出**：通过精细的组合与数论估计，证明这种情况下 $\\binom{2n}{n}$ 的素因子乘积无法达到其真实大小，从而导出矛盾

切比雪夫的原始证明则依赖于对 $\\vartheta(x) = \\sum_{p \\le x} \\ln p$ 的上下界估计。

## 示例

### 示例 1：$n = 10$

在 10 和 20 之间的素数为 11, 13, 17, 19。

Bertrand 假设保证至少存在一个，实际有 4 个。

### 示例 2：$n = 100$

在 100 和 200 之间的素数有 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199，共 21 个。

### 示例 3：$n = 2^k$ 的情形

对于 $n = 2^k$，Bertrand 假设保证在 $2^k$ 和 $2^{k+1}$ 之间存在素数。这直接蕴含了素数有无穷多个——因为从每个区间 $(2^k, 2^{k+1})$ 中都能取出一个不同的素数。

## 应用

- **素数分布理论**：素数间隙的上界估计
- **算法分析**：与素数筛法和哈希表大小选择相关
- **组合数论**：二项式系数素因子结构的经典应用
- **信息论**：某些编码构造中素数存在性的保证
- **计算复杂性**：随机算法和素性测试的理论基础

## 相关概念

- [素数定理 (Prime Number Theorem)](./prime-number-theorem.md)：描述素数渐进分布的更深层次结果
- 切比雪夫函数 (Chebyshev Functions)：$\\vartheta(x)$ 和 $\\psi(x)$
- 中心二项式系数 (Central Binomial Coefficient)：$\\binom{2n}{n}$
- [Bertrand 假设的强化形式](./bertrand-postulate.md)：如存在素数 $p$ 满足 $n < p < (1 + \\epsilon)n$（对充分大的 $n$）
- [狄利克雷定理 (Dirichlet's Theorem)](./dirichlet-theorem-arithmetic-progression.md)：等差数列中的素数分布

## 参考

### 教材

- [Apostol. Introduction to Analytic Number Theory. Springer, 1976. Chapter 8]
- [Nathanson. Elementary Methods in Number Theory. Springer, 2000. Chapter 8]

### 历史文献

- [Chebyshev. Mémoire sur les nombres premiers. 1850]
- [Erdős. Beweis eines Satzes von Tschebyschef. 1932]

### 在线资源

- [Mathlib4 文档 - Bertrand][https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Bertrand.html]

---

*最后更新：2026-04-15 | 版本：v1.0.0*
