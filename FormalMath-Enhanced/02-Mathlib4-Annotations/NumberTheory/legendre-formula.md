---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: Legendre 公式 (Legendre's Formula)
---
# Legendre 公式 (Legendre's Formula)

## Mathlib4 引用

```lean
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

namespace NumberTheory

variable {n p : ℕ} (hp : Nat.Prime p)

/-- Legendre 公式：n! 中素数 p 的指数等于 Σ_{k=1}^∞ ⌊n / p^k⌋ -/
theorem legendre_formula :
    padicValNat p n.factorial = ∑ k in Finset.Ico 1 (Nat.log p n + 1), n / p^k := by
  -- 计算 1 到 n 中 p 的倍数、p² 的倍数等的个数并求和
  sorry

end NumberTheory
```

## 数学背景

Legendre 公式由法国数学家阿德里安-马里·勒让德（Adrien-Marie Legendre）于1808年证明，是初等数论中关于阶乘素因子分解的基本结果。该定理给出了计算 $n!$ 中某个素数 $p$ 的精确指数（即 $p$-adic 赋值）的方法：只需将 $n$ 除以 $p, p^2, p^3, \dots$ 后取整并求和。这个看似简单却非常实用的公式在组合数论、素数分布、p-adic 分析和二项式系数的素因子研究中具有核心地位。

## 直观解释

Legendre 公式提供了一个优雅而直观的计数方法。想象从 1 到 $n$ 的所有整数排成一排，我们要计算 $n!$ 中包含多少个因子 $p$。首先，每第 $p$ 个数至少贡献一个 $p$ 因子——共有 $\lfloor n/p \rfloor$ 个这样的数。但这还不够，因为每第 $p^2$ 个数实际上贡献了两个 $p$ 因子，我们在第一轮只算了一个，需要再补一个——有 $\lfloor n/p^2 \rfloor$ 个。同理，每第 $p^3$ 个数需要再补一个，依此类推。这就像剥洋葱一样，一层一层地剥去已经计数的 $p$ 因子，直到所有的 $p$ 因子都被精确计数为止。

## 形式化表述

设 $n$ 是正整数，$p$ 是素数，则 $n!$ 中素数 $p$ 的指数为：

$$v_p(n!) = \sum_{{k=1}}^\infty \left\lfloor \frac{n}{p^k} \right\rfloor = \left\lfloor \frac{n}{p} \right\rfloor + \left\lfloor \frac{n}{p^2} \right\rfloor + \left\lfloor \frac{n}{p^3} \right\rfloor + \cdots$$

其中：

- $v_p(n!)$ 表示 $p$ 在 $n!$ 的素因子分解中的指数（p-adic 赋值）
- $\lfloor x \rfloor$ 表示不超过 $x$ 的最大整数
- 求和实际上在 $p^k > n$ 时终止，因此只有有限项非零

等价地，Legendre 公式也可写成：

$$v_p(n!) = \frac{n - s_p(n)}{p - 1}$$

其中 $s_p(n)$ 是 $n$ 在 $p$ 进制下的各位数字之和。

## 证明思路

1. **计数 p 的倍数**：在 $\{1, 2, \dots, n\}$ 中，$p$ 的倍数有 $\lfloor n/p \rfloor$ 个，每个至少贡献一个 $p$ 因子
2. **计数 p² 的倍数**：$p^2$ 的倍数有 $\lfloor n/p^2 \rfloor$ 个，每个额外再贡献一个 $p$ 因子
3. **归纳推广**：对 $p^k$ 的倍数有 $\lfloor n/p^k \rfloor$ 个，每个在前 $k-1$ 轮已计 $k-1$ 个，本轮再补一个
4. **总和即得**：将所有轮次的贡献相加即得 $v_p(n!)$

核心洞察在于高次幂的倍数同时是低次幂的倍数，需要分层计数以避免遗漏。

## 示例

### 示例 1：100! 中 2 的指数

$v_2(100!) = \lfloor 100/2 \rfloor + \lfloor 100/4 \rfloor + \lfloor 100/8 \rfloor + \lfloor 100/16 \rfloor + \lfloor 100/32 \rfloor + \lfloor 100/64 \rfloor$
$= 50 + 25 + 12 + 6 + 3 + 1 = 97$。

### 示例 2：100! 中 5 的指数

$v_5(100!) = \lfloor 100/5 \rfloor + \lfloor 100/25 \rfloor = 20 + 4 = 24$。
这决定了 100! 末尾有多少个零（由 2 和 5 配对决定，这里是 24 个）。

### 示例 3：二项式系数

计算 $\binom{100}{50}$ 中素数 7 的指数：\n$v_7(\binom{100}{50}) = v_7(100!) - v_7(50!) - v_7(50!)$\n$= (14 + 2) - (7 + 1) - (7 + 1) = 16 - 8 - 8 = 0$。\n因此 $\binom{100}{50}$ 不被 7 整除。

## 应用

- **组合数论**：计算二项式系数和多项式系数的素因子分解
- **p-adic 分析**：p-adic 赋值和 p-adic 数的基础工具
- **素数分布**：素数阶乘（primorial）和切比雪夫函数的研究
- **算法竞赛**：快速计算阶乘末尾零的个数等问题
- **密码学**：大数模运算中的素因子分析

## 相关概念

- p-adic 赋值 (p-adic Valuation)：素数在整数分解中的指数
- 阶乘 (Factorial)：前 n 个正整数的乘积
- 取整函数 (Floor Function)：不超过实数的最大整数
- 二项式系数 (Binomial Coefficient)：$\binom{n}{k} = \frac{n!}{k!(n-k)!}$
- Kummer 定理：Legendre 公式在二项式系数上的推广

## 参考

### 教材

- [T. M. Apostol. Introduction to Analytic Number Theory. Springer, 1976. Chapter 3]
- [G. H. Hardy, E. M. Wright. An Introduction to the Theory of Numbers. Oxford, 6th edition, 2008. Chapter 22]

### 在线资源

- [Mathlib4 - padicValNat](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Padics/PadicVal.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*