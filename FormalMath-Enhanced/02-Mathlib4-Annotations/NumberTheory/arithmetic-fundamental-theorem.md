---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: 算术基本定理 (Fundamental Theorem of Arithmetic)
---
# 算术基本定理 (Fundamental Theorem of Arithmetic)

## Mathlib4 引用

```lean
import Mathlib.NumberTheory.Divisors

namespace NumberTheory

variable {n : ℕ} (hn : 1 < n)

/-- 算术基本定理：每个大于 1 的正整数都可唯一分解为素数的乘积（不计顺序） -/
theorem arithmetic_fundamental_theorem :
    ∃! (f : ℕ →₀ ℕ), n = ∏ p in f.support, p ^ f p := by
  -- 存在性由强归纳法证明，唯一性由欧几里得引理证明
  sorry

end NumberTheory
```

## 数学背景

算术基本定理，也称为唯一分解定理，是数论中最根本的定理之一。该定理断言：每个大于 1 的正整数都可以唯一地（不计素因子顺序）分解为素数的乘积。这一定理在古希腊数学中已有雏形（欧几里得《几何原本》中包含了存在性和唯一性的核心思想），但高斯在1801年的《算术研究》中首次给出了现代形式的严格陈述和证明。算术基本定理是整个整数环 $\mathbb{Z}$（以及更一般的唯一分解整环）理论的基石。

## 直观解释

算术基本定理就像化学中的元素周期律：正如任何物质都可以分解为不可再分的基本元素（原子），任何整数也可以分解为不可再分的素数。而且，就像水分解永远是 2 个氢原子和 1 个氧原子（不考虑同位素），整数的素因子分解也是唯一的——$60 = 2^2 \times 3 \times 5$，无论你用什么方法分解，最终都会得到完全相同的结果。这一定理揭示了整数世界的深层结构：素数是构成所有整数的"原子"，而整数的几乎所有算术性质都可以追溯到它的素因子分解。

## 形式化表述

每个大于 1 的正整数 $n$ 都可以唯一地表示为：

$$n = p_1^{{e_1}} p_2^{{e_2}} \cdots p_k^{{e_k}}$$

其中 $p_1 < p_2 < \cdots < p_k$ 是素数，$e_i \geq 1$ 是正整数。

唯一性的精确含义：若 $n = p_1^{{e_1}} \cdots p_k^{{e_k}} = q_1^{{f_1}} \cdots q_m^{{f_m}}$ 是两种素因子分解，则 $k = m$，且经过适当排列后有 $p_i = q_i$ 和 $e_i = f_i$。

其中：

- 素数（prime）是大于 1 且只有 1 和自身两个正因子的正整数
- $p_i^{{e_i}}$ 称为素数幂因子
- 这个分解在正整数范围内是唯一的

## 证明思路

1. **存在性**：用强归纳法。假设所有小于 $n$ 的正整数都可分解。若 $n$ 是素数，则分解就是它本身；若 $n$ 是合数，则 $n = ab$，$a, b < n$，由归纳假设 $a, b$ 都可分解，故 $n$ 也可分解
2. **欧几里得引理**：若素数 $p | ab$，则 $p | a$ 或 $p | b$
3. **唯一性**：假设 $n$ 有两种素因子分解，利用欧几里得引理逐步证明对应的素数和指数必须相同
4. **形式化表述**：Mathlib4 中用有限支撑函数（finsupp）来表示素因子分解

核心洞察在于素数的不可分性保证了分解的唯一性。

## 示例

### 示例 1：60 的素因子分解

$60 = 2 \times 30 = 2 \times 2 \times 15 = 2^2 \times 3 \times 5$。无论先用什么方法分解（如 $60 = 6 \times 10$），最终都会得到 $2^2 \times 3 \times 5$。

### 示例 2：GCD 与 LCM 的计算

利用唯一分解，$\gcd(a, b)$ 等于各公共素因子取最小指数的乘积，$\text{lcm}(a, b)$ 等于各素因子取最大指数的乘积。例如：$36 = 2^2 \times 3^2$，$60 = 2^2 \times 3 \times 5$，故 $\gcd = 2^2 \times 3 = 12$，$\text{lcm} = 2^2 \times 3^2 \times 5 = 180$。

### 示例 3：无理数证明

$\sqrt{2}$ 是无理数：假设 $\sqrt{2} = p/q$（最简分数），则 $2q^2 = p^2$。由唯一分解，左边 2 的指数是奇数，右边是偶数，矛盾。

## 应用

- **密码学**：RSA 等公钥算法基于大整数的素因子分解困难性
- **编码理论**：纠错码和哈希算法中的数论结构
- **抽象代数**：唯一分解整环（UFD）的定义和判别
- **解析数论**：黎曼假设和素数定理的研究基础
- **计算数论**：整数分解算法和素性检验的理论依据

## 相关概念

- 素数 (Prime Number)：大于 1 且不可再分解的整数
- 合数 (Composite Number)：可分解为更小正整数乘积的数
- 欧几里得引理 (Euclid's Lemma)：$p | ab \implies p | a$ 或 $p | b$
- 唯一分解整环 (UFD)：具有唯一素因子分解性质的整环
- 大整数分解 (Integer Factorization）：现代密码学的核心困难问题

## 参考

### 教材

- [G. H. Hardy, E. M. Wright. An Introduction to the Theory of Numbers. Oxford, 6th edition, 2008. Chapter 1]
- [K. Ireland, M. Rosen. A Classical Introduction to Modern Number Theory. Springer, 1990. Chapter 1]

### 在线资源

- [Mathlib4 - Nat Factorization](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Divisors.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*