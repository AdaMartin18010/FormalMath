---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: Möbius 反演定理 (Möbius Inversion Theorem)
---
# Möbius 反演定理 (Möbius Inversion Theorem)

## Mathlib4 引用

```lean
import Mathlib.NumberTheory.Moebius

namespace NumberTheory

variable {f g : ℕ → ℝ}

/-- Möbius 反演定理：若 g(n) = Σ_{d|n} f(d)，则 f(n) = Σ_{d|n} μ(d) g(n/d) -/
theorem moebius_inversion (h : ∀ n, g n = ∑ d in n.divisors, f d) :
    ∀ n, f n = ∑ d in n.divisors, moebius d * g (n / d) := by
  -- 利用 Dirichlet 卷积和 Möbius 函数是常数函数 1 的 Dirichlet 逆
  sorry

end NumberTheory
```

## 数学背景

Möbius 反演定理是数论和组合数学中的经典结果，由德国数学家奥古斯特·费迪南德·莫比乌斯（August Ferdinand Möbius）于1832年引入。该定理提供了一种在数论函数之间进行相互转换的强大工具：如果一个函数 $g(n)$ 可以表示为另一个函数 $f(d)$ 在所有 $n$ 的因子 $d$ 上的和，那么 $f(n)$ 也可以通过 $g$ 和 Möbius 函数 $\mu$ 的加权和来恢复。这一定理在解析数论、组合计数、信息论和图论中有广泛应用，是理解算术函数代数结构的核心结果。

## 直观解释

Möbius 反演定理可以看作是一种"筛法"的数学表达。想象你有一群人，$g(n)$ 表示所有编号是 $n$ 的倍数的人所做的贡献总和。问题是：如何从中恢复出编号恰好为 $n$ 的那个人的原始贡献 $f(n)$？Möbius 反演定理告诉我们：可以通过一个巧妙的包含-排除过程来实现——对于 $n$ 的每个因子 $d$，根据 $d$ 的不同素因子个数决定是加还是减 $g(n/d)$。如果 $d$ 有偶数个不同素因子就加，奇数个就减，有平方因子就不算。这正是 Möbius 函数 $\mu(d)$ 的取值规则。

## 形式化表述

设 $f, g$ 是定义在正整数上的算术函数，若对所有正整数 $n$ 有：

$$g(n) = \sum_{{d | n}} f(d)$$

则 Möbius 反演公式给出：

$$f(n) = \sum_{{d | n}} \mu(d) \cdot g\left(\frac{n}{d}\right)$$

等价地，用 Dirichlet 卷积表示：

$$g = f * 1 \iff f = g * \mu$$

其中 Möbius 函数 $\mu(n)$ 定义为：

$$\mu(n) = \begin{cases} 1 & n = 1 \\ (-1)^k & n \text{ 是 } k \text{ 个不同素数的乘积} \\ 0 & n \text{ 含有平方因子} \end{cases}$$

且 $1(n) = 1$ 对所有 $n$ 成立。

## 证明思路

1. **Dirichlet 卷积**：定义 $(f * g)(n) = \sum_{{d|n}} f(d) g(n/d)$，这是算术函数上的交换结合运算
2. **Möbius 函数的性质**：$\mu * 1 = \delta$，其中 $\delta(1) = 1$，$\delta(n) = 0$（$n > 1$）是 Dirichlet 卷积的单位元
3. **卷积反演**：由 $g = f * 1$ 两边卷积 $\mu$ 得 $g * \mu = f * (1 * \mu) = f * \delta = f$
4. **展开即得**：$f(n) = \sum_{{d|n}} \mu(d) g(n/d)$

核心洞察在于 Möbius 函数是普通求和运算在 Dirichlet 卷积下的逆元。

## 示例

### 示例 1：Euler totient 函数

已知 $\sum_{{d|n}} \varphi(d) = n$。由 Möbius 反演：\n$\varphi(n) = \sum_{{d|n}} \mu(d) \cdot \frac{n}{d} = n \prod_{{p|n}} (1 - \frac{1}{p})$。

### 示例 2：素数计数

设 $\pi(x)$ 为不超过 $x$ 的素数个数，$\Pi(x) = \sum_{{p^k \leq x}} \frac{1}{k}$。Möbius 反演在素数分布的显式公式中起着重要作用。

### 示例 3：图计数

在计数有标号图时，设 $g(n)$ 为所有 $n$ 顶点图的数量，$f(n)$ 为连通 $n$ 顶点图的数量。则有 $g(n) = \sum_{{k|n}} \binom{n}{k} f(k) g(n-k)$ 的变体，Möbius 反演可用于提取 $f(n)$。

## 应用

- **解析数论**：素数分布、Dirichlet 特征和 L-函数的研究
- **组合数学**：计数问题中的包含-排除原理和 sieve 方法
- **信息论**：信源编码和信道容量的 Möbius 反演公式
- **图论**：连通图计数和色多项式的计算
- **格论**：偏序集上的 Möbius 反演的一般化

## 相关概念

- Möbius 函数 (Möbius Function)：数论中的基本算术函数
- Dirichlet 卷积 (Dirichlet Convolution)：算术函数间的二元运算
- 算术函数 (Arithmetic Function)：定义在正整数上的函数
- Euler totient 函数 (Euler's Totient Function)：Möbius 反演的经典应用
- 包含-排除原理 (Inclusion-Exclusion Principle)：Möbius 反演的组合原型

## 参考

### 教材

- [T. M. Apostol. Introduction to Analytic Number Theory. Springer, 1976. Chapter 2]
- [G. H. Hardy, E. M. Wright. An Introduction to the Theory of Numbers. Oxford, 6th edition, 2008. Chapter 16]

### 在线资源

- [Mathlib4 - Moebius](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Moebius.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*