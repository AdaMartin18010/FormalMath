---
msc_primary: 00A99
processed_at: '2026-04-03'
title: 素数定理 (Prime Number Theorem)
---
# 素数定理 (Prime Number Theorem)

## Mathlib4 引用

```lean
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Primorial

namespace Nat

/-- 素数定理：$\pi(x) \sim \frac{x}{\ln x}$ -/
theorem primeNumberTheorem :
    Filter.Tendsto (fun x => (primeCounting x : ℝ) * Real.log x / x)
      Filter.atTop (nhds 1) := by
  -- 依赖于复分析和解析数论
  sorry

/-- 等价形式：第 n 个素数 $p_n \sim n \ln n$ -/
theorem nthPrimeApprox (n : ℕ) :
    nthPrime n ∼[atTop] n * Real.log n := by
  sorry

end Nat
```

## 数学背景

素数定理是数论中最重要和最优美的结果之一，描述了素数在自然数中的分布规律。高斯和勒让德在18世纪末通过数值观察提出猜想，但直到1896年才由雅克·阿达马（Jacques Hadamard）和查尔斯·让·德拉瓦莱·普森（Charles Jean de la Vallée Poussin）独立证明。这一证明标志着解析数论的诞生。

## 直观解释

素数定理告诉我们：**不超过 $x$ 的素数个数大约为 $\frac{x}{\ln x}$**。换句话说，一个随机选取的 $n$ 位整数是素数的概率约为 $\frac{1}{n \ln 10}$。

这解释了为什么素数越来越"稀疏"——随着数字增大，素数间隔趋于增大，但这种稀疏化遵循精确的对数规律。尽管素数分布看似不规则，但整体上却展现出惊人的规律性。

## 形式化表述

设 $\pi(x)$ 表示不超过 $x$ 的素数个数，则：

$$\pi(x) \sim \frac{x}{\ln x}$$

等价表述：

$$\lim_{x \to \infty} \frac{\pi(x)}{x / \ln x} = 1$$

更精确的估计包含误差项：

$$\pi(x) = \text{Li}(x) + O\left(x e^{-c\sqrt{\ln x}}\right)$$

其中 $\text{Li}(x) = \int_2^x \frac{dt}{\ln t}$ 是对数积分。

## 证明思路

1. **黎曼 $\zeta$ 函数**：定义 $\zeta(s) = \sum_{n=1}^{\infty} n^{-s}$
2. **欧拉乘积**：$\zeta(s) = \prod_p (1 - p^{-s})^{-1}$
3. **解析延拓**：将 $\zeta$ 延拓到 $\text{Re}(s) > 0$（除 $s = 1$）
4. **非零区域**：证明 $\zeta(s) \neq 0$ 对 $\text{Re}(s) \geq 1$
5. **围道积分**：利用 $\frac{\zeta'(s)}{\zeta(s)}$ 和围道积分提取 $\pi(x)$

核心是黎曼 $\zeta$ 函数的解析性质和复变函数技巧。

## 示例

### 示例 1：数值验证

计算 $\pi(10^6) = 78498$。

近似：$\frac{10^6}{\ln(10^6)} = \frac{10^6}{6\ln 10} \approx 72382$

比值：$\frac{78498}{72382} \approx 1.084$

更精确的对数积分：$\text{Li}(10^6) \approx 78628$

比值：$\frac{78498}{78628} \approx 0.998$（更接近 1）

### 示例 2：素数密度

10 位整数中素数的比例约为 $\frac{1}{\ln(10^{10})} = \frac{1}{10 \ln 10} \approx \frac{1}{23}$

随机选取一个 10 位整数，它是素数的概率约为 4.3%。

### 示例 3：素数间隙

平均素数间隙约为 $\ln p$。在 $10^6$ 附近：

平均间隙 $\approx \ln(10^6) \approx 13.8$

实际观察到的间隙与此相符。

## 应用

- **密码学**：RSA 加密的安全性依赖于大素数的分布
- **随机算法**：素性测试算法的设计
- **计算复杂性**：素数判定和因子分解的复杂度
- **量子计算**：Shor 算法的分析基础
- **音乐理论**：某些音律与素数分布的联系

## 相关概念

- [切比雪夫函数 (Chebyshev Functions)](./chebyshev-functions.md)：$\psi(x)$ 和 $\vartheta(x)$
- [黎曼假设 (Riemann Hypothesis)](./riemann-hypothesis.md)：关于 $\zeta$ 函数零点的著名猜想
- [算术级数中的素数 (Primes in Arithmetic Progression)](./dirichlet-theorem.md)：狄利克雷定理
- [孪生素数猜想 (Twin Prime Conjecture)](./twin-prime-conjecture.md)：无限多对 $p, p+2$ 都是素数
- [梅森素数 (Mersenne Primes)](./mersenne-primes.md)：形如 $2^p - 1$ 的素数

## 参考

### 教材

- [Davenport. Multiplicative Number Theory. Springer, 3rd edition, 2000. Chapter 18]
- [Apostol. Introduction to Analytic Number Theory. Springer, 1976. Chapter 13]

### 历史文献

- [Hadamard. Sur la distribution des zéros de la fonction ζ(s). 1896]
- [de la Vallée Poussin. Recherches analytiques sur la théorie des nombres premiers. 1896]

### 在线资源

- [Mathlib4 文档 - PrimeCounting](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/PrimeCounting.html)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
