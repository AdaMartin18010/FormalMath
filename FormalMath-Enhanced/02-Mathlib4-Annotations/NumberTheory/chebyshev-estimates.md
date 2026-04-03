---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# Chebyshev估计 (Chebyshev Estimates)

## Mathlib4 引用

```lean
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.VonMangoldt

namespace ChebyshevEstimates

open ArithmeticFunction

/-- Chebyshevθ函数 -/
def chebyshevTheta (x : ℝ) : ℝ := ∑ p in (Finset.Iic ⌊x⌋).filter Nat.Prime, Real.log p

/-- Chebyshevψ函数 -/
def chebyshevPsi (x : ℝ) : ℝ := ∑ n in Finset.Iic ⌊x⌋, vonMangoldt n

/-- Chebyshev第一不等式：π(x)的下界 -/
theorem chebyshev_lower_bound (x : ℝ) (hx : 2 ≤ x) :
    ∃ c > 0, c * x / Real.log x ≤ Nat.primeCounting ⌊x⌋ := by
  -- 利用θ函数的性质
  sorry

/-- Chebyshev第二不等式：π(x)的上界 -/
theorem chebyshev_upper_bound (x : ℝ) (hx : 2 ≤ x) :
    ∃ C, Nat.primeCounting ⌊x⌋ ≤ C * x / Real.log x := by
  sorry

/-- 素数定理的弱形式：π(x) ~ x/log x -/
theorem weak_prime_number_theorem :
    Nat.primeCounting ⌊x⌋ = Θ(x / Real.log x) := by
  -- Chebyshev上下界的组合
  sorry

end ChebyshevEstimates
```

## 数学背景

Chebyshev估计是Pafnuty Chebyshev在1850年代证明的结果，是素数定理证明的重要步骤。Chebyshev证明了素数计数函数 $\pi(x)$ 的增长阶是 $x/\log x$，虽然没有证明极限存在（这需要Hadamard和de la Vallée Poussin在1896年的工作）。这些估计在解析数论中仍然有用，提供了素数分布的定量信息。

## 直观解释

Chebyshev估计告诉我们：**素数的分布大致像 $x/\log x$ 那样增长**。

想象素数像散落的珍珠。Chebyshev证明了在数 $x$ 之前的素数个数约等于 $x/\log x$。虽然不如精确的素数定理，但这已经是非常强的结果——它确定了素数分布的正确数量级，排除了像 $x/(\log x)^2$ 或 $x/\sqrt{\log x}$ 这样的错误猜测。

## 形式化表述

设 $\pi(x) = \sum_{p \leq x} 1$ 是素数计数函数。

**Chebyshev估计**：
$$\frac{cx}{\log x} \leq \pi(x) \leq \frac{Cx}{\log x}$$

对足够大的 $x$，其中 $c, C > 0$ 是常数。

**关键函数**：

- $\vartheta(x) = \sum_{p \leq x} \log p$（Chebyshev theta函数）
- $\psi(x) = \sum_{n \leq x} \Lambda(n)$（Chebyshev psi函数，$\Lambda$ 是von Mangoldt函数）

**等价形式**：$\vartheta(x) \asymp x$，$\psi(x) \asymp x$

## 证明思路

1. **阶乘分析**：
   - $\log(n!) = \sum_{p \leq n} \sum_{k \geq 1} \lfloor n/p^k \rfloor \log p$
   - 用Stirling公式估计 $\log(n!)$

2. **比较论证**：
   - 上界：$\binom{2n}{n} < 4^n$，分析素因子
   - 下界：$\text{lcm}(1, 2, \ldots, n) \geq 2^n$

3. **函数关系**：
   - $\psi(x) - \vartheta(x) = O(\sqrt{x})$
   - 转化为 $\pi(x)$ 的估计

核心洞察是阶乘的素因子分解与二项式系数的组合性质。

## 示例

### 示例 1：数值验证

$x = 1000$：$\pi(1000) = 168$

$x/\log x \approx 1000/6.9 \approx 145$

比值 $\pi(x)\log x/x \approx 1.16$，在Chebyshev界限内。

### 示例 2：Bertrand假设

Chebyshev证明了Bertrand假设：对 $n > 1$，存在素数 $p$ 使 $n < p < 2n$。

这是他的估计的直接推论。

### 示例 3：常数确定

Chebyshev得到：$0.92 < \frac{\pi(x)\log x}{x} < 1.11$（对大 $x$）。

后来的工作将界限收紧到接近1（素数定理）。

## 应用

- **素数定理**：证明 $\pi(x) \sim x/\log x$ 的第一步
- **Bertrand假设**：$(n, 2n)$ 中必有素数
- **解析数论**：各种素数分布问题的定量结果
- **密码学**：素数生成的效率分析
- **计算复杂性**：素性测试的复杂度

## 相关概念

- [素数计数函数 (Prime Counting Function)](./prime-counting-function.md)：$\pi(x)$
- [von Mangoldt函数 (von Mangoldt Function)](./von-mangoldt-function.md)：$\Lambda(n)$
- [素数定理 (Prime Number Theorem)](./prime-number-theorem.md)：$\pi(x)$ 的渐近公式
- [Bertrand假设 (Bertrand's Postulate)](./bertrands-postulate.md)：区间内必有素数
- [Stirling公式 (Stirling's Formula)](./stirling-formula.md)：阶乘的渐近

## 参考

### 教材

- [Davenport. Multiplicative Number Theory. Springer, 3rd edition, 2000. Chapter 2]
- [Apostol. Introduction to Analytic Number Theory. Springer, 1976. Chapter 4]

### 历史文献

- [Chebyshev. Sur la fonction qui détermine la totalité des nombres premiers. 1852]

### 在线资源

- [Mathlib4 文档 - PrimeCounting](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/PrimeCounting.html)
- [Wikipedia - Prime Number Theorem](https://en.wikipedia.org/wiki/Prime_number_theorem)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
