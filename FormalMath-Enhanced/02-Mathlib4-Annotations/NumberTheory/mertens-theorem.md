---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: Mertens定理 (Mertens' Theorems)
---
# Mertens定理 (Mertens' Theorems)

## Mathlib4 引用

```lean
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.PrimeCounting

namespace MertensTheorem

open ArithmeticFunction

/-- Mertens第一定理：素数和的渐近 -/
theorem mertens_first (n : ℕ) :
    ∑ p in (Finset.Iic n).filter Nat.Prime, Real.log p / p = Real.log n + O(1) := by
  -- 利用Stieltjes积分
  sorry

/-- Mertens第二定理：Mertens常数 -/
theorem mertens_second :
    Tendsto (fun n => ∑ p in (Finset.Iic n).filter Nat.Prime, 1 / p - Real.log (Real.log n))
      atTop (𝓝 M) := by
  -- 定义Mertens常数
  sorry

/-- Mertens第三定理：素数乘积的渐近 -/
theorem mertens_third (n : ℕ) (hn : 1 ≤ n) :
    ∏ p in (Finset.Iic n).filter Nat.Prime, (1 - 1 / p)⁻¹ ~[atTop] Real.log n := by
  -- 取对数转化为求和
  sorry

noncomputable def mertensConstant : ℝ :=
  lim (fun n => ∑ p in (Finset.Iic n).filter Nat.Prime, 1 / p - Real.log (Real.log n))

end MertensTheorem
```

## 数学背景

Mertens定理由Franz Mertens在1874年证明，是解析数论中关于素数分布的经典结果。这些定理给出了素数倒数和的精确渐近行为，以及形如 $\prod_{p \leq n}(1-1/p)^{-1}$ 的素数乘积的渐近公式。Mertens第二定理中的常数（现在称为Mertens常数或Meissel-Mertens常数）与Euler-Mascheroni常数类似，在数论中有许多应用。

## 直观解释

Mertens定理告诉我们：**素数虽然稀疏，但其倒数和以特定方式发散**。

想象素数像越来越稀疏的"里程碑"。虽然里程碑间隔越来越大，但如果把到第 $n$ 个里程碑的"倒数贡献"加起来，这个和以 $\log\log n$ 的速度缓慢增长。Mertens定理精确描述了这种增长，并定义了一个类似于Euler常数的重要常数。

## 形式化表述

**Mertens第一定理**：
$$\sum_{p \leq x} \frac{\log p}{p} = \log x + O(1)$$

**Mertens第二定理**：
$$\sum_{p \leq x} \frac{1}{p} = \log\log x + M + O\left(\frac{1}{\log x}\right)$$

其中 $M \approx 0.261497$ 是Mertens常数。

**Mertens第三定理**：
$$\prod_{p \leq x} \left(1 - \frac{1}{p}\right)^{-1} \sim e^\gamma \log x$$

其中 $\gamma$ 是Euler-Mascheroni常数。

## 证明思路

1. **Abel求和**：
   - 利用 $\sum_{p \leq x} \log p = \vartheta(x) \sim x$
   - Abel分部求和转化和式

2. **分部求和**：
   - $\sum_{p \leq x} \frac{\log p}{p} = \frac{\vartheta(x)}{x} + \int_2^x \frac{\vartheta(t)}{t^2} dt$
   - 利用 $\vartheta(t) = t + O(t/\log t)$

3. **收敛性**：
   - 证明 $\sum_{p \leq x} \frac{1}{p} - \log\log x$ 收敛
   - 极限定义为Mertens常数

核心洞察是素数定理给出的 $\vartheta(x)$ 的渐近行为。

## 示例

### 示例 1：数值计算

$n = 100$：$\sum_{p \leq 100} 1/p \approx 1.97$

$\log\log 100 \approx \log(4.6) \approx 1.53$

$M \approx 1.97 - 1.53 = 0.44$（近似值，大 $n$ 时收敛到 $0.261$）

### 示例 2：素数乘积

$\prod_{p \leq 100} (1-1/p)^{-1} \approx 5.54$

$e^\gamma \log 100 \approx 1.78 \times 4.6 \approx 8.2$（大 $n$ 时逼近）

### 示例 3：与Euler乘积的联系

$\prod_p (1-1/p)^{-1} = \sum_{n=1}^\infty 1/n = \infty$（调和级数）

Mertens第三定理给出了部分乘积的精确渐近。

## 应用

- **解析数论**：算术函数的均值
- **概率数论**：随机整数的分布
- **计算数论**：素数筛法的分析
- **代数数论**：类数公式
- **信息论**：素数编码的效率

## 相关概念

- Mertens常数 (Mertens Constant)：$M \approx 0.261497$
- Euler-Mascheroni常数 (Euler-Mascheroni Constant)：$\gamma \approx 0.577$
- Abel求和 (Abel Summation)：分部求和技巧
- Chebyshev函数 (Chebyshev Function)：$\vartheta(x)$
- [素数定理 (Prime Number Theorem)](./prime-number-theorem.md)：$\pi(x)$ 的渐近

## 参考

### 教材

- [Davenport. Multiplicative Number Theory. Springer, 3rd edition, 2000. Chapter 2]
- [Hardy & Wright. An Introduction to the Theory of Numbers. Oxford, 1979. Chapter 22]

### 历史文献

- [Mertens. Ein Beitrag zur analytischen Zahlentheorie. 1874]

### 在线资源

- [Mathlib4 文档 - ArithmeticFunction][https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ArithmeticFunction.html](需更新)
- [Wikipedia - Mertens' Theorems](https://en.wikipedia.org/wiki/Mertens%27_theorems)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
