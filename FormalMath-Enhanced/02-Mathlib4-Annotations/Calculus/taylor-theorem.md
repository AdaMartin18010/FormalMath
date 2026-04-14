---
msc_primary: 00A99
processed_at: '2026-04-03'
title: Taylor定理 (Taylor's Theorem)
---
# Taylor定理 (Taylor's Theorem)

## Mathlib4 引用

```lean
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.Deriv.Polynomial

namespace Taylor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Taylor定理带Lagrange余项 -/
theorem taylor_theorem_lagrange (f : ℝ → E) (n : ℕ) (a b : ℝ)
    (hf : ContDiffOn ℝ (n + 1) f (Icc a b)) :
    ∃ c ∈ Ioo a b, f b = ∑ k in range (n + 1), (b - a)^k / k! • (iteratedDeriv k f a) +
      (b - a)^(n + 1) / (n + 1)! • (iteratedDeriv (n + 1) f c) := by
  -- 使用Cauchy中值定理逐步构造
  sorry

/-- Taylor定理带积分余项 -/
theorem taylor_theorem_integral (f : ℝ → E) (n : ℕ) (a b : ℝ)
    (hf : ContDiffOn ℝ (n + 1) f (Icc a b)) :
    f b = ∑ k in range (n + 1), (b - a)^k / k! • (iteratedDeriv k f a) +
      ∫ t in a..b, (b - t)^n / n! • (iteratedDeriv (n + 1) f t) := by
  -- 分部积分得到积分余项
  sorry

end Taylor
```

## 数学背景

Taylor定理以布鲁克·泰勒（Brook Taylor）命名，他在1715年的著作《正的和反的增量方法》中首次发表了这一定理。然而，余项的研究则由后来的数学家（如拉格朗日、柯西）完成。该定理是数学分析中最重要的工具之一，将复杂函数局部近似为多项式。

## 直观解释

Taylor定理告诉我们：**光滑函数在某点附近可以近似为多项式**。就像用越来越精细的"镜头"观察函数，高阶Taylor多项式捕捉更多的局部行为。余项告诉我们近似的误差有多大。

## 形式化表述

设 $f$ 在包含 $a$ 的区间上有 $n+1$ 阶连续导数，则：

$$f(x) = \sum_{k=0}^n \frac{f^{(k)}(a)}{k!}(x-a)^k + R_n(x)$$

**Lagrange余项**：$R_n(x) = \frac{f^{(n+1)}(\xi)}{(n+1)!}(x-a)^{n+1}$，其中 $\xi$ 在 $a$ 和 $x$ 之间

**积分余项**：$R_n(x) = \int_a^x \frac{f^{(n+1)}(t)}{n!}(x-t)^n dt$

## 证明思路

1. **构造辅助函数**：定义包含Taylor多项式和余项的函数
2. **反复应用中值定理**：利用Rolle定理或Cauchy中值定理
3. **控制余项**：估计余项的大小
4. **极限论证**：当 $n \to \infty$ 时得到Taylor级数

## 示例

### 示例 1：指数函数

$e^x = \sum_{k=0}^n \frac{x^k}{k!} + \frac{e^\xi}{(n+1)!}x^{n+1}$

对所有 $x$ 收敛到 $e^x$。

### 示例 2：正弦函数

$\sin x = x - \frac{x^3}{3!} + \frac{x^5}{5!} - \cdots + R_n(x)$

奇函数，只有奇次幂。

## 应用

- **数值分析**：函数逼近、数值积分
- **物理学**：小振动近似、摄动理论
- **优化理论**：二阶条件、牛顿法
- **概率论**：特征函数展开

## 相关概念

- Taylor级数：无穷级数展开
- Maclaurin级数：在0点的Taylor展开
- 解析函数：可展开为Taylor级数的函数
- Padé逼近：有理函数逼近

## 参考

### 教材

- [Apostol. Calculus, Vol. 1. Wiley, 2nd edition, 1967. Chapter 7]
- [Rudin. Principles of Mathematical Analysis. McGraw-Hill, 1976. Chapter 5]

### 历史文献

- [Taylor. Methodus Incrementorum Directa et Inversa. 1715]

### 在线资源

- [Mathlib4 文档 - Taylor][https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/Taylor.html](需更新)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
