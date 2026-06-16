---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: 期望的线性性 (Linearity of Expectation)
---
# 期望的线性性 (Linearity of Expectation)

## Mathlib4 引用

```lean
import Mathlib.MeasureTheory.Integral.Bochner

namespace MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X Y : Ω → ℝ} (hX : Integrable X P) (hY : Integrable Y P)

/-- 期望的线性性：E[X + Y] = E[X] + E[Y] -/
theorem expectation_add :
    expectation (X + Y) P = expectation X P + expectation Y P := by
  -- 由积分的线性性直接得到
  sorry

/-- 期望的数乘性：E[cX] = cE[X] -/
theorem expectation_smul (c : ℝ) :
    expectation (c • X) P = c * expectation X P := by
  -- 由积分的齐次性直接得到
  sorry

end MeasureTheory
```

## 数学背景

期望的线性性是概率论和测度论中最基本、最常用的性质之一。该性质断言：随机变量之和的期望等于各自期望之和，即 E[X + Y] = E[X] + E[Y]。这一结论的惊人之处在于它完全不需要 X 和 Y 具有任何独立性或其他关系。

## 直观解释

期望的线性性可以看作是一种平均值的分配律。想象你和你的朋友一起经营两家公司，总利润的平均值必然等于两家公司各自平均利润之和——无论两家公司的业绩是互相促进还是此消彼长。这个看似平凡的性质在概率论中却威力无穷。

## 形式化表述

设 $X$ 和 $Y$ 是同一概率空间上的随机变量，$a, b \in \mathbb{{R}}$ 是常数，则：

$$\mathbb{E}[aX + bY] = a\mathbb{E}[X] + b\mathbb{E}[Y]$$

更一般地，对任意有限个随机变量 $X_1, X_2, \dots, X_n$ 和常数 $c_1, c_2, \dots, c_n$：

$$\mathbb{E}\left[\sum_{{i=1}}^n c_i X_i\right] = \sum_{{i=1}}^n c_i \mathbb{E}[X_i]$$

其中：

- $\mathbb{E}[X]$ 表示随机变量 $X$ 的数学期望
- 此性质不要求 $X_i$ 之间相互独立
- 此性质成立的前提是各个期望 $\mathbb{E}[X_i]$ 均存在

## 证明思路

1. **积分线性性**：期望本质上是关于概率测度的积分，而积分具有线性性
2. **离散情形**：$\mathbb{E}[X+Y] = \sum_\omega (X(\omega) + Y(\omega)) P(\omega) = \sum_\omega X(\omega)P(\omega) + \sum_\omega Y(\omega)P(\omega) = \mathbb{E}[X] + \mathbb{E}[Y]$
3. **一般测度空间**：通过简单函数逼近和 Bochner 积分的线性性推广到一般情形
4. **数乘性**：利用积分的齐次性 $\int cX \, dP = c \int X \, dP$

核心洞察在于期望作为线性泛函，其线性性根植于积分的构造本身。

## 示例

### 示例 1：掷两枚骰子

设 $X, Y$ 分别为两枚骰子的点数。$\mathbb{E}[X] = \mathbb{E}[Y] = 3.5$。由线性性，点数之和的期望为 $\mathbb{E}[X+Y] = 3.5 + 3.5 = 7$。这与直接计算 36 种等概率结果的平均值完全一致。

### 示例 2：随机图中的三角形数

在 $n$ 个顶点的随机图 $G(n, p)$ 中，设 $X$ 为三角形数。将 $X$ 表示为 $\binom{n}{3}$ 个指示变量之和，每个指示变量对应一个潜在三角形是否存在。由期望线性性，$\mathbb{E}[X] = \binom{n}{3} p^3$，无需考虑不同三角形之间的复杂相关性。

### 示例 3：优惠券收集问题

收集全部 $n$ 种优惠券所需次数的期望可以分解为收集第 $k$ 张新优惠券所需等待时间的期望之和。由线性性，总期望为 $n(1 + 1/2 + \dots + 1/n) \approx n \ln n$。

## 应用

- **组合概率**：计算复杂随机结构中特定子结构期望数量的标准方法
- **算法分析**：分析随机算法和启发式算法的期望性能
- **博弈论**：计算多人博弈中期望收益和最优策略
- **统计物理**：配分函数和自由能的线性近似计算
- **机器学习**：集成方法（如随机森林）中基学习器期望误差的分解

## 相关概念

- 数学期望 (Expected Value)：随机变量取值的概率加权平均
- 指示随机变量 (Indicator Random Variable)：仅取 0 或 1 的随机变量
- Bochner 积分 (Bochner Integral)：向量值函数的积分，期望的测度论基础
- 方差可加性 (Additivity of Variance)：独立随机变量和的方差等于方差之和
- 全期望公式 (Law of Total Expectation)：$\mathbb{E}[X] = \mathbb{E}[\mathbb{E}[X|Y]]$

## 参考

### 教材

- [P. Billingsley. Probability and Measure. Wiley, 3rd edition, 1995. Chapter 15]
- [S. Ross. A First Course in Probability. Pearson, 10th edition, 2018. Chapter 4]

### 在线资源

- [Mathlib4 - Bochner Integral](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Bochner.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*