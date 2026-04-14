---
msc_primary: 00A99
processed_at: '2026-04-15'
title: 切比雪夫不等式 (Chebyshev's Inequality)
---
# 切比雪夫不等式 (Chebyshev's Inequality)

## Mathlib4 引用

```lean
import Mathlib.Probability.Variance

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ℝ} (hX : Measurable X) (hX2 : Integrable (fun ω => (X ω)^2) P)

/-- 切比雪夫不等式：随机变量偏离期望超过 ε 的概率不超过方差除以 ε² -/
theorem chebyshev_inequality (μ : ℝ) (hμ : μ = expectation X P) (ε : ℝ) (hε : 0 < ε) :
    P {ω | |X ω - μ| ≥ ε} ≤ variance X P / ε^2 := by
  -- 由马尔可夫不等式应用于 (X - μ)² 得到
  sorry

end ProbabilityTheory
```

## 数学背景

切比雪夫不等式由俄罗斯数学家帕夫努季·切比雪夫（Pafnuty Chebyshev）于1867年证明，是概率论中最基本且应用广泛的不等式之一。该不等式给出了随机变量偏离其期望值的一个普适上界，仅依赖于方差，而不要求随机变量服从任何特定分布。

## 直观解释

切比雪夫不等式提供了一个非常直观的保证：如果一个随机变量的方差很小，那么它取值的波动也会很小。可以想象一个班级的考试成绩，如果平均分是75分且方差很小，那么切比雪夫不等式告诉我们，成绩偏离75分很远的同学比例是有明确上界的。

## 形式化表述

设 $X$ 是一个具有有限期望 $\mu = \mathbb{E}[X]$ 和有限方差 $\sigma^2 = \text{Var}(X)$ 的随机变量，则对任意 $\varepsilon > 0$：

$$P(|X - \mu| \geq \varepsilon) \leq \frac{\sigma^2}{\varepsilon^2}$$

等价地，用标准差表示：

$$P(|X - \mu| \geq k\sigma) \leq \frac{1}{k^2}$$

其中：

- $\mu = \mathbb{E}[X]$ 是 $X$ 的数学期望
- $\sigma^2 = \mathbb{E}[(X - \mu)^2]$ 是 $X$ 的方差
- $\varepsilon > 0$ 和 $k > 0$ 是任意正数

## 证明思路

1. **构造非负随机变量**：考虑 $(X - \mu)^2$，这是一个非负随机变量
2. **应用马尔可夫不等式**：对 $(X - \mu)^2$ 应用马尔可夫不等式
3. **事件转换**：利用 $\{|X - \mu| \geq \varepsilon\} = \{(X - \mu)^2 \geq \varepsilon^2\}$
4. **化简得结论**：$P(|X - \mu| \geq \varepsilon) = P((X - \mu)^2 \geq \varepsilon^2) \leq \mathbb{E}[(X - \mu)^2]/\varepsilon^2 = \sigma^2/\varepsilon^2$

核心洞察在于将偏差控制问题转化为非负随机变量的期望控制问题。

## 示例

### 示例 1：正态分布

设 $X \sim N(\mu, \sigma^2)$。根据切比雪夫不等式，$P(|X - \mu| \geq 2\sigma) \leq 1/4 = 25\%$。实际上正态分布的精确概率约为 4.6\%，说明切比雪夫不等式是较宽松的上界，但具有普适性。

### 示例 2：掷骰子的均值

设掷一枚公平骰子，$X$ 为点数。$\mathbb{E}[X] = 3.5$，$\text{Var}(X) = 35/12 \approx 2.92$。切比雪夫不等式给出 $P(|X - 3.5| \geq 3) \leq 2.92/9 \approx 0.324$。实际概率为 0（骰子点数不可能偏离 3.5 超过 2.5），这再次说明了不等式的保守性。

### 示例 3：质量控制

某零件长度均值为 10cm，方差为 0.01cm²。切比雪夫不等式保证长度偏离均值超过 0.5cm 的比例不超过 $0.01 / 0.25 = 4\%$。

## 应用

- **大数定律**：证明弱大数定律和强大数定律的关键工具
- **统计估计**：构造置信区间和样本量估计
- **随机算法**：分析随机算法的收敛速度和失败概率
- **质量控制**：评估产品参数的波动范围和合格率
- **金融风险**：估计资产收益率的极端偏离概率

## 相关概念

- 马尔可夫不等式 (Markov's Inequality)：切比雪夫不等式的基础
- 方差 (Variance)：衡量随机变量离散程度的核心指标
- 大数定律 (Law of Large Numbers)：大量独立随机变量平均值的稳定性
- 置信区间 (Confidence Interval)：统计估计中的误差范围
- 中心极限定理 (Central Limit Theorem)：独立随机变量和的正态收敛

## 参考

### 教材

- [P. Billingsley. Probability and Measure. Wiley, 3rd edition, 1995. Section 6]
- [R. Durrett. Probability: Theory and Examples. Cambridge, 5th edition, 2019. Chapter 1]

### 在线资源

- [Mathlib4 - Variance](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Variance.html)
- [Wikipedia - Chebyshev's inequality](https://en.wikipedia.org/wiki/Chebyshev%27s_inequality)

---

*最后更新：2026-04-15 | 版本：v1.0.0*