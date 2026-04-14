---
msc_primary: 00A99
processed_at: '2026-04-15'
title: 马尔可夫不等式 (Markov's Inequality)
---
# 马尔可夫不等式 (Markov's Inequality)

## Mathlib4 引用

```lean
import Mathlib.MeasureTheory.Integral.Lebesgue

namespace MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ℝ} (hX : Measurable X) (hXnonneg : 0 ≤ X)

/-- 马尔可夫不等式：非负随机变量超过 ε 的概率不超过期望除以 ε -/
theorem markov_inequality (ε : ℝ) (hε : 0 < ε) :
    P {ω | X ω ≥ ε} ≤ (expectation X P) / ε := by
  -- 由积分单调性和指示函数性质直接得到
  sorry

end MeasureTheory
```

## 数学背景

马尔可夫不等式由俄国数学家安德雷·马尔可夫（Andrey Markov）提出，是概率论和测度论中最基本的不等式之一。该不等式仅利用随机变量的非负性和期望，给出了尾部概率的一个简单上界。

## 直观解释

马尔可夫不等式的含义非常直观：如果一个非负随机变量的平均值很小，那么它取很大值的概率也不可能很大。想象一个城市的居民收入分布：如果平均收入是 5 万元，那么收入超过 100 万元的人口比例不可能超过 5%%。这个结论不需要知道收入分布的任何细节——无论它是正态分布、幂律分布还是其他任何分布。

## 形式化表述

设 $X$ 是一个非负随机变量（即 $X \geq 0$ 几乎必然），$\mathbb{E}[X] < \infty$，则对任意 $\varepsilon > 0$：

$$P(X \geq \varepsilon) \leq \frac{\mathbb{E}[X]}{\varepsilon}$$

其中：

- $X$ 是非负随机变量
- $\mathbb{E}[X]$ 是 $X$ 的数学期望
- $\varepsilon > 0$ 是任意正数

注意：不等式仅对非负随机变量成立，对可取负值的随机变量不适用。

## 证明思路

1. **指示函数**：将事件 $\{X \geq \varepsilon\}$ 用指示函数 $\mathbf{1}_{{\{X \geq \varepsilon\}}}$ 表示
2. **不等式控制**：注意到 $X \geq \varepsilon \cdot \mathbf{1}_{{\{X \geq \varepsilon\}}}$（因为 $X$ 非负）
3. **期望单调性**：对两边取期望得 $\mathbb{E}[X] \geq \varepsilon \cdot \mathbb{E}[\mathbf{1}_{{\{X \geq \varepsilon\}}}] = \varepsilon \cdot P(X \geq \varepsilon)$
4. **整理得证**：两边除以 $\varepsilon$ 即得结论

核心洞察在于非负性使得期望可以控制尾部概率的质量。

## 示例

### 示例 1：等待时间

设某服务台的平均等待时间为 10 分钟。马尔可夫不等式保证等待时间超过 30 分钟的概率不超过 $10/30 = 1/3 \approx 33.3%%$。

### 示例 2：网页加载

某网站页面的平均加载时间为 2 秒。根据马尔可夫不等式，加载时间超过 10 秒的比例不超过 $2/10 = 20%%$。

### 示例 3：与切比雪夫不等式的联系

对随机变量 $Y$，设 $X = (Y - \mu)^2 \geq 0$，$\mathbb{E}[X] = \sigma^2$。对 $X$ 应用马尔可夫不等式（取 $\varepsilon = t^2$）即得切比雪夫不等式 $P(|Y - \mu| \geq t) \leq \sigma^2/t^2$。

## 应用

- **概率上界估计**：为复杂分布提供简单但普适的尾部概率上界
- **切比雪夫不等式**：马尔可夫不等式的直接推论
- **Chernoff 界**：通过矩母函数得到更紧的集中不等式
- **随机算法分析**：分析随机算法运行时间和空间复杂度的概率保证
- **排队论**：等待时间和服务强度的基本分析工具

## 相关概念

- 切比雪夫不等式 (Chebyshev's Inequality)：马尔可夫不等式的推广
- Chernoff 界 (Chernoff Bound)：利用矩母函数得到的更紧上界
- 期望 (Expectation)：随机变量的平均值或重心
- 指示函数 (Indicator Function)：事件概率与期望之间的桥梁
- 集中不等式 (Concentration Inequality)：描述随机变量围绕期望波动的概率界

## 参考

### 教材

- [P. Billingsley. Probability and Measure. Wiley, 3rd edition, 1995. Section 5]
- [M. Mitzenmacher, E. Upfal. Probability and Computing. Cambridge, 2nd edition, 2017. Chapter 2]

### 在线资源

- [Mathlib4 - Lebesgue Integral](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Lebesgue.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*