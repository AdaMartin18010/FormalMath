---
msc_primary: 00A99
processed_at: '2026-04-15'
title: 独立随机变量和的方差 (Variance of Sum of Independent Random Variables)
---
# 独立随机变量和的方差 (Variance of Sum of Independent Random Variables)

## Mathlib4 引用

```lean
import Mathlib.Probability.Variance

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X Y : Ω → ℝ} (hX : Integrable (fun ω => (X ω)^2) P)
    (hY : Integrable (fun ω => (Y ω)^2) P)

/-- 独立随机变量和的方差等于方差之和 -/
theorem variance_add_independent (hindep : Independent X Y P) :
    variance (X + Y) P = variance X P + variance Y P := by
  -- 展开方差定义，利用独立性消去协方差项
  sorry

end ProbabilityTheory
```

## 数学背景

独立随机变量和的方差公式是概率论中最基本且实用的结果之一。该公式断言：若 $X$ 和 $Y$ 独立，则 $\text{Var}(X + Y) = \text{Var}(X) + \text{Var}(Y)$。这一性质是风险分散、投资组合理论、统计抽样和实验设计的理论基础。

## 直观解释

这个定理可以用投资组合的例子来理解：假设你同时投资两只互不相关的股票。每只股票的日收益率都有各自的波动（方差）。根据这个定理，组合总收益的方差就是两只股票方差之和。如果你将全部资金投入一只股票，你承担的是该股票的完整波动；但如果你平均分配到两只独立股票上，总波动的增长速度慢于预期收益的增长速度，从而提高了风险调整后的收益。

## 形式化表述

设 $X$ 和 $Y$ 是两个独立的随机变量，且方差均存在，则：

$$\text{Var}(X + Y) = \text{Var}(X) + \text{Var}(Y)$$

更一般地，若 $X_1, X_2, \dots, X_n$ 两两独立（或更弱地，不相关），则：

$$\text{Var}\left(\sum_{{i=1}}^n X_i\right) = \sum_{{i=1}}^n \text{Var}(X_i)$$

其中：

- $\text{Var}(X) = \mathbb{E}[(X - \mathbb{E}[X])^2]$ 是随机变量 $X$ 的方差
- 独立性条件至关重要；若 $X, Y$ 不独立，则有 $\text{Var}(X+Y) = \text{Var}(X) + \text{Var}(Y) + 2\text{Cov}(X,Y)$
- $\text{Cov}(X,Y) = \mathbb{E}[(X-\mu_X)(Y-\mu_Y)]$ 是协方差

## 证明思路

1. **方差定义展开**：$\text{Var}(X+Y) = \mathbb{E}[(X+Y - \mu_X - \mu_Y)^2]$
2. **平方展开**：$= \mathbb{E}[(X-\mu_X)^2 + (Y-\mu_Y)^2 + 2(X-\mu_X)(Y-\mu_Y)]$
3. **期望线性性**：$= \text{Var}(X) + \text{Var}(Y) + 2\text{Cov}(X,Y)$
4. **独立性利用**：若 $X, Y$ 独立，则 $\text{Cov}(X,Y) = 0$，从而得证

核心洞察在于独立性消除了交叉项（协方差），使得总方差呈现可加性。

## 示例

### 示例 1：掷骰子

掷两枚公平骰子，设 $X, Y$ 为点数。$\text{Var}(X) = \text{Var}(Y) = 35/12 \approx 2.92$。由独立性，点数之和的方差为 $35/12 + 35/12 = 35/6 \approx 5.83$。

### 示例 2：抽样调查

对 100 名受访者进行独立问卷调查，每人回答的得分方差为 4。则总分方差为 $100 \times 4 = 400$，标准差为 20。平均得分的方差为 $400/100^2 = 0.04$，标准差为 0.2。这解释了为什么大样本均值更加稳定。

### 示例 3：投资组合

两只独立股票的收益率方差分别为 0.04 和 0.09。等权重投资组合的收益率方差为 $(0.04 + 0.09)/4 = 0.0325$，标准差约为 0.18，小于任何一只股票的标准差（0.2 和 0.3），体现了风险分散效应。

## 应用

- **投资组合理论**：现代资产组合理论（MPT）中风险分散的数学基础
- **统计抽样**：样本均值标准误差的计算和置信区间的构造
- **实验设计**：随机化实验中方差分析和显著性检验的理论依据
- **质量控制**：多工序生产过程中的总质量波动预测
- **保险精算**：独立保单组合总赔付风险的聚合计算

## 相关概念

- 方差 (Variance)：衡量随机变量偏离期望程度的指标
- 协方差 (Covariance)：描述两个随机变量联合变化趋势的指标
- 独立性 (Independence)：一个随机变量的分布不受另一个变量取值影响的性质
- 不相关性 (Uncorrelatedness)：协方差为零的较弱的条件
- 大数定律 (Law of Large Numbers)：独立随机变量和方差可加性的渐近结果

## 参考

### 教材

- [P. Billingsley. Probability and Measure. Wiley, 3rd edition, 1995. Section 21]
- [S. Ross. A First Course in Probability. Pearson, 10th edition, 2018. Chapter 4]

### 在线资源

- [Mathlib4 - Variance](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Variance.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*