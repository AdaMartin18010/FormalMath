---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: 大数定律 (Law of Large Numbers)
---
# 大数定律 (Law of Large Numbers)

## Mathlib4 引用

```lean
import Mathlib.Probability.IdentDistrib

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ}

/-- 弱大数定律：独立同分布随机变量序列的样本均值依概率收敛于期望 -/
theorem weak_law_large_numbers (hind : Pairwise (Independent identDistrib X P))
    (hμ : Integrable (X 0) P) :
    Tendsto (fun n => (1 / n) * ∑ i in Finset.range n, X i) atTop (𝓝 (expectation (X 0) P)) := by
  -- 利用切比雪夫不等式证明依概率收敛
  sorry

end ProbabilityTheory
```

## 数学背景

大数定律是概率论中最重要的极限定理之一，由雅各布·伯努利（Jacob Bernoulli）在17世纪末首次提出并于1713年发表。该定理揭示了在重复独立试验中，随机事件的频率会稳定在其概率附近。

## 直观解释

大数定律的直观含义非常深刻：当你反复抛掷一枚硬币时，虽然每次的结果都是随机的，但随着抛掷次数的增加，正面朝上的比例会越来越接近 50%%。这就像一个漫长的赌博游戏——短期内你可能大赚或大亏，但只要玩得足够久，结果就会趋向于期望的平均值。

## 形式化表述

设 $X_1, X_2, \dots$ 是独立同分布的随机变量序列，$\mathbb{E}[X_1] = \mu$，$\text{Var}(X_1) = \sigma^2 < \infty$。定义样本均值为：

$$\bar{X}_n = \frac{1}{n} \sum_{{i=1}}^n X_i$$

**弱大数定律（WLLN）**：
$$\bar{X}_n \xrightarrow{{P}} \mu \quad (n \to \infty)$$

**强大数定律（SLLN）**：
$$\bar{X}_n \xrightarrow{{a.s.}} \mu \quad (n \to \infty)$$

其中：

- $\xrightarrow{{P}}$ 表示依概率收敛
- $\xrightarrow{{a.s.}}$ 表示几乎必然收敛
- $\mu = \mathbb{E}[X_1]$ 是共同的数学期望

## 证明思路

1. **期望和方差计算**：计算样本均值 $\bar{X}_n$ 的期望为 $\mu$，方差为 $\sigma^2/n$
2. **切比雪夫不等式**：对弱大数定律，应用切比雪夫不等式于 $\bar{X}_n$
3. **概率上界**：得到 $P(|\bar{X}_n - \mu| \geq \varepsilon) \leq \sigma^2/(n\varepsilon^2) \to 0$
4. **Borel-Cantelli 引理**：对强大数定律，利用 Borel-Cantelli 引理证明几乎必然收敛

核心洞察在于独立性的方差可加性使得样本均值的波动以 $1/n$ 的速度衰减。

## 示例

### 示例 1：抛硬币实验

抛掷一枚公平硬币 $n$ 次，设 $X_i = 1$ 表示第 $i$ 次正面朝上。$\bar{X}_n$ 是正面频率。大数定律保证当 $n \to \infty$ 时，正面频率依概率收敛于 $1/2$。

### 示例 2：蒙特卡洛积分

计算定积分 $\int_0^1 f(x) dx$ 时，可以生成 $n$ 个均匀随机点 $U_i$，用 $\frac{1}{n} \sum_{{i=1}}^n f(U_i)$ 近似。大数定律保证这个估计随 $n$ 增大而收敛到真实积分值。

### 示例 3：保险精算

某保险公司有 10000 份同质保单，每份保单的赔付额是独立同分布的随机变量。大数定律使得公司能够精确预测总赔付额，从而合理定价保费。

## 应用

- **统计学基础**：频率学派的概率解释和统计推断的理论根基
- **蒙特卡洛方法**：数值积分和模拟仿真的收敛性保证
- **保险与金融**：风险评估、期权定价和资产组合管理的理论依据
- **统计力学**：气体分子运动论中宏观量与微观平均的对应
- **机器学习**：经验风险最小化的渐近一致性分析

## 相关概念

- 中心极限定理 (Central Limit Theorem)：描述大数定律收敛速度的更精细结果
- 切比雪夫不等式 (Chebyshev's Inequality)：证明弱大数定律的关键工具
- 依概率收敛 (Convergence in Probability)：弱大数定律中的收敛模式
- 几乎必然收敛 (Almost Sure Convergence)：强大数定律中的收敛模式
- 样本均值 (Sample Mean)：随机变量序列的算术平均

## 参考

### 教材

- [P. Billingsley. Probability and Measure. Wiley, 3rd edition, 1995. Chapter 22]
- [R. Durrett. Probability: Theory and Examples. Cambridge, 5th edition, 2019. Chapter 2]

### 历史文献

- [J. Bernoulli. Ars Conjectandi. 1713]

### 在线资源

- [Mathlib4 - IdentDistrib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/IdentDistrib.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*