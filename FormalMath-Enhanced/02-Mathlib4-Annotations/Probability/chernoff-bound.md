---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: Chernoff 界 (Chernoff Bound)
---
# Chernoff 界 (Chernoff Bound)

## Mathlib4 引用

```lean
import Mathlib.Probability.IdentDistrib

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ}

/-- Chernoff 界：独立伯努利变量和偏离期望的指数衰减上界 -/
theorem chernoff_bound_upper (hind : Pairwise (Independent identDistrib X P))
    (hX01 : ∀ i ω, X i ω ∈ {0, 1}) (hμ : expectation (X 0) P = p)
    (ε : ℝ) (hε : 0 < ε) :
    P {ω | (1 / n) * ∑ i in Finset.range n, X i ω ≥ p + ε} ≤
      Real.exp (-2 * n * ε^2) := by
  -- 利用矩母函数和 Markov 不等式推导
  sorry

end ProbabilityTheory
```

## 数学背景

Chernoff 界是概率论和计算机科学中最重要的集中不等式之一，以赫尔曼·切尔诺夫（Herman Chernoff）的名字命名。与切比雪夫不等式提供的多项式衰减不同，Chernoff 界给出了独立随机变量和偏离其期望的指数衰减上界。

## 直观解释

Chernoff 界的威力在于它描述了大数定律的收敛速度。想象抛掷一枚有偏硬币 1000 次，正面朝上的概率为 60%%。切比雪夫不等式只能告诉你正面频率偏离 60%% 超过 5%% 的概率不超过某个多项式衰减的值，而 Chernoff 界则能给出这个概率小于 $e^{{-50}}$——这是一个极其微小的数。这说明当独立随机变量的数量很大时，样本均值几乎不可能显著偏离期望值。

## 形式化表述

设 $X_1, X_2, \dots, X_n$ 是独立的伯努利随机变量，$P(X_i = 1) = p_i$，$P(X_i = 0) = 1 - p_i$。令 $S_n = \sum_{{i=1}}^n X_i$，$\mu = \mathbb{E}[S_n] = \sum_{{i=1}}^n p_i$。则对任意 $\delta > 0$：

**上尾**：
$$P(S_n \geq (1+\delta)\mu) \leq \left(\frac{{e^\delta}}{{(1+\delta)^{{1+\delta}}}}\right)^\mu$$

**下尾**：
$$P(S_n \leq (1-\delta)\mu) \leq \left(\frac{{e^{{-\delta}}}}{{(1-\delta)^{{1-\delta}}}}\right)^\mu$$

对于 $0 < \delta < 1$，有更简洁的形式：

$$P(|S_n - \mu| \geq \delta\mu) \leq 2e^{{-\mu\delta^2/3}}$$

若所有 $p_i = p$，则对样本均值 $\bar{X}_n = S_n/n$：

$$P(|\bar{X}_n - p| \geq \varepsilon) \leq 2e^{{-2n\varepsilon^2}}$$

其中：

- $S_n$ 是 $n$ 个独立伯努利变量之和
- $\mu = \mathbb{E}[S_n]$ 是期望总和
- 不等式右端随 $n$ 指数衰减

## 证明思路

1. **矩母函数**：计算单个伯努利变量的矩母函数 $M_{{X_i}}(t) = \mathbb{E}[e^{{tX_i}}] = 1 - p_i + p_i e^t$
2. **独立性利用**：$S_n$ 的矩母函数为各 $M_{{X_i}}(t)$ 的乘积
3. **Markov 不等式**：对 $e^{{tS_n}}$ 应用 Markov 不等式，取最优的 $t > 0$
4. **优化与放缩**：利用 $1 + x \leq e^x$ 等不等式放缩，得到指数形式的上界

核心洞察在于独立性的矩母函数可分解性使得能够精细控制尾部概率。

## 示例

### 示例 1：民意调查

调查 1000 名选民，真实支持率为 55%%。Chernoff 界给出样本支持率偏离真实值超过 3%% 的概率不超过 $2e^{{-2 \times 1000 \times 0.03^2}} = 2e^{{-1.8}} \approx 0.33$。若样本量增至 10000，该上界降至约 $2e^{{-18}} \approx 3 \times 10^{{-8}}$。

### 示例 2：随机算法

某蒙特卡洛算法每次运行以概率 $p \geq 0.6$ 给出正确答案。运行 $n = 100$ 次后取多数表决。Chernoff 界保证错误概率小于 $e^{{-2 \times 100 \times 0.1^2}} = e^{{-2}} \approx 0.135$。若 $n = 1000$，错误概率小于 $e^{{-20}} \approx 2 \times 10^{{-9}}$。

### 示例 3：负载均衡

将 $n$ 个球独立随机投入 $n$ 个箱子。Chernoff 界可用于证明最大负载以高概率不超过 $O(\ln n / \ln \ln n)$，这是 balls-into-bins 问题的经典结果。

## 应用

- **随机算法分析**：分析拉斯维加斯和蒙特卡洛算法的失败概率和运行时间
- **机器学习理论**：PAC 学习框架中的样本复杂度和泛化误差界
- **通信与编码**：信道容量、纠错码性能和网络吞吐量分析
- **负载均衡**：分布式系统中任务分配和资源调度的概率保证
- **统计假设检验**：大规模数据下的显著性水平和检验功效分析

## 相关概念

- 集中不等式 (Concentration Inequality)：描述随机变量围绕期望集中的概率界
- 矩母函数 (Moment Generating Function)：$M_X(t) = \mathbb{E}[e^{{tX}}]$，推导 Chernoff 界的核心工具
- Hoeffding 不等式 (Hoeffding's Inequality)：Chernoff 界在有界随机变量上的推广
- 伯努利试验 (Bernoulli Trial)：仅有两个可能结果的独立随机试验
- PAC 学习 (PAC Learning)：计算学习理论中的概率近似正确框架

## 参考

### 教材

- [M. Mitzenmacher, E. Upfal. Probability and Computing. Cambridge, 2nd edition, 2017. Chapter 4]
- [S. Shalev-Shwartz, S. Ben-David. Understanding Machine Learning. Cambridge, 2014. Chapter B]

### 在线资源

- [Mathlib4 - IdentDistrib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/IdentDistrib.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*