---
msc_primary: 00A99
processed_at: '2026-04-15'
title: 中心极限定理 (Central Limit Theorem)
---
# 中心极限定理 (Central Limit Theorem)

## Mathlib4 引用

```lean
import Mathlib.Probability.Distributions.Gaussian

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ}

/-- 中心极限定理：独立同分布随机变量序列的标准化和依分布收敛于标准正态分布 -/
theorem central_limit_theorem (hind : Pairwise (Independent identDistrib X P))
    (hμ2 : Integrable (fun ω => (X 0 ω)^2) P) (hμ : expectation (X 0) P = μ) (hσ : variance (X 0) P = σ^2) (hσpos : 0 < σ) :
    Tendsto (fun n => (1 / (σ * sqrt n)) * ∑ i in Finset.range n, (X i - μ)) atTop
      (𝓝 (gaussianReal 0 1)) := by
  -- 证明通常基于特征函数或矩生成函数的收敛
  sorry

end ProbabilityTheory
```

## 数学背景

中心极限定理是概率论中最深刻、影响最广泛的定理之一，由棣莫弗（De Moivre）于1733年对二项分布首次发现，后经拉普拉斯（Laplace）和李雅普诺夫（Lyapunov）等人推广到一般情形。

## 直观解释

中心极限定理揭示了一个令人惊叹的数学规律：当我们把许多微小的、独立的随机影响因素叠加在一起时，最终的分布总是呈现出优美的钟形曲线——正态分布。想象一下一个班级学生的身高：它受到遗传、营养、运动、睡眠等众多独立因素的共同影响。每个因素单独作用时可能服从完全不同的分布，但它们的综合效果却神奇地趋向于正态分布。

## 形式化表述

设 $X_1, X_2, \dots$ 是独立同分布的随机变量序列，$\mathbb{E}[X_1] = \mu$，$\text{Var}(X_1) = \sigma^2 < \infty$。定义部分和 $S_n = \sum_{{i=1}}^n X_i$，则标准化和：

$$Z_n = \frac{{S_n - n\mu}}{{\sigma\sqrt{{n}}}} = \frac{{1}}{{\sigma\sqrt{{n}}}} \sum_{{i=1}}^n (X_i - \mu)$$

依分布收敛于标准正态分布：

$$Z_n \xrightarrow{{d}} N(0, 1) \quad (n \to \infty)$$

即对任意实数 $z$：

$$\lim_{{n \to \infty}} P(Z_n \leq z) = \Phi(z) = \frac{{1}}{{\sqrt{{2\pi}}}} \int_{{-\infty}}^z e^{{-t^2/2}} dt$$

其中：

- $\Phi(z)$ 是标准正态分布的累积分布函数
- $\xrightarrow{{d}}$ 表示依分布收敛

## 证明思路

1. **特征函数**：引入随机变量 $X_i$ 的特征函数 $\varphi_X(t) = \mathbb{E}[e^{{itX}}]$
2. **泰勒展开**：在 $t=0$ 附近展开 $\varphi_X(t) = 1 + it\mu - \frac{{t^2\sigma^2}}{{2}} + o(t^2)$
3. **独立性利用**：$Z_n$ 的特征函数为 $\varphi_{{Z_n}}(t) = [\varphi_X(t/(\sigma\sqrt{{n}}))]^n$
4. **极限计算**：取对数并利用 $\ln(1+x) \sim x$ 得到 $\ln \varphi_{{Z_n}}(t) \to -t^2/2$，即标准正态分布的特征函数

核心洞察在于大量微小独立效应的叠加会产生一种普适的极限分布。

## 示例

### 示例 1：二项分布的正态近似

抛掷一枚公平硬币 $n = 100$ 次，正面次数 $S_n \sim \text{Binomial}(100, 0.5)$。根据中心极限定理，$P(S_n \leq 55) \approx P(Z \leq (55.5 - 50)/5) = P(Z \leq 1.1) \approx 0.864$。

### 示例 2：骰子点数和

掷 30 枚公平骰子，每枚期望为 3.5，方差为 35/12。总点数和的标准化近似服从 $N(0,1)$。这解释了为什么大量骰子点数和的分布接近钟形曲线。

### 示例 3：测量误差

某物理量的测量受到 100 个独立微小误差源的影响。根据中心极限定理，总测量误差近似服从正态分布，这正是经典误差理论的基础假设。

## 应用

- **统计推断**：假设检验、置信区间和参数估计的理论基础
- **质量管理**：六西格玛管理中的正态假设和过程控制
- **金融工程**：Black-Scholes 期权定价模型和风险管理
- **信号处理**：噪声分析和滤波器设计的统计模型
- **生物统计学**：临床试验和大规模流行病学研究中的样本量计算

## 相关概念

- 正态分布 (Normal Distribution)：中心极限定理的极限分布
- 大数定律 (Law of Large Numbers)：描述均值收敛的相伴定理
- 特征函数 (Characteristic Function)：证明中心极限定理的核心工具
- 依分布收敛 (Convergence in Distribution)：中心极限定理中的收敛模式
- 棣莫弗-拉普拉斯定理 (De Moivre-Laplace Theorem)：中心极限定理在二项分布中的特例

## 参考

### 教材

- [P. Billingsley. Probability and Measure. Wiley, 3rd edition, 1995. Chapter 27]
- [R. Durrett. Probability: Theory and Examples. Cambridge, 5th edition, 2019. Chapter 3]

### 在线资源

- [Mathlib4 - Gaussian](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Distributions/Gaussian.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*