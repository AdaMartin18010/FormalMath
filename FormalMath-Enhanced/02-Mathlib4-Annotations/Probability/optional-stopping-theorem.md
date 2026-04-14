---
msc_primary: 00A99
processed_at: '2026-04-15'
title: 可选停时定理 (Optional Stopping Theorem)
---
# 可选停时定理 (Optional Stopping Theorem)

## Mathlib4 引用

```lean
import Mathlib.Probability.Martingale.Convergence

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℕ (MeasureSpace.toMeasurableSpace Ω)}
  {M : ℕ → Ω → ℝ} (hM : Martingale M ℱ P)

/-- 可选停时定理：在适当条件下，鞅在停时的期望等于初始期望 -/
theorem optional_stopping (τ : Ω → ℕ) (hτ : IsStoppingTime ℱ τ)
    (hbdd : ∃ N, ∀ ω, τ ω ≤ N)
    (hbddM : ∀ n, ∀ᵐ ω ∂P, |M n ω| ≤ C) :
    expectation (M τ) P = expectation (M 0) P := by
  -- 利用鞅的有界收敛性和停时的可测性证明
  sorry

end ProbabilityTheory
```

## 数学背景

可选停时定理（Optional Stopping Theorem, OST）是鞅论中的核心结果，由约瑟夫·杜布（Joseph L. Doob）系统发展。该定理断言：在适当条件下，一个鞅在停时处的期望等于其初始期望。这一定理在金融数学、博弈论和随机过程理论中具有基础性地位。

## 直观解释

可选停时定理可以用一个赌场博弈的例子来理解：假设你参与一个公平的赌博游戏，每次下注的期望收益为零（这是一个鞅）。定理告诉你：无论你采用多么复杂的退出策略——比如连赢三把就走、输光本金就停或达到某个目标利润就退出——你的总期望收益始终等于你开始时的本金。这似乎是反直觉的，因为某些策略在特定路径上看起来非常有利。但关键在于期望是对所有可能路径的平均，而那些看似有利的策略也伴随着同样多的不利路径。

## 形式化表述

设 $(M_n)_{{n \geq 0}}$ 是一个关于滤子 $(\mathcal{F}_n)_{{n \geq 0}}$ 的鞅，$\tau$ 是一个关于同一滤子的停时。在以下任一条件下：

$$\mathbb{E}[M_\tau] = \mathbb{E}[M_0]$$

**常见充分条件**：

1. $\tau$ 是有界停时（存在 $N$ 使得 $\tau \leq N$ a.s.）
2. $M$ 一致有界且 $\mathbb{E}[\tau] < \infty$
3. $M$ 一致可积

其中：

- 鞅（Martingale）：满足 $\mathbb{E}[M_{{n+1}} | \mathcal{F}_n] = M_n$ 的随机过程
- 停时（Stopping Time）：时刻 $n$ 是否停止仅依赖于截至 $n$ 的信息，即 $\{\tau \leq n\} \in \mathcal{F}_n$
- $M_\tau$ 表示鞅在停时 $\tau$ 处的值

## 证明思路

1. **离散停时逼近**：将一般有界停时 $\tau$ 用取有限值的停时 $\tau \wedge n$ 逼近
2. **鞅性质保持**：证明 $(M_{{\tau \wedge n}})$ 仍然是鞅
3. **期望不变性**：对任意 $n$，$\mathbb{E}[M_{{\tau \wedge n}}] = \mathbb{E}[M_0]$
4. **控制收敛**：在有界性条件下，令 $n \to \infty$ 并应用控制收敛定理得到 $\mathbb{E}[M_\tau] = \mathbb{E}[M_0]$

核心洞察在于鞅的公平性在可预见的停时策略下保持不变。

## 示例

### 示例 1：简单随机游走的停时

设 $(S_n)$ 是对称简单随机游走，$S_0 = 0$，$\tau = \min\{n : S_n = 1\}$。虽然这是停时，但 $\mathbb{E}[\tau] = \infty$，不满足可选停时定理的条件。事实上 $\mathbb{E}[S_\tau] = 1 \neq 0 = \mathbb{E}[S_0]$。

### 示例 2：有界退出策略

设 $(S_n)$ 同上，但令 $\tau = \min\{n \leq 100 : S_n = 1\}$（若 100 步内未到达则停于 100）。此时 $\tau$ 有界，OST 适用，$\mathbb{E}[S_\tau] = 0$。

### 示例 3：美式期权定价

在风险中性测度下，贴现股价过程是鞅。美式期权的提前执行时间是一个停时。可选停时定理说明在无套利条件下，美式期权的价值等于最优停时策略下的期望贴现收益。

## 应用

- **金融数学**：美式期权定价、最优执行策略和套利分析
- **博弈论**：公平博弈中各种退出策略的期望收益分析
- **统计学**：序贯分析中的停止规则和检验功效
- **随机控制**：最优停止问题和动态决策理论
- **数学金融**：风险中性定价和对冲策略的形式化推导

## 相关概念

- 鞅 (Martingale)：公平博弈的数学模型，条件期望等于当前值
- 停时 (Stopping Time)：仅依赖于当前和历史信息的随机时间
- 滤子 (Filtration)：随时间递增的信息结构
- 控制收敛定理 (Dominated Convergence Theorem)：交换极限与积分顺序的核心工具
- 美式期权 (American Option)：可以在到期前任意时间执行的金融衍生品

## 参考

### 教材

- [R. Williams. Probability with Martingales. Cambridge, 1991. Chapter 10]
- [S. Shreve. Stochastic Calculus for Finance I. Springer, 2004. Chapter 4]

### 在线资源

- [Mathlib4 - Martingale Convergence](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Martingale/Convergence.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*