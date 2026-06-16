---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: Jensen 不等式 (Jensen's Inequality)
---
# Jensen 不等式 (Jensen's Inequality)

## Mathlib4 引用

```lean
import Mathlib.Probability.Moments

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ℝ} (hX : Integrable X P)

/-- Jensen 不等式：对凸函数 φ，有 φ(E[X]) ≤ E[φ(X)] -/
theorem jensen_inequality {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ)
    (hφX : Integrable (φ ∘ X) P) :
    φ (expectation X P) ≤ expectation (φ ∘ X) P := by
  -- 利用凸函数的支撑超平面性质和期望的单调性证明
  sorry

end ProbabilityTheory
```

## 数学背景

Jensen 不等式由丹麦数学家约翰·延森（Johan Jensen）于1906年证明，是数学分析、概率论和凸优化中的核心不等式。该不等式断言：对于凸函数 $\phi$，有 $\phi(\mathbb{E}[X]) \leq \mathbb{E}[\phi(X)]$；对于凹函数，不等号方向相反。

## 直观解释

Jensen 不等式的几何直觉非常优美：想象一个凸函数图像（如抛物线 $y = x^2$），曲线上任意两点的连线都在曲线的上方。如果把随机变量 $X$ 的取值看作曲线上的一系列点，那么这些点的平均位置（即期望）对应的函数值，必然小于或等于这些点函数值的平均。换句话说，凸函数会放大离散性——先取平均再代入函数，结果不会大于先代入函数再取平均。

## 形式化表述

设 $X$ 是一个随机变量，$\phi: \mathbb{{R}} \to \mathbb{{R}}$ 是一个凸函数，且 $\mathbb{E}[X]$ 和 $\mathbb{E}[\phi(X)]$ 均存在，则：

$$\phi(\mathbb{E}[X]) \leq \mathbb{E}[\phi(X)]$$

若 $\phi$ 是严格凸函数，且 $X$ 不是几乎必然的常数，则严格不等式成立：

$$\phi(\mathbb{E}[X]) < \mathbb{E}[\phi(X)]$$

对于凹函数 $\psi$，不等号反向：

$$\psi(\mathbb{E}[X]) \geq \mathbb{E}[\psi(X)]$$

其中：

- $\phi$ 是凸函数意味着对任意 $x, y$ 和 $t \in [0,1]$：$\phi(tx + (1-t)y) \leq t\phi(x) + (1-t)\phi(y)$
- 概率测度 $P$ 可以推广到一般的概率空间

## 证明思路

1. **支撑超平面**：凸函数在每一点都存在支撑超平面，即存在斜率 $m$ 使得 $\phi(x) \geq \phi(a) + m(x-a)$ 对所有 $x$ 成立
2. **取 $a = \mathbb{E}[X]$**：得到 $\phi(X) \geq \phi(\mathbb{E}[X]) + m(X - \mathbb{E}[X])$
3. **两边取期望**：$\mathbb{E}[\phi(X)] \geq \phi(\mathbb{E}[X]) + m\mathbb{E}[X - \mathbb{E}[X]] = \phi(\mathbb{E}[X])$
4. **严格凸情形**：若 $X$ 非常数，则存在正概率使 $X \neq \mathbb{E}[X]$，由严格凸性得严格不等式

核心洞察在于凸函数的图像总是位于其切线的上方。

## 示例

### 示例 1：算术-几何平均不等式

取 $\phi(x) = -\ln x$（在 $x > 0$ 上凸），对正随机变量 $X$ 应用 Jensen 不等式得 $-\ln(\mathbb{E}[X]) \leq -\mathbb{E}[\ln X]$，即 $\mathbb{E}[X] \geq e^{\mathbb{E}[\ln X]}$。对离散均匀分布即得经典的算术-几何平均不等式。

### 示例 2：方差非负性

取 $\phi(x) = x^2$（凸函数），得 $(\mathbb{E}[X])^2 \leq \mathbb{E}[X^2]$，即 $\text{Var}(X) = \mathbb{E}[X^2] - (\mathbb{E}[X])^2 \geq 0$。

### 示例 3：信息论中的 KL 散度

在信息论中，相对熵（KL 散度）的非负性可以通过 Jensen 不等式（对凸函数 $\phi(x) = x \ln x$）证明。这说明真实分布与近似分布之间的信息损失总是非负的。

## 应用

- **信息论**：KL 散度非负性、熵和互信息的性质推导
- **经济学**：风险厌恶者的效用函数分析（凹效用函数下的确定性等价）
- **统计学习**：EM 算法和变分推断中的下界优化
- **金融数学**：期权定价中的凸性偏误和 Jensen's gap
- **概率不等式**：推导 Hoeffding、Bernstein 等集中不等式

## 相关概念

- 凸函数 (Convex Function)：图像位于任意弦下方的函数
- 支撑超平面 (Supporting Hyperplane)：凸函数图像的切线或切平面推广
- 算术-几何平均不等式 (AM-GM Inequality)：Jensen 不等式的经典推论
- KL 散度 (Kullback-Leibler Divergence)：衡量两个概率分布差异的信息论指标
- 琴生不等式 (Jensen's Inequality in Discrete Form)：有限点情形的 Jensen 不等式

## 参考

### 教材

- [W. Rudin. Real and Complex Analysis. McGraw-Hill, 3rd edition, 1987. Chapter 3]
- [S. Boyd, L. Vandenberghe. Convex Optimization. Cambridge, 2004. Section 3.1]

### 在线资源

- [Mathlib4 - Moments](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Moments.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*