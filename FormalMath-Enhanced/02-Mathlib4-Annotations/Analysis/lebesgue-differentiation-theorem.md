---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: Lebesgue微分定理 (Lebesgue Differentiation Theorem)
---
# Lebesgue微分定理 (Lebesgue Differentiation Theorem)

## Mathlib4 引用

```lean
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.LocallyIntegrable

namespace LebesgueDifferentiation

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {μ : Measure X} [IsDoublingMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Lebesgue微分定理 -/
theorem lebesgue_differentiation {f : X → E} (hf : LocallyIntegrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun r => (μ (ball x r))⁻¹ • ∫ y in ball x r, f y ∂μ) (𝓝[>] 0) (𝓝 (f x)) := by
  -- Vitali覆盖和Hardy-Littlewood极大函数
  sorry

/--  Hardy-Littlewood极大不等式 -/
theorem hardy_littlewood_maximal {f : X → E} (hf : Integrable f μ) (p : ℝ≥0∞) (hp : 1 < p) :
    ∫⁻ x, maximalFunction f x ^ p ∂μ ≤ C p * ∫⁻ x, ‖f x‖ ^ p ∂μ := by
  -- 覆盖引理的应用
  sorry

end LebesgueDifferentiation
```

## 数学背景

Lebesgue微分定理由法国数学家Henri Lebesgue于1910年证明，是实分析、测度论和调和分析中最基本、最重要的结果之一。它表明局部可积函数在几乎每一点都是"Lebesgue点"，即函数在该点附近的平均值收敛到函数值本身。这一定理是连接积分与微分的核心桥梁，是微积分基本定理在Lebesgue积分框架下的深刻推广，也是调和分析中Hardy-Littlewood极大函数理论、Sobolev空间理论以及现代偏微分方程正则性理论的基石。

### Lebesgue点与平均收敛

**定义（Lebesgue点）**：设 $f \in L^1_{\text{loc}}(\mathbb{R}^n)$，$x \in \mathbb{R}^n$。称 $x$ 是 $f$ 的**Lebesgue点**，如果：

$$\lim_{r \to 0^+} \frac{1}{|B(x, r)|} \int_{B(x,r)} |f(y) - f(x)| \, dy = 0$$

其中 $B(x, r)$ 是以 $x$ 为中心、半径 $r$ 的球，$|B(x,r)|$ 是其Lebesgue测度。

**注**：若 $x$ 是Lebesgue点，则：

$$\lim_{r \to 0^+} \frac{1}{|B(x, r)|} \int_{B(x,r)} f(y) \, dy = f(x)$$

因为：

$$\left|\frac{1}{|B(x,r)|}\int_{B(x,r)} f(y)dy - f(x)\right| \leq \frac{1}{|B(x,r)|}\int_{B(x,r)} |f(y)-f(x)|dy$$

### Hardy-Littlewood极大函数

**定义（Hardy-Littlewood极大函数）**：设 $f \in L^1_{\text{loc}}(\mathbb{R}^n)$。其**（非切向）极大函数**定义为：

$$Mf(x) = \sup_{r > 0} \frac{1}{|B(x,r)|} \int_{B(x,r)} |f(y)| \, dy$$

$Mf(x)$ 测量了 $f$ 在 $x$ 附近所有尺度上的平均绝对值的上确界。

## Lebesgue微分定理的陈述

**定理（Lebesgue微分定理）**：设 $f \in L^1_{\text{loc}}(\mathbb{R}^n)$（在 $\mathbb{R}^n$ 上局部可积）。则对几乎处处的 $x \in \mathbb{R}^n$：

$$\lim_{r \to 0^+} \frac{1}{|B(x,r)|} \int_{B(x,r)} f(y) \, dy = f(x)$$

等价地，$\mathbb{R}^n$ 中几乎每一点都是 $f$ 的Lebesgue点。

**更一般的陈述**：设 $(X, d, \mu)$ 是加倍测度空间（doubling measure space），$f \in L^1_{\text{loc}}(\mu)$。则对 $\mu$-几乎处处的 $x \in X$：

$$\lim_{r \to 0^+} \frac{1}{\mu(B(x,r))} \int_{B(x,r)} f(y) \, d\mu(y) = f(x)$$

### 加倍测度

**定义（加倍测度）**：度量空间 $(X, d)$ 上的Borel测度 $\mu$ 称为**加倍测度**，如果存在常数 $C > 0$，使得对所有球 $B(x, r)$：

$$\mu(B(x, 2r)) \leq C \cdot \mu(B(x, r))$$

Lebesgue测度是加倍测度（$\mathbb{R}^n$ 中 $B(x, 2r)$ 的体积是 $B(x,r)$ 的 $2^n$ 倍）。加倍条件保证测度不会在任何点附近"爆炸"。

## 证明概要

Lebesgue微分定理的证明通常通过Hardy-Littlewood极大函数和Vitali覆盖引理来完成。

### 第一步：Hardy-Littlewood极大不等式

**定理（Hardy-Littlewood极大不等式）**：设 $f \in L^p(\mathbb{R}^n)$，$1 < p \leq \infty$。则 $Mf \in L^p(\mathbb{R}^n)$，且：

$$||Mf||_{L^p} \leq C_p ||f||_{L^p}$$

对 $p = 1$，有弱型估计：

$$|\{x : Mf(x) > \lambda\}| \leq \frac{C}{\lambda} ||f||_{L^1}$$

**证明（Vitali覆盖引理）**：设 $E \subseteq \mathbb{R}^n$ 可测，$\mathcal{B}$ 是一族覆盖 $E$ 的球。Vitali覆盖引理断言存在可数不交子族 $\{B_i\} \subseteq \mathcal{B}$，使得 $E \subseteq \bigcup_i 3B_i$（$3B_i$ 表示与 $B_i$ 同心、半径3倍的球）。

利用Vitali覆盖，可以证明 $Mf$ 的弱型估计：设 $E_\lambda = \{Mf > \lambda\}$。对 $x \in E_\lambda$，存在球 $B_x$ 使得 $\frac{1}{|B_x|}\int_{B_x}|f| > \lambda$。由Vitali引理，选取不交子族 $\{B_i\}$ 覆盖 $E_\lambda$ 的很大一部分。则：

$$|E_\lambda| \leq C \sum_i |B_i| \leq \frac{C}{\lambda} \sum_i \int_{B_i} |f| \leq \frac{C}{\lambda} ||f||_{L^1}$$

### 第二步：Lebesgue微分定理的证明

**证明**：对 $f \in L^1_{\text{loc}}$，定义：

$$\Omega f(x) = \limsup_{r \to 0} \frac{1}{|B(x,r)|}\int_{B(x,r)} |f(y) - f(x)|dy$$

我们要证明 $\Omega f = 0$ a.e.。

**对连续函数**：若 $g$ 连续，则显然 $\Omega g = 0$ 处处成立（由连续性）。

**对一般函数**：设 $f \in L^1_{\text{loc}}$。对任意 $\epsilon > 0$，选取连续函数 $g$（在紧集上）使得 $||f - g||_{L^1} < \epsilon$（由稠密性）。

注意：

$$\Omega f(x) \leq \Omega(f-g)(x) + \Omega g(x) = \Omega(f-g)(x)$$

而：

$$\Omega(f-g)(x) \leq M(f-g)(x) + |f(x) - g(x)|$$

因此：

$$\{x : \Omega f(x) > \lambda\} \subseteq \{M(f-g) > \lambda/2\} \cup \{|f-g| > \lambda/2\}$$

由极大函数的弱型估计和Chebyshev不等式：

$$|\{\Omega f > \lambda\}| \leq \frac{C}{\lambda}||f-g||_{L^1} + \frac{2}{\lambda}||f-g||_{L^1} \leq \frac{C'}{\lambda}\epsilon$$

令 $\epsilon \to 0$，得 $|\{\Omega f > \lambda\}| = 0$ 对所有 $\lambda > 0$。因此 $\Omega f = 0$ a.e.。 $\square$

## 例子

### 例子1：连续函数

若 $f$ 连续，则每一点都是Lebesgue点。因为：

$$\frac{1}{|B(x,r)|}\int_{B(x,r)} |f(y) - f(x)|dy \leq \sup_{y \in B(x,r)} |f(y) - f(x)| \to 0$$

当 $r \to 0$ 时，由连续性。

### 例子2：阶梯函数

设 $f(x) = \chi_{[0,1]}(x)$（$\mathbb{R}$ 上的指示函数）。不连续点为 $x = 0$ 和 $x = 1$。

在 $x = 0$：对 $r < 1$，$\frac{1}{2r}\int_{-r}^{r} f(y)dy = \frac{1}{2r} \cdot r = \frac{1}{2} \neq f(0) = 1$。但 $x = 0$ 是零测集中的一个点。

对 $x \in (0, 1)$，当 $r$ 足够小时 $B(x,r) \subseteq (0,1)$，积分值为 $f(x) = 1$。

对 $x \notin [0,1]$，类似地当 $r$ 足够小时积分值为 $0 = f(x)$。

### 例子3：Dirichlet函数

设 $f = \chi_{\mathbb{Q}}$（有理数集的指示函数）。$f = 0$ a.e.（因为有理数测度为零）。

在Lebesgue意义下，$f$ 的代表元可以取为 $0$。对 $g = 0$，每一点都是Lebesgue点。因此Lebesgue微分定理对 $f$ 成立（在几乎处处意义下）。

### 例子4：非Lebesgue点

可以构造函数使得某一点不是Lebesgue点。例如，在 $\mathbb{R}$ 上设：

$$f(x) = \begin{cases} 1 & x \in \bigcup_{n=1}^{\infty} (2^{-n}, 2^{-n} + 4^{-n}) \\ 0 & \text{否则} \end{cases}$$

在 $x = 0$ 附近，$f$ 在越来越小的区间上取值为1，但这些区间的总测度 $\sum 4^{-n} = 1/3$。可以验证 $0$ 不是Lebesgue点。但这样的点构成零测集。

## 应用

### 1. 微积分基本定理的推广

Lebesgue微分定理推广了微积分基本定理：若 $f \in L^1[a,b]$，$F(x) = \int_a^x f(t)dt$，则 $F'(x) = f(x)$ 对几乎处处的 $x$ 成立。

这是因为：

$$\frac{F(x+h) - F(x)}{h} = \frac{1}{h}\int_x^{x+h} f(t)dt \to f(x)$$

当 $h \to 0$ 时，由Lebesgue微分定理。

### 2. 调和分析中的极大函数

Hardy-Littlewood极大函数理论是现代调和分析的基石。Carleson定理（Fourier级数几乎处处收敛）、Calderon-Zygmund分解、奇异积分算子的有界性等都依赖于极大函数估计。

### 3. Sobolev空间理论

在Sobolev空间 $W^{1,p}$ 中，函数虽然不一定可微，但具有弱导数。Lebesgue微分定理和极大函数理论用于证明Sobolev嵌入定理、Poincare不等式等核心结果。例如，对 $u \in W^{1,p}$，有：

$$\frac{1}{|B|}\int_B |u - u_B| \leq C \cdot \text{diam}(B) \cdot \left(\frac{1}{|B|}\int_B |\nabla u|^p\right)^{1/p}$$

### 4. 几何测度论

在几何测度论中，Radon测度的密度：

$$\Theta^n(\mu, x) = \lim_{r \to 0} \frac{\mu(B(x,r))}{\omega_n r^n}$$

的存在性（对适当的测度）是Lebesgue微分定理的类比，在曲线长度、曲面面积、分形维数的研究中至关重要。

---

*最后更新：2026-04-03 | 版本：v1.0.0*
