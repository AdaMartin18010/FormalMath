---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: L函数函数方程 (L-Functional Equation)
---
# L函数函数方程 (L-Functional Equation)

## Mathlib4 引用

```lean
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Completion

namespace LFunctionalEquation

variable {χ : DirichletCharacter ℂ N}

/-- Dirichlet L函数的函数方程 -/
theorem dirichlet_l_functional_equation {s : ℂ} (hs : s ≠ 1) :
    completedL χ s = W χ * completedL (inv χ) (1 - s) := by
  -- Poisson求和公式
  sorry

/-- Riemann Zeta的函数方程 -/
theorem riemann_zeta_functional_equation {s : ℂ} (hs : s ≠ 1) :
    completedZeta s = completedZeta (1 - s) := by
  -- χ = 1 的特殊情形
  sorry

/-- 解析延拓与函数方程 -/
theorem analytic_continuation :
    AnalyticOn ℂ (completedL χ) (univ \ {1}) := by
  sorry

end LFunctionalEquation
```

## 数学背景

L函数的函数方程是解析数论中最深刻、最核心的结果之一，由Bernhard Riemann（对zeta函数，1859年）和Erich Hecke（对更一般的L函数，1917-1936年）建立。它表明L函数在 $s$ 和 $1-s$ 处的值通过某种"补全因子"深刻联系，揭示了算术对象背后隐藏的对称性。函数方程是证明L函数解析延拓、建立函数方程类Riemann假设猜想、以及连接算术与分析两大数学领域的基石。

### Dirichlet特征

**定义（Dirichlet特征）**：模 $N$ 的**Dirichlet特征**是群同态 $\chi: (\mathbb{Z}/N\mathbb{Z})^\times \to \mathbb{C}^\times$，通过周期延拓（令 $\chi(n) = \chi(n \bmod N)$ 当 $(n,N) = 1$，否则 $\chi(n) = 0$）看作 $\mathbb{Z}$ 上的函数。

**本原特征**：特征 $\chi$ 称为**本原的**（primitive），如果不存在 $N$ 的真因子 $d | N$ 和模 $d$ 的特征 $\chi_0$，使得 $\chi(n) = \chi_0(n)$ 对所有 $(n, N) = 1$ 成立。

**特征的正交性**：

$$\frac{1}{\varphi(N)} \sum_{\chi \pmod{N}} \chi(a) \overline{\chi(b)} = \begin{cases} 1 & a \equiv b \pmod{N}, (a,N)=1 \\ 0 & \text{否则} \end{cases}$$

### Dirichlet L函数

**定义（Dirichlet L函数）**：设 $\chi$ 是Dirichlet特征。其**Dirichlet L函数**定义为：

$$L(s, \chi) = \sum_{n=1}^{\infty} \frac{\chi(n)}{n^s} = \prod_{p \text{ prime}} \frac{1}{1 - \chi(p)p^{-s}}$$

其中 $\text{Re}(s) > 1$。Euler乘积在 $\text{Re}(s) > 1$ 时绝对收敛。

当 $\chi = \chi_0$ 是主特征（模 $N$）时，$L(s, \chi_0)$ 与Riemann zeta函数相差有限个Euler因子：

$$L(s, \chi_0) = \zeta(s) \prod_{p | N} (1 - p^{-s})$$

## 函数方程的陈述

### Dirichlet L函数的函数方程

**定理（函数方程）**：设 $\chi$ 是模 $N$ 的本原Dirichlet特征。定义**补全L函数**（completed L-function）：

$$\Lambda(s, \chi) = \left(\frac{\pi}{N}\right)^{-(s + a)/2} \Gamma\left(\frac{s + a}{2}\right) L(s, \chi)$$

其中 $a = a(\chi) \in \{0, 1\}$ 由 $\chi(-1) = (-1)^a$ 确定（即 $a = 0$ 若 $\chi$ 偶，$a = 1$ 若 $\chi$ 奇）。

则 $\Lambda(s, \chi)$ 可以解析延拓为整个复平面上的整函数（当 $\chi \neq \chi_0$ 时），或仅在 $s = 1$ 处有单极点（当 $\chi = \chi_0$ 时），并且满足函数方程：

$$\Lambda(s, \chi) = \varepsilon(\chi) \Lambda(1-s, \overline{\chi})$$

其中 $\varepsilon(\chi)$ 是**根数**（root number），满足 $|\varepsilon(\chi)| = 1$。

根数可以显式计算：

$$\varepsilon(\chi) = \frac{\tau(\chi)}{i^a \sqrt{N}}$$

其中 $\tau(\chi) = \sum_{n=1}^{N} \chi(n) e^{2\pi i n/N}$ 是**Gauss和**。

### Riemann Zeta函数的函数方程

当 $\chi = \chi_0$（即 $N = 1$）时，$L(s, \chi_0) = \zeta(s)$，补全zeta函数为：

$$\xi(s) = \pi^{-s/2} \Gamma\left(\frac{s}{2}\right) \zeta(s)$$

函数方程简化为：

$$\xi(s) = \xi(1-s)$$

或等价地：

$$\zeta(s) = 2^s \pi^{s-1} \sin\left(\frac{\pi s}{2}\right) \Gamma(1-s) \zeta(1-s)$$

## 证明概要

### 第一步：Poisson求和公式

函数方程证明的核心工具是**Poisson求和公式**：设 $f$ 是 $\mathbb{R}$ 上的Schwartz函数，则：

$$\sum_{n \in \mathbb{Z}} f(n) = \sum_{n \in \mathbb{Z}} \hat{f}(n)$$

其中 $\hat{f}(\xi) = \int_{-\infty}^{\infty} f(x) e^{-2\pi i x \xi} dx$ 是Fourier变换。

### 第二步：Theta函数与Mellin变换

对特征 $\chi$，定义theta函数：

$$\theta_\chi(t) = \sum_{n \in \mathbb{Z}} \chi(n) e^{-\pi n^2 t/N} \quad (t > 0)$$

利用Poisson求和公式和Gauss和的性质，可以建立theta函数的函数方程：

$$\theta_\chi(t) = \frac{\tau(\chi)}{\sqrt{N} \, t^{1/2}} \theta_{\overline{\chi}}(1/t)$$

### 第三步：Mellin变换与解析延拓

补全L函数与theta函数的Mellin变换有关。将积分拆分为 $(0, 1]$ 和 $[1, \infty)$，在 $(0, 1]$ 上利用theta函数的函数方程作变量替换 $t \mapsto 1/t$，得到解析延拓和函数方程。

具体计算给出：

$$\Lambda(s, \chi) = \varepsilon(\chi) \Lambda(1-s, \overline{\chi})$$

其中根数 $\varepsilon(\chi)$ 如上定义。由于 $\theta_\chi(t)$ 当 $t \to \infty$ 时指数衰减，$[1, \infty)$ 上的积分定义整函数；$(0, 1]$ 上的部分经变换后与 $\overline{\chi}$ 的补全L函数相关。 $\square$

## 例子

### 例子1：Riemann Zeta函数的对称性

Riemann zeta函数的函数方程 $\xi(s) = \xi(1-s)$ 表明补全zeta函数关于 $s = 1/2$ 对称。这意味着zeta函数的非平凡零点（若 $\rho$ 是零点，则 $1-\rho$、$\overline{\rho}$、$1-\overline{\rho}$ 也是零点）关于实轴和 $s = 1/2$ 对称。

Riemann假设断言所有非平凡零点都位于 $s = 1/2$ 这条直线上，这与函数方程揭示的对称性深刻相关。

### 例子2：模4特征

设 $\chi_4$ 是模4的非主特征：$\chi_4(1) = 1$，$\chi_4(3) = -1$，$\chi_4(2) = \chi_4(0) = 0$。这是本原特征，$a(\chi_4) = 1$（奇特征）。

$$L(s, \chi_4) = 1 - \frac{1}{3^s} + \frac{1}{5^s} - \frac{1}{7^s} + \cdots = \sum_{n=0}^{\infty} \frac{(-1)^n}{(2n+1)^s}$$

Gauss和：$\tau(\chi_4) = e^{2\pi i/4} - e^{6\pi i/4} = i - (-i) = 2i$。

根数：$\varepsilon(\chi_4) = \frac{2i}{i \cdot 2} = 1$。

函数方程：$\Lambda(s, \chi_4) = \Lambda(1-s, \chi_4)$（因为 $\overline{\chi_4} = \chi_4$）。

特殊值：$L(1, \chi_4) = \pi/4$（Leibniz公式）。

### 例子3：二次特征的L函数

设 $d$ 是基本判别式，$\chi_d$ 是模 $|d|$ 的Kronecker符号（二次特征）。则 $L(s, \chi_d)$ 与虚二次域 $\mathbb{Q}(\sqrt{d})$（$d < 0$）或实二次域（$d > 0$）的Dedekind zeta函数密切相关：

$$\zeta_{\mathbb{Q}(\sqrt{d})}(s) = \zeta(s) L(s, \chi_d)$$

函数方程给出了这些代数数论对象的深刻对称性。

### 例子4：函数方程与特殊值

函数方程将 $s$ 处的L值与 $1-s$ 处的L值联系起来。特别地，对正整数 $n$：

$$\zeta(2n) = (-1)^{n+1} \frac{B_{2n} (2\pi)^{2n}}{2(2n)!}$$

其中 $B_{2n}$ 是Bernoulli数。函数方程将此与 $\zeta(1-2n) = -B_{2n}/(2n)$ 联系起来。

## 应用

### 1. 素数定理的证明

Dirichlet L函数的解析延拓和函数方程是证明Dirichlet素数定理（算术级数中有无穷多个素数）的核心工具。通过对 $L(s, \chi)$ 在 $s = 1$ 处非零的证明，结合函数方程提供的解析信息，可以得到素数分布的精确渐近公式。

### 2. Riemann假设的研究

函数方程揭示的关于 $s = 1/2$ 的对称性是Riemann假设研究的核心。任何证明或反证Riemann假设的方法都必须解释为什么零点应该（或不应该）位于临界线上。函数方程也是计算zeta函数零点的算法（如Riemann-Siegel公式）的基础。

### 3. BSD猜想

Birch和Swinnerton-Dyer猜想将椭圆曲线 $E$ 的Mordell-Weil群秩与 $L(E, s)$ 在 $s = 1$ 处的零点阶数联系起来。函数方程将 $s = 1$ 处的行为与 $s = 0$ 处的行为联系起来，在p进L函数和Iwasawa理论中尤为重要。

### 4. 自守形式与Langlands纲领

Hecke将Dirichlet L函数推广到Hecke L函数（对数域的特征），其函数方程更为复杂。Langlands纲领将这一框架进一步推广到自守L函数，猜想所有"来自算术"的L函数都应满足某种函数方程。模形式、Maass形式等自守形式的L函数都满足优美的函数方程，这是现代数论研究的核心主题。

### 5. 解析数论中的显式公式

Riemann的显式公式将素数的分布与zeta函数的零点联系起来：

$$\psi(x) = x - \sum_{\rho} \frac{x^{\rho}}{\rho} - \frac{\zeta'(0)}{\zeta(0)} - \frac{1}{2}\log(1-x^{-2})$$

其中 $\rho$ 取遍zeta函数的非平凡零点。这个公式的推导依赖于函数方程和zeta函数的完备信息。

---

*最后更新：2026-04-03 | 版本：v1.0.0*
