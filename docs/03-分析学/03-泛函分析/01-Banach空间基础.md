---
msc_primary: 46B05
msc_secondary:
  - 46B20
  - 46B25
processed_at: '2026-04-20'
title: Banach空间基础
---

# Banach空间基础

## 1. 引言

Banach空间是完备赋范线性空间，构成了泛函分析的基石。由波兰数学家Stefan Banach在20世纪20年代系统研究并以其名字命名，这一理论为无穷维空间中的分析学提供了严格的框架。与有限维欧几里得空间不同，Banach空间中的拓扑性质更为丰富，许多在有限维情形中显然成立的结论需要更精细的工具才能证明。本文从范数的基本概念出发，通过一系列典型例子建立直观理解，最终阐明完备性在泛函分析中的核心地位。

## 2. 赋范线性空间

### 2.1 范数的定义

**定义 2.1**（范数）。设 $X$ 是域 $\mathbb{K}$（通常为 $\mathbb{R}$ 或 $\mathbb{C}$）上的线性空间。映射 $\|\cdot\|: X \to [0, +\infty)$ 称为**范数**（norm），若满足以下三条公理：

1. **正定性**：$\|x\| = 0$ 当且仅当 $x = 0$；
2. **齐次性**：$\|\alpha x\| = |\alpha| \|x\|$，对所有 $\alpha \in \mathbb{K}$，$x \in X$ 成立；
3. **三角不等式**：$\|x + y\| \leq \|x\| + \|y\|$，对所有 $x, y \in X$ 成立。

满足上述条件的对 $(X, \|\cdot\|)$ 称为**赋范线性空间**（normed linear space）。范数自然诱导度量 $d(x, y) = \|x - y\|$，从而赋予 $X$ 度量拓扑。

**注记 2.2**。若将正定性弱化为 $\|x\| = 0 \Rightarrow x = 0$ 的否定形式，即允许非零元的范数为零，则称 $\|\cdot\|$ 为**半范数**（seminorm）。半范数空间在分布理论和Sobolev空间的研究中具有重要价值。

### 2.2 范数诱导的拓扑

赋范线性空间上的范数诱导的拓扑具有以下基本性质：

**命题 2.3**。在赋范线性空间 $(X, \|\cdot\|)$ 中：
- 加法 $(x, y) \mapsto x + y$ 是 $X \times X \to X$ 的连续映射；
- 数乘 $(\alpha, x) \mapsto \alpha x$ 是 $\mathbb{K} \times X \to X$ 的连续映射；
- 范数映射 $x \mapsto \|x\|$ 是 $X \to [0, +\infty)$ 的连续映射。

*证明*。对于加法，设 $(x_n, y_n) \to (x, y)$，则
$$\| (x_n + y_n) - (x + y) \| \leq \|x_n - x\| + \|y_n - y\| \to 0.$$
对于数乘，设 $\alpha_n \to \alpha$，$x_n \to x$，则
$$\|\alpha_n x_n - \alpha x\| \leq |\alpha_n| \|x_n - x\| + |\alpha_n - \alpha| \|x\| \to 0.$$
范数的连续性由反向三角不等式 $\big|\|x\| - \|y\|\big| \leq \|x - y\|$ 直接得到。$\square$

### 2.3 等价范数

**定义 2.4**。设 $X$ 为线性空间，$\|\cdot\|_1$ 和 $\|\cdot\|_2$ 为 $X$ 上的两个范数。若存在常数 $C_1, C_2 > 0$ 使得
$$C_1 \|x\|_1 \leq \|x\|_2 \leq C_2 \|x\|_1, \quad \forall x \in X,$$
则称这两个范数**等价**（equivalent）。

等价的范数诱导相同的拓扑结构。在有限维空间中，所有范数彼此等价，这是有限维空间区别于无穷维空间的一个本质特征。

**定理 2.5**（有限维空间的范数等价性）。设 $X$ 为有限维线性空间，则 $X$ 上任意两个范数等价。

*证明概要*。设 $\dim X = n$，取一组基 $\{e_1, \ldots, e_n\}$。对任意范数 $\|\cdot\|$，映射 $(\alpha_1, \ldots, \alpha_n) \mapsto \|\sum_{i=1}^n \alpha_i e_i\|$ 在 $\mathbb{K}^n$ 的单位球面上达到正的最小值和有限的最大值，由此可建立与欧几里得范数的等价性。$\square$

## 3. Banach空间的定义与基本性质

### 3.1 完备性

**定义 3.1**（Banach空间）。赋范线性空间 $(X, \|\cdot\|)$ 称为**Banach空间**，若其作为度量空间（装备度量 $d(x,y) = \|x-y\|$）是完备的，即 $X$ 中的每个Cauchy列都在 $X$ 中收敛。

回忆：序列 $(x_n)_{n=1}^\infty$ 称为**Cauchy列**，若对任意 $\varepsilon > 0$，存在 $N \in \mathbb{N}$，使得当 $m, n \geq N$ 时，$\|x_m - x_n\| < \varepsilon$。

**命题 3.2**。设 $X$ 为赋范线性空间，$Y \subseteq X$ 为其线性子空间。则：
1. 若 $Y$ 完备，则 $Y$ 在 $X$ 中是闭的；
2. 若 $X$ 完备且 $Y$ 闭，则 $Y$ 完备（关于诱导范数）。

换言之，Banach空间的闭子空间仍是Banach空间。

### 3.2 完备化的存在性

**定理 3.3**。每个赋范线性空间 $(X, \|\cdot\|)$ 都存在**完备化**（completion），即存在Banach空间 $\tilde{X}$ 和等距嵌入 $i: X \hookrightarrow \tilde{X}$，使得 $i(X)$ 在 $\tilde{X}$ 中稠密。完备化在等距同构意义下唯一。

*证明概要*。构造方法与度量空间的完备化类似：取 $X$ 中所有Cauchy列构成的空间，模去趋于零的Cauchy列（即定义等价关系 $(x_n) \sim (y_n)$ 当且仅当 $\|x_n - y_n\| \to 0$），在商空间上定义范数 $\|[(x_n)]\| = \lim_{n\to\infty} \|x_n\|$。$\square$

## 4. 典型Banach空间例子

### 4.1 序列空间 $l^p$

**定义 4.1**。设 $1 \leq p < \infty$。定义
$$l^p = \left\{ x = (x_n)_{n=1}^\infty \in \mathbb{K}^{\mathbb{N}} : \sum_{n=1}^\infty |x_n|^p < \infty \right\},$$
配备范数
$$\|x\|_p = \left( \sum_{n=1}^\infty |x_n|^p \right)^{1/p}.$$

对于 $p = \infty$，定义
$$l^\infty = \left\{ x = (x_n)_{n=1}^\infty \in \mathbb{K}^{\mathbb{N}} : \sup_{n \in \mathbb{N}} |x_n| < \infty \right\},$$
配备范数
$$\|x\|_\infty = \sup_{n \in \mathbb{N}} |x_n|.$$

**定理 4.2**。对 $1 \leq p \leq \infty$，$(l^p, \|\cdot\|_p)$ 是Banach空间。

*证明*。以 $1 \leq p < \infty$ 为例。首先验证 $l^p$ 是线性空间：若 $x, y \in l^p$，由 Minkowski 不等式（对级数形式），$x + y \in l^p$ 且 $\|x + y\|_p \leq \|x\|_p + \|y\|_p$。齐次性显然。

完备性：设 $(x^{(k)})_{k=1}^\infty$ 为 $l^p$ 中的Cauchy列，其中 $x^{(k)} = (x^{(k)}_n)_{n=1}^\infty$。对每个固定的 $n$，有
$$|x^{(k)}_n - x^{(m)}_n| \leq \|x^{(k)} - x^{(m)}\|_p,$$
故 $(x^{(k)}_n)_{k=1}^\infty$ 是 $\mathbb{K}$ 中的Cauchy列。由 $\mathbb{K}$ 的完备性，设 $x^{(k)}_n \to x_n$。令 $x = (x_n)$。

对任意 $\varepsilon > 0$，存在 $K$ 使得当 $k, m \geq K$ 时，$\|x^{(k)} - x^{(m)}\|_p < \varepsilon$。对任意 $N \in \mathbb{N}$，
$$\sum_{n=1}^N |x^{(k)}_n - x^{(m)}_n|^p < \varepsilon^p.$$
令 $m \to \infty$，得
$$\sum_{n=1}^N |x^{(k)}_n - x_n|^p \leq \varepsilon^p.$$
再令 $N \to \infty$，得 $\|x^{(k)} - x\|_p \leq \varepsilon$。故 $x^{(k)} - x \in l^p$，从而 $x \in l^p$ 且 $x^{(k)} \to x$。$\square$

**例 4.3**。考虑 $l^2$ 中的序列 $e^{(n)} = (0, \ldots, 0, 1, 0, \ldots)$（第 $n$ 位为1）。则 $\|e^{(n)}\|_2 = 1$，且对 $n \neq m$，$\|e^{(n)} - e^{(m)}\|_2 = \sqrt{2}$。这说明 $l^2$ 中的单位球面不是列紧的——这与有限维空间形成鲜明对比。

### 4.2 函数空间 $L^p$

**定义 4.4**。设 $(\Omega, \mathcal{F}, \mu)$ 为测度空间，$1 \leq p < \infty$。定义
$$L^p(\Omega, \mu) = \left\{ f: \Omega \to \mathbb{K} \text{ 可测} : \int_\Omega |f|^p \, d\mu < \infty \right\} / \sim,$$
其中 $f \sim g$ 当且仅当 $f = g$ $\mu$-几乎处处成立。配备范数
$$\|f\|_p = \left( \int_\Omega |f|^p \, d\mu \right)^{1/p}.$$

对于 $p = \infty$，定义
$$L^\infty(\Omega, \mu) = \{ f: \Omega \to \mathbb{K} \text{ 可测且本性有界} \} / \sim,$$
配备本性上确界范数
$$\|f\|_\infty = \operatorname{ess\,sup}_{\omega \in \Omega} |f(\omega)| = \inf\{ M \geq 0 : |f| \leq M \text{ a.e.} \}.$$

**定理 4.5**（Riesz-Fischer）。对 $1 \leq p \leq \infty$，$L^p(\Omega, \mu)$ 是Banach空间。

*证明概要*。$L^p$ 的赋范线性空间结构由 Minkowski 不等式保证。完备性的证明与 $l^p$ 类似：取Cauchy列 $(f_n)$，利用Chebyshev不等式或直接从Cauchy条件提取子列几乎处处收敛，再用Fatou引理控制极限。$\square$

**例 4.6**。设 $\Omega = [0, 1]$，$\mu$ 为Lebesgue测度。考虑函数列
$$f_n(x) = \begin{cases} n^{1/p}, & 0 \leq x \leq \frac{1}{n}, \\ 0, & \frac{1}{n} < x \leq 1. \end{cases}$$
则 $\|f_n\|_p = 1$。对 $n < m$，有
$$\|f_n - f_m\|_p^p = \int_0^{1/m} |n^{1/p} - m^{1/p}|^p dx + \int_{1/m}^{1/n} n dx = \frac{(n^{1/p} - m^{1/p})^p}{m} + n\left(\frac{1}{n} - \frac{1}{m}\right).$$
当 $n, m \to \infty$ 时，上式趋于0（对 $p > 1$），但 $(f_n)$ 在 $L^p$ 中不收敛于任何连续函数。这说明了完备性的必要性——$L^p$ 的完备化（其本身）包含了更多的"广义函数"。

### 4.3 连续函数空间 $C[0,1]$

**定义 4.7**。设 $C[0,1]$ 为闭区间 $[0,1]$ 上全体连续函数 $f: [0,1] \to \mathbb{K}$ 构成的线性空间，配备上确界范数
$$\|f\|_\infty = \sup_{x \in [0,1]} |f(x)| = \max_{x \in [0,1]} |f(x)|.$$

**定理 4.8**。$(C[0,1], \|\cdot\|_\infty)$ 是Banach空间。

*证明*。首先，$\|f\|_\infty$ 确实是范数（上确界可达因 $[0,1]$ 紧且 $f$ 连续）。设 $(f_n)$ 为 $C[0,1]$ 中的Cauchy列，则对每个 $x \in [0,1]$，$(f_n(x))$ 是 $\mathbb{K}$ 中的Cauchy列，故收敛于某 $f(x)$。由一致Cauchy条件，对任意 $\varepsilon > 0$，存在 $N$ 使得当 $n, m \geq N$ 时，$|f_n(x) - f_m(x)| < \varepsilon$ 对所有 $x$ 成立。令 $m \to \infty$，得 $|f_n(x) - f(x)| \leq \varepsilon$，即 $f_n \rightrightarrows f$（一致收敛）。一致收敛保持连续性，故 $f \in C[0,1]$。$\square$

**例 4.9**（不完备的例子）。考虑 $C[0,1]$ 但配备 $L^1$ 范数 $\|f\|_1 = \int_0^1 |f(x)| dx$。这个空间不完备。例如，定义
$$f_n(x) = \begin{cases} 0, & 0 \leq x \leq \frac{1}{2} - \frac{1}{n}, \\ n(x - \frac{1}{2} + \frac{1}{n}), & \frac{1}{2} - \frac{1}{n} < x < \frac{1}{2}, \\ 1, & \frac{1}{2} \leq x \leq 1. \end{cases}$$
则 $(f_n)$ 是 $L^1$ 范数下的Cauchy列，但极限函数在 $x = 1/2$ 处不连续。$C[0,1]$ 关于 $L^1$ 范数的完备化正是 $L^1[0,1]$。

### 4.4 其他重要例子

**例 4.10**（$c_0$ 空间）。定义
$$c_0 = \{ x = (x_n) \in l^\infty : \lim_{n\to\infty} x_n = 0 \}.$$
则 $c_0$ 是 $l^\infty$ 的闭子空间，故为Banach空间。其对偶空间同构于 $l^1$。

**例 4.11**（$c$ 空间）。定义
$$c = \{ x = (x_n) \in l^\infty : \lim_{n\to\infty} x_n \text{ 存在} \}.$$
$c$ 也是Banach空间，且 $c_0 \subset c \subset l^\infty$。

## 5. 商空间与直和

### 5.1 商范数

设 $X$ 为赋范线性空间，$M \subseteq X$ 为闭子空间。商空间 $X/M$ 可配备**商范数**：
$$\|[x]\|_{X/M} = \inf_{m \in M} \|x + m\| = \operatorname{dist}(x, M).$$

**定理 5.1**。若 $X$ 为Banach空间且 $M$ 闭，则 $(X/M, \|\cdot\|_{X/M})$ 是Banach空间。

### 5.2 有界直和

设 $(X_n, \|\cdot\|_n)_{n=1}^\infty$ 为一列Banach空间。定义 $l^p$ 直和：
$$\bigoplus_{n=1}^\infty X_n \;(l^p) = \left\{ (x_n) : x_n \in X_n, \sum_{n=1}^\infty \|x_n\|_n^p < \infty \right\},$$
配备范数 $\|(x_n)\| = (\sum_{n=1}^\infty \|x_n\|_n^p)^{1/p}$。这是Banach空间。

## 6. 收敛模式与Schauder基

### 6.1 强收敛与弱收敛

**定义 6.1**。在赋范线性空间 $X$ 中：
- **强收敛**（按范数收敛）：$x_n \to x$ 指 $\|x_n - x\| \to 0$；
- **弱收敛**：$x_n \rightharpoonup x$ 指对所有连续线性泛函 $f \in X^*$，$f(x_n) \to f(x)$。

强收敛蕴含弱收敛，反之一般不成立。

**例 6.2**。在 $l^2$ 中，$e^{(n)} \rightharpoonup 0$（因为对任意 $y \in l^2$，$\langle e^{(n)}, y \rangle = y_n \to 0$），但 $\|e^{(n)}\|_2 = 1 \not\to 0$，故不强收敛于0。

### 6.2 Schauder基

**定义 6.3**。Banach空间 $X$ 中的序列 $(e_n)_{n=1}^\infty$ 称为**Schauder基**，若对每个 $x \in X$，存在唯一的标量序列 $(\alpha_n)$ 使得
$$x = \sum_{n=1}^\infty \alpha_n e_n$$
（级数按范数收敛）。

**定理 6.4**（Schauder）。具有Schauder基的Banach空间必可分。

**例 6.5**。$l^p$（$1 \leq p < \infty$）具有标准Schauder基 $\{e^{(n)}\}$。$C[0,1]$ 具有Schauder基（如Faber-Schauder系统）。然而，并非所有可分Banach空间都有Schauder基（Enflo, 1973）。

## 7. 与项目其他部分的关联

Banach空间理论是后续学习有界线性算子、谱理论、紧算子等内容的基础。其与Hilbert空间（见[02-Hilbert空间基础](02-Hilbert空间基础.md)）的关系类似于欧几里得空间与内积空间的关系：每个Hilbert空间都是Banach空间，但反之不成立。$L^p$ 空间在实分析（见`docs/03-分析学/02-实分析/`）中已有详细讨论，本文从泛函分析视角重新强调了其完备性与结构性质。分布论与Sobolev空间（见[09-分布论入门](09-分布论入门.md)和[10-Sobolev空间](10-Sobolev空间.md)）则进一步拓展了函数空间的框架。

## 8. 参考文献

1. S. Banach, *Théorie des Opérations Linéaires*, Monografie Matematyczne, Warszawa, 1932.
2. N. Dunford & J.T. Schwartz, *Linear Operators, Part I: General Theory*, Interscience, 1958.
3. W. Rudin, *Functional Analysis*, 2nd ed., McGraw-Hill, 1991.
4. H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Springer, 2011.
5. 张恭庆、林源渠，《泛函分析讲义》（上册），北京大学出版社，1987。
