---
msc_primary: "26D15"
msc_secondary:
  - 46C05
  - 15A45
---

# 概念卡片：Cauchy-Schwarz不等式

## 严格定义

设 $V$ 为实或复内积空间，$\langle \cdot, \cdot \rangle$ 为内积，$\|x\| = \sqrt{\langle x, x \rangle}$ 为诱导范数。

**Cauchy-Schwarz 不等式**：对任意 $x, y \in V$，
$$|\langle x, y \rangle| \leq \|x\| \cdot \|y\|。$$

**等号条件**：等号成立当且仅当 $x$ 与 $y$ 线性相关（即存在标量 $\lambda$ 使得 $x = \lambda y$ 或 $y = \lambda x$）。

**常见形式**：
- **离散形式（序列）**：$\left|\sum_{i=1}^n x_i \overline{y_i}\right|^2 \leq \left(\sum_{i=1}^n |x_i|^2\right)\left(\sum_{i=1}^n |y_i|^2\right)$；
- **积分形式（函数）**：$\left|\int f \bar{g}\right|^2 \leq \left(\int |f|^2\right)\left(\int |g|^2\right)$；
- **概率形式**：$|\mathrm{Cov}(X, Y)|^2 \leq \mathrm{Var}(X) \cdot \mathrm{Var}(Y)$。

## 历史背景

Cauchy-Schwarz 不等式是数学中最基本且应用最广泛的不等式之一，其历史涉及多位数学家。

**Cauchy 的离散形式（1821）**：Augustin-Louis Cauchy 在《分析教程》（Cours d'Analyse, 1821）中首次证明了离散形式：
$$(\sum a_i b_i)^2 \leq (\sum a_i^2)(\sum b_i^2)。$$
他的证明使用了 Lagrange 恒等式：
$$(\sum a_i^2)(\sum b_i^2) - (\sum a_i b_i)^2 = \sum_{i < j} (a_i b_j - a_j b_i)^2 \geq 0。$$

**Bunyakovsky 的积分形式（1859）**：俄罗斯数学家 Viktor Bunyakovsky（1804–1889）在 1859 年将 Cauchy 的不等式推广到积分形式，证明了
$$\left(\int_a^b f(x)g(x) \, \mathrm{d}x\right)^2 \leq \left(\int_a^b f(x)^2 \, \mathrm{d}x\right)\left(\int_a^b g(x)^2 \, \mathrm{d}x\right)。$$

**Schwarz 的内积形式（1885）**：Karl Hermann Amandus Schwarz（1843–1921）在 1885 年研究极小曲面时，证明了内积空间中的一般形式。他的证明方法（考虑二次型 $\|x + ty\|^2 \geq 0$）成为今天最标准的证明。

**命名争议**：在西方文献中常称为 Cauchy-Schwarz 不等式；在俄罗斯和东欧传统中称为 Cauchy-Bunyakovsky-Schwarz 不等式（或简称 CBS 不等式），以承认 Bunyakovsky 的贡献。

## 直观理解

Cauchy-Schwarz 不等式的核心直觉是**"投影不延长"**。

在内积空间中，$\langle x, y \rangle / \|y\|$ 是 $x$ 在 $y$ 方向上的（有符号）投影长度。Cauchy-Schwarz 说：这个投影长度不可能超过 $x$ 自身的长度 $\|x\|$。几何上，直角三角形的斜边（$\|x\|$）总是长于直角边（投影长度）。

**余弦解释**：定义
$$\cos \theta = \frac{\mathrm{Re}\langle x, y \rangle}{\|x\| \|y\|}。$$
Cauchy-Schwarz 保证 $|\cos \theta| \leq 1$，即 $\theta$ 是合法的"夹角"。等号成立当且仅当 $|\cos \theta| = 1$，即 $\theta = 0$ 或 $\pi$，$x$ 与 $y$ 共线。

**概率解释**：对随机变量 $X, Y$，$\mathrm{Cov}(X, Y)^2 \leq \mathrm{Var}(X)\mathrm{Var}(Y)$。等号成立当且仅当 $Y = aX + b$（几乎必然），即 $X$ 与 $Y$ 完全线性相关。

## 数学例子

### 标准证明（Schwarz 方法）

设 $x, y \in V$，$y \neq 0$。对任意标量 $t$，
$$0 \leq \|x + ty\|^2 = \|x\|^2 + 2\,\mathrm{Re}(t\langle x, y \rangle) + |t|^2\|y\|^2。$$
取 $t = -\frac{\langle x, y \rangle}{\|y\|^2}$（对实内积空间），则
$$0 \leq \|x\|^2 - \frac{|\langle x, y \rangle|^2}{\|y\|^2}，$$
整理即得 $|\langle x, y \rangle|^2 \leq \|x\|^2 \|y\|^2$。

### 在 $L^2$ 空间中的应用

设 $f, g \in L^2[0, 1]$。Cauchy-Schwarz 给出
$$\left|\int_0^1 f(x)g(x) \, \mathrm{d}x\right| \leq \|f\|_{L^2} \|g\|_{L^2} = \left(\int_0^1 |f|^2\right)^{1/2}\left(\int_0^1 |g|^2\right)^{1/2}。$$

特别地，取 $g = 1$（常函数），得
$$\left|\int_0^1 f\right| \leq \left(\int_0^1 |f|^2\right)^{1/2}。$$
这说明 $L^2$ 平均控制 $L^1$ 平均（在有限测度空间上）。

### 方差-协方差不等式

对随机变量 $X, Y$，相关系数
$$\rho(X, Y) = \frac{\mathrm{Cov}(X, Y)}{\sigma_X \sigma_Y}$$
满足 $|\rho(X, Y)| \leq 1$。这直接是 Cauchy-Schwarz 在 Hilbert 空间 $L^2(\Omega, \mathcal{F}, \mathbb{P})$ 中的应用（内积为协方差）。

### 向量形式的三角不等式

由 Cauchy-Schwarz，
$$\|x + y\|^2 = \|x\|^2 + 2\,\mathrm{Re}\langle x, y \rangle + \|y\|^2 \leq \|x\|^2 + 2\|x\|\|y\| + \|y\|^2 = (\|x\| + \|y\|)^2。$$
故 $\|x + y\| \leq \|x\| + \|y\|$。这说明 Cauchy-Schwarz 是证明内积空间满足三角不等式的关键一步。

### 等周不等式的证明

设 $\gamma$ 为 $\mathbb{R}^2$ 中的闭曲线，长度为 $L$，围成面积为 $A$。等周不等式说 $4\pi A \leq L^2$。

利用 Fourier 级数：设 $\gamma$ 参数化为 $(x(t), y(t))$，$t \in [0, 2\pi]$。由 Cauchy-Schwarz（在序列空间 $\ell^2$ 中），
$$L^2 = \left(\int_0^{2\pi} \sqrt{x'(t)^2 + y'(t)^2} \, \mathrm{d}t\right)^2 \geq \cdots \geq 4\pi A。$$
等号成立当且仅当 $\gamma$ 为圆。

## 与其他概念的联系

### 与 Hölder 不等式的联系

Cauchy-Schwarz 是 Hölder 不等式在 $p = q = 2$ 时的特例。Hölder 说：对 $p, q > 1$，$1/p + 1/q = 1$，
$$\sum |x_i y_i| \leq \left(\sum |x_i|^p\right)^{1/p} \left(\sum |y_i|^q\right)^{1/q}。$$
$p = q = 2$ 时退化为 Cauchy-Schwarz。$p = 1, q = \infty$ 时退化为 $\sum |x_i y_i| \leq (\sum |x_i|) \sup |y_i|$。

### 与 Gram 矩阵的联系

对向量 $x_1, \ldots, x_n$，Gram 矩阵 $G = (\langle x_i, x_j \rangle)_{i,j}$ 是半正定的。Cauchy-Schwarz 正是 $n = 2$ 时 $\det G \geq 0$ 的展开：
$$\det G = \|x_1\|^2 \|x_2\|^2 - |\langle x_1, x_2 \rangle|^2 \geq 0。$$

### 与量子力学的联系

在量子力学中，Cauchy-Schwarz 不等式体现为**不确定性原理的数学基础**。对自伴算子 $A, B$，定义对易子 $[A, B] = AB - BA$。Robertson 不确定性关系：
$$\sigma_\psi(A) \sigma_\psi(B) \geq \frac{1}{2} |\langle \psi, [A, B] \psi \rangle|。$$
证明中关键一步是 Cauchy-Schwarz 于向量 $(A - \langle A \rangle)\psi$ 和 $(B - \langle B \rangle)\psi$。

## 参考

- Steele, J. M. (2004). *The Cauchy-Schwarz Master Class*. Cambridge University Press.
- Hardy, G. H., Littlewood, J. E., & Pólya, G. (1952). *Inequalities* (2nd ed.). Cambridge University Press.
- Cauchy, A.-L. (1821). *Cours d'Analyse de l'École Royale Polytechnique*. Paris.
- Schwarz, H. A. (1885). Über ein die Flächen kleinsten Flächeninhalts betreffendes Problem der Variationsrechnung. *Acta Societatis Scientiarum Fennicae*, 15, 315–362.
