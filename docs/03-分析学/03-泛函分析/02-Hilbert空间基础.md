---
msc_primary: 46C05
msc_secondary:
  - 46C07
  - 46C15
processed_at: '2026-04-20'
title: Hilbert空间基础
---

# Hilbert空间基础

## 1. 引言

Hilbert空间是装备了内积的完备线性空间，由David Hilbert在研究积分方程时系统发展。与一般的Banach空间相比，Hilbert空间拥有更丰富的几何结构：正交性、正交投影、标准正交基等概念使得无穷维空间中的分析更接近于有限维欧几里得空间的几何直观。本文从内积的定义出发，系统建立Hilbert空间的核心理论，包括正交分解、Riesz表示定理、标准正交基以及刻画Hilbert空间特征的Parallelogram定律。

## 2. 内积空间

### 2.1 内积的定义

**定义 2.1**（内积）。设 $X$ 是域 $\mathbb{K}$（$\mathbb{R}$ 或 $\mathbb{C}$）上的线性空间。映射 $\langle \cdot, \cdot \rangle: X \times X \to \mathbb{K}$ 称为**内积**（inner product），若满足：

1. **共轭对称性**：$\langle x, y \rangle = \overline{\langle y, x \rangle}$；
2. **对第一个变量的线性**：$\langle \alpha x + \beta y, z \rangle = \alpha \langle x, z \rangle + \beta \langle y, z \rangle$；
3. **正定性**：$\langle x, x \rangle \geq 0$，且 $\langle x, x \rangle = 0 \Leftrightarrow x = 0$。

由共轭对称性，对第二个变量有共轭线性：$\langle x, \alpha y + \beta z \rangle = \bar{\alpha} \langle x, y \rangle + \bar{\beta} \langle x, z \rangle$。实内积空间中对两个变量都是线性的。

**命题 2.2**（Cauchy-Schwarz不等式）。设 $(X, \langle \cdot, \cdot \rangle)$ 为内积空间，则对所有 $x, y \in X$，
$$|\langle x, y \rangle|^2 \leq \langle x, x \rangle \langle y, y \rangle.$$
等号成立当且仅当 $x$ 与 $y$ 线性相关。

*证明*。若 $y = 0$ 结论显然。设 $y \neq 0$，对任意 $\lambda \in \mathbb{K}$，由内积正定性：
$$0 \leq \langle x - \lambda y, x - \lambda y \rangle = \langle x, x \rangle - \bar{\lambda} \langle x, y \rangle - \lambda \langle y, x \rangle + |\lambda|^2 \langle y, y \rangle.$$
取 $\lambda = \frac{\langle x, y \rangle}{\langle y, y \rangle}$，代入得：
$$0 \leq \langle x, x \rangle - \frac{|\langle x, y \rangle|^2}{\langle y, y \rangle},$$
即 $|\langle x, y \rangle|^2 \leq \langle x, x \rangle \langle y, y \rangle$。$\square$

**推论 2.3**。由内积可诱导范数 $\|x\| = \sqrt{\langle x, x \rangle}$。Cauchy-Schwarz不等式等价于 $|\langle x, y \rangle| \leq \|x\| \|y\|$。

*验证范数公理*：正定性由定义直接得到；齐次性：$\|\alpha x\| = \sqrt{\langle \alpha x, \alpha x \rangle} = \sqrt{|\alpha|^2 \langle x, x \rangle} = |\alpha| \|x\|$；三角不等式：
$$\|x + y\|^2 = \|x\|^2 + 2\operatorname{Re}\langle x, y \rangle + \|y\|^2 \leq \|x\|^2 + 2\|x\|\|y\| + \|y\|^2 = (\|x\| + \|y\|)^2.$$

### 2.2 Hilbert空间的定义

**定义 2.4**。内积空间 $(X, \langle \cdot, \cdot \rangle)$ 称为**Hilbert空间**，若其关于诱导范数 $\|x\| = \sqrt{\langle x, x \rangle}$ 完备，即为Banach空间。

## 3. Parallelogram定律与Jordan-von Neumann定理

### 3.1 Parallelogram定律

**定理 3.1**（Parallelogram定律）。在内积空间中，对任意 $x, y$：
$$\|x + y\|^2 + \|x - y\|^2 = 2(\|x\|^2 + \|y\|^2).$$

*证明*。直接展开：
$$\|x + y\|^2 = \|x\|^2 + 2\operatorname{Re}\langle x, y \rangle + \|y\|^2,$$
$$\|x - y\|^2 = \|x\|^2 - 2\operatorname{Re}\langle x, y \rangle + \|y\|^2.$$
相加即得。$\square$

**几何解释**：平行四边形两对角线长度的平方和等于四边长度的平方和。这是欧几里得几何在内积空间中的直接推广。

### 3.2 判定定理

**定理 3.2**（Jordan-von Neumann）。赋范线性空间 $(X, \|\cdot\|)$ 的范数可由某内积诱导，当且仅当其满足Parallelogram定律。此时内积由**极化恒等式**唯一确定：
- 实情形：$\langle x, y \rangle = \frac{1}{4}(\|x+y\|^2 - \|x-y\|^2)$；
- 复情形：$\langle x, y \rangle = \frac{1}{4}(\|x+y\|^2 - \|x-y\|^2 + i\|x+iy\|^2 - i\|x-iy\|^2)$。

*证明概要*。必要性已由定理3.1证明。充分性：假设Parallelogram定律成立，用极化恒等式定义 $\langle x, y \rangle$，验证其满足内积公理。共轭对称性与正定性较易验证，难点在于证明对第一个变量的线性——这需要反复应用Parallelogram定律。$\square$

**例 3.3**。$L^2(\Omega, \mu)$ 满足Parallelogram定律：
$$\|f+g\|_2^2 + \|f-g\|_2^2 = \int(|f+g|^2 + |f-g|^2)d\mu = 2\int(|f|^2 + |g|^2)d\mu = 2(\|f\|_2^2 + \|g\|_2^2).$$
对应的内积为 $\langle f, g \rangle = \int f \bar{g} \, d\mu$。

**例 3.4**。$L^p[0,1]$（$p \neq 2$）不满足Parallelogram定律，故非Hilbert空间。取 $f = \chi_{[0,1/2]}$，$g = \chi_{[1/2,1]}$，则 $\|f\|_p = \|g\|_p = (1/2)^{1/p}$，$\|f+g\|_p = \|f-g\|_p = 1$。Parallelogram定律要求 $1 + 1 = 2 \cdot 2 \cdot (1/2)^{2/p}$，即 $2 = 4 \cdot 2^{-2/p}$，仅当 $p = 2$ 成立。

## 4. 正交性与正交投影

### 4.1 正交补

**定义 4.1**。设 $X$ 为内积空间，$x, y \in X$。若 $\langle x, y \rangle = 0$，称 $x$ 与 $y$ **正交**（orthogonal），记作 $x \perp y$。对子集 $S \subseteq X$，定义其**正交补**
$$S^\perp = \{ x \in X : \langle x, s \rangle = 0, \forall s \in S \}.$$

**命题 4.2**。$S^\perp$ 是 $X$ 的闭子空间（不论 $S$ 是否为子空间），且 $S \subseteq (S^\perp)^\perp$。若 $M$ 为子空间，则 $M \cap M^\perp = \{0\}$。

### 4.2 正交投影定理

**定理 4.3**（正交投影）。设 $H$ 为Hilbert空间，$M \subseteq H$ 为闭子空间。则对每个 $x \in H$，存在唯一的 $y \in M$（称为 $x$ 在 $M$ 上的**正交投影**），使得
$$\|x - y\| = \inf_{m \in M} \|x - m\| = \operatorname{dist}(x, M).$$
等价地，$x - y \in M^\perp$。由此得到**正交分解**：
$$H = M \oplus M^\perp.$$

*证明*。存在性：设 $d = \operatorname{dist}(x, M)$，取序列 $(y_n) \subseteq M$ 使得 $\|x - y_n\| \to d$。应用Parallelogram定律于 $x - y_n$ 和 $x - y_m$：
$$\|2x - (y_n + y_m)\|^2 + \|y_n - y_m\|^2 = 2(\|x - y_n\|^2 + \|x - y_m\|^2).$$
由于 $\frac{y_n + y_m}{2} \in M$，有 $\|x - \frac{y_n + y_m}{2}\| \geq d$，即 $\|2x - (y_n + y_m)\| \geq 2d$。代入得
$$\|y_n - y_m\|^2 \leq 2(\|x - y_n\|^2 + \|x - y_m\|^2) - 4d^2 \to 0.$$
故 $(y_n)$ 为Cauchy列，由 $M$ 闭，$y_n \to y \in M$，且 $\|x - y\| = d$。

唯一性：若 $y, y' \in M$ 都达到距离 $d$，由上述论证 $\|y - y'\| = 0$。

正交性：对任意 $m \in M$，考虑函数 $\varphi(t) = \|x - (y + tm)\|^2 = \|x - y\|^2 - 2t\operatorname{Re}\langle x - y, m \rangle + t^2\|m\|^2$。在 $t = 0$ 处取最小值，故 $\varphi'(0) = -2\operatorname{Re}\langle x - y, m \rangle = 0$。类似处理虚部，得 $\langle x - y, m \rangle = 0$。$\square$

**推论 4.4**。若 $M$ 为Hilbert空间 $H$ 的闭子空间，则 $(M^\perp)^\perp = M$。

### 4.3 投影算子

**定义 4.5**。由定理4.3，可定义**正交投影算子** $P_M: H \to M$，$P_M(x) = y$，其中 $y$ 为 $x$ 在 $M$ 上的唯一最近点。

**命题 4.6**。$P_M$ 是有界线性算子，$\|P_M\| = 1$（当 $M \neq \{0\}$ 时），且满足 $P_M^2 = P_M$，$P_M^* = P_M$（自伴性）。

## 5. Riesz表示定理

**定理 5.1**（Riesz表示定理）。设 $H$ 为Hilbert空间。对每个连续线性泛函 $f \in H^*$，存在唯一的 $y \in H$ 使得
$$f(x) = \langle x, y \rangle, \quad \forall x \in H,$$
且 $\|f\| = \|y\|$。映射 $y \mapsto f_y$（其中 $f_y(x) = \langle x, y \rangle$）是 $H$ 到 $H^*$ 的共轭线性等距同构。

*证明*。存在性：若 $f = 0$，取 $y = 0$。设 $f \neq 0$，则 $\ker f$ 是 $H$ 的真闭子空间。由正交分解，$(\ker f)^\perp \neq \{0\}$。取 $z \in (\ker f)^\perp$ 且 $z \neq 0$，则 $f(z) \neq 0$。对任意 $x \in H$，
$$f\left(x - \frac{f(x)}{f(z)} z\right) = f(x) - \frac{f(x)}{f(z)} f(z) = 0,$$
故 $x - \frac{f(x)}{f(z)} z \in \ker f$，从而与 $z$ 正交：
$$\left\langle x - \frac{f(x)}{f(z)} z, z \right\rangle = 0 \Rightarrow f(x) = \frac{f(z)}{\|z\|^2} \langle x, z \rangle = \left\langle x, \frac{\overline{f(z)}}{\|z\|^2} z \right\rangle.$$
令 $y = \frac{\overline{f(z)}}{\|z\|^2} z$ 即可。

唯一性：若 $\langle x, y_1 \rangle = \langle x, y_2 \rangle$ 对所有 $x$ 成立，则 $\langle x, y_1 - y_2 \rangle = 0$，取 $x = y_1 - y_2$ 得 $y_1 = y_2$。

等距性：$|f_y(x)| = |\langle x, y \rangle| \leq \|x\| \|y\|$，故 $\|f_y\| \leq \|y\|$。又 $|f_y(y)| = \|y\|^2$，故 $\|f_y\| \geq \|y\|$。$\square$

**注记 5.2**。Riesz表示定理说明Hilbert空间是自反的（通过共轭线性等构 $H \cong H^*$），且 $H^{**} \cong H$。这是Hilbert空间相较于一般Banach空间的重大优势。

## 6. 标准正交基

### 6.1 标准正交系

**定义 6.1**。Hilbert空间 $H$ 中的集合 $\{e_\alpha\}_{\alpha \in I}$ 称为**标准正交系**（orthonormal system），若
$$\langle e_\alpha, e_\beta \rangle = \delta_{\alpha\beta} = \begin{cases} 1, & \alpha = \beta, \\ 0, & \alpha \neq \beta. \end{cases}$$

**定理 6.2**（Bessel不等式）。设 $\{e_n\}_{n=1}^\infty$ 为Hilbert空间 $H$ 中的标准正交列，则对任意 $x \in H$，
$$\sum_{n=1}^\infty |\langle x, e_n \rangle|^2 \leq \|x\|^2.$$

*证明*。对任意 $N$，令 $y_N = x - \sum_{n=1}^N \langle x, e_n \rangle e_n$。直接计算得 $y_N \perp e_k$（$k \leq N$），故
$$\|x\|^2 = \|y_N\|^2 + \sum_{n=1}^N |\langle x, e_n \rangle|^2 \geq \sum_{n=1}^N |\langle x, e_n \rangle|^2.$$
令 $N \to \infty$ 即得。$\square$

### 6.2 标准正交基的定义

**定义 6.3**。标准正交系 $\{e_\alpha\}$ 称为**标准正交基**（orthonormal basis），若其张成的线性子空间在 $H$ 中稠密。等价地，$x = \sum_{\alpha} \langle x, e_\alpha \rangle e_\alpha$（Fourier展开），且 $\|x\|^2 = \sum_{\alpha} |\langle x, e_\alpha \rangle|^2$（Parseval等式）。

**定理 6.4**。每个非零Hilbert空间都有标准正交基。可分Hilbert空间具有可数标准正交基。

*证明概要*。应用Zorn引理于全体标准正交系（按包含关系偏序），极大元必为标准正交基。$\square$

### 6.3 典型例子

**例 6.5**。$l^2$ 的标准正交基为 $\{e^{(n)}\}$，其中 $e^{(n)}$ 为第 $n$ 个标准基向量。对 $x = (x_n) \in l^2$，Fourier展开即为 $x = \sum_{n=1}^\infty x_n e^{(n)}$。

**例 6.6**。$L^2[0, 2\pi]$ 的标准正交基可取 Fourier 系 $\{\frac{1}{\sqrt{2\pi}} e^{inx}\}_{n \in \mathbb{Z}}$。对 $f \in L^2[0, 2\pi]$，有
$$f = \sum_{n=-\infty}^\infty \hat{f}(n) \frac{e^{inx}}{\sqrt{2\pi}}, \quad \hat{f}(n) = \frac{1}{\sqrt{2\pi}} \int_0^{2\pi} f(x) e^{-inx} dx.$$
Parseval等式给出 $\|f\|_2^2 = \sum_{n=-\infty}^\infty |\hat{f}(n)|^2$。

**例 6.7**。$L^2[-1, 1]$ 有标准正交基 $\{\sqrt{n + \frac{1}{2}} P_n(x)\}$，其中 $P_n$ 为Legendre多项式：
$$P_n(x) = \frac{1}{2^n n!} \frac{d^n}{dx^n}(x^2 - 1)^n.$$

## 7. 同构分类

**定理 7.1**。两个Hilbert空间等距同构，当且仅当它们具有相同的Hilbert维数（标准正交基的基数）。特别地，每个可分无穷维Hilbert空间都与 $l^2$ 等距同构。

*证明*。设 $\{e_\alpha\}$ 和 $\{f_\alpha\}$ 分别为 $H_1$ 和 $H_2$ 的标准正交基，指标集同为 $I$。定义 $U: H_1 \to H_2$ 为
$$U\left(\sum_{\alpha} c_\alpha e_\alpha\right) = \sum_{\alpha} c_\alpha f_\alpha.$$
由Parseval等式，$U$ 是良定义的等距同构。$\square$

**推论 7.2**。无穷维可分复Hilbert空间的结构完全由其维数决定，在同构意义下只有 $l^2(\mathbb{C}^n)$（$n = 1, 2, \ldots$）和 $l^2 = l^2(\mathbb{N})$ 这些模型。

## 8. 与项目其他部分的关联

Hilbert空间的理论是量子力学的数学基础，波函数即Hilbert空间中的向量，可观测量对应自伴算子（见[03-有界线性算子](03-有界线性算子.md)与[04-谱理论基础](04-谱理论基础.md)）。正交投影与Riesz表示定理在偏微分方程的变分方法中具有核心地位，弱解的存在性往往依赖于Hilbert空间的结构。Sobolev空间 $H^k = W^{k,2}$ 是Hilbert空间，这使得椭圆型方程的研究特别便利（见[10-Sobolev空间](10-Sobolev空间.md)）。

## 9. 参考文献

1. D. Hilbert, *Grundzüge einer allgemeinen Theorie der linearen Integralgleichungen*, Teubner, 1912.
2. J. von Neumann, *Mathematische Grundlagen der Quantenmechanik*, Springer, 1932.
3. P. Jordan & J. von Neumann, "On inner products in linear, metric spaces", *Ann. Math.* 36 (1935), 719–723.
4. W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw-Hill, 1987.
5. 郑维行、王声望，《实变函数与泛函分析概要》（第四版），高等教育出版社，2010。
