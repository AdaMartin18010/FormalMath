---
msc_primary: "40A05"
msc_secondary:
  - 26A03
  - 54E45
---

# 概念卡片：Bolzano-Weierstrass定理

## 严格定义

**Bolzano-Weierstrass 定理**：在欧氏空间 $\mathbb{R}^n$（或更一般地，有限维赋范空间）中，任何有界序列都有收敛子列。

等价表述：

- $\mathbb{R}^n$ 中的有界无穷子集必有聚点；
- 闭有界集是序列紧致的。

**与紧致性的关系**：在度量空间中，序列紧致 $\Leftrightarrow$ 紧致 $\Leftrightarrow$ 完全有界且完备。Bolzano-Weierstrass 定理是 Heine-Borel 定理在序列语言中的对应物。

## 历史背景

Bolzano-Weierstrass 定理的历史是分析学严格化进程的核心篇章。

**Bolzano 的原创证明（1817）**：捷克数学家、哲学家 Bernard Bolzano（1781–1848）在 1817 年的论文《纯粹分析的证明》中证明了有界实数集的上确界存在性，并隐含地证明了有界序列有收敛子列。他的动机是为介值定理提供一个"纯粹分析的"（即不依赖几何直观）的证明。Bolzano 使用了**区间套**方法——将有界区间不断二分，选择包含无穷多项的那一半——这一方法至今仍是标准证明的核心。

**Weierstrass 的系统化（1860s）**：Karl Weierstrass（1815–1897）在柏林大学的讲义中系统发展了 Bolzano 的思想，将有界序列的收敛子列存在性作为分析学的基础工具。Weierstrass 的分析算术化纲领——用 $\varepsilon$-$\delta$ 语言严格定义极限、连续性和收敛性——使得 Bolzano-Weierstrass 定理成为不可或缺的基石。

**公理化与推广（1900–1950）**：随着点集拓扑和泛函分析的发展，Bolzano-Weierstrass 定理被抽象为度量空间中的序列紧致性概念。Eberlein-Šmulian 定理将其推广到 Banach 空间的弱拓扑：弱闭且有界集在弱拓扑下是弱序列紧致的。

## 直观理解

Bolzano-Weierstrass 定理的直观是**"无限鸽子必须挤进有限鸽笼"**。

想象一个无穷序列的点被限制在一个有限区域内（如有界区间 $[a, b]$）。将这些点不断分类到越来越小的子区域中：第一次分为左右两半，至少一半包含无穷多个点；将那一半再分为两半，又至少一半包含无穷多个点……如此无限进行。

这个过程产生了一个嵌套的区间套 $[a_1, b_1] \supset [a_2, b_2] \supset \cdots$，其长度趋于零。由区间套定理（完备公理的推论），这些区间的交为单点 $\{c\}$。从每个区间中选取一个序列中的点，就得到一个收敛到 $c$ 的子列。

**有限维的关键**：在 $\mathbb{R}^n$ 中，有界性意味着可以被封闭在"有限体积"的区域内。在无限维空间中，单位球"太大"——存在无穷多个两两距离为常数的点（如 $\ell^2$ 中的标准基），因此 Bolzano-Weierstrass 定理失效。

## 数学例子

### 标准证明（区间套法）

设 $\{x_n\} \subseteq [a, b]$ 为有界序列。

1. 令 $I_0 = [a, b]$。将 $I_0$ 二等分为 $[a, (a+b)/2]$ 和 $[(a+b)/2, b]$。至少一个子区间包含 $\{x_n\}$ 的无穷多项，记为 $I_1$。
2. 递归地，将 $I_{k-1}$ 二等分，选取包含无穷多项的那一半为 $I_k$。
3. 得到区间套 $I_0 \supset I_1 \supset I_2 \supset \cdots$，$|I_k| = (b-a)/2^k \to 0$。
4. 由完备性，$\bigcap_k I_k = \{c\}$ 对某个 $c \in [a, b]$。
5. 从 $I_k$ 中选取 $x_{n_k}$（$n_k > n_{k-1}$）。则 $|x_{n_k} - c| \leq |I_k| \to 0$，故 $x_{n_k} \to c$。

### 应用到连续函数的有界性

**定理**：$[a, b]$ 上的连续函数 $f$ 有界。

**证明**：假设 $f$ 无界。则对每个 $n$，存在 $x_n \in [a, b]$ 使得 $|f(x_n)| > n$。由 Bolzano-Weierstrass，$\{x_n\}$ 有收敛子列 $x_{n_k} \to c \in [a, b]$。由连续性，$f(x_{n_k}) \to f(c)$。但 $|f(x_{n_k})| > n_k \to \infty$，矛盾。

### 有限维推广

**定理**：$\mathbb{R}^n$ 中的有界序列有收敛子列。

**证明**：对 $n = 2$ 演示。设 $\{(x_k, y_k)\}$ 有界。则 $\{x_k\}$ 有界，有收敛子列 $x_{k_j} \to x$。子列 $\{y_{k_j}\}$ 仍有界，故有子子列 $y_{k_{j_l}} \to y$。则 $(x_{k_{j_l}}, y_{k_{j_l}}) \to (x, y)$。

### 无限维反例

在 $\ell^2$ 中，标准基 $e_n = (0, \ldots, 0, 1, 0, \ldots)$ 满足 $\|e_n\| = 1$（有界），但 $\|e_n - e_m\| = \sqrt{2}$（$n \neq m$）。故无 Cauchy 子列，更无收敛子列。

## 与其他概念的联系

### 与完备性的联系

Bolzano-Weierstrass 定理等价于实数的完备性公理（Dedekind 完备性、区间套定理、确界原理等都是等价的）。具体地：

- 由完备性 $\Rightarrow$ Bolzano-Weierstrass（区间套证明）；
- 由 Bolzano-Weierstrass $\Rightarrow$ Cauchy 收敛：Cauchy 列必有界，故有收敛子列，从而整列收敛。

### 与弱紧性的联系

在无限维 Banach 空间中，范数拓扑下的 Bolzano-Weierstrass 定理失效。但 Eberlein-Šmulian 定理说：Banach 空间的闭单位球在**弱拓扑**下是序列紧致的。这是分析学中极为重要的结果，广泛应用于变分法和偏微分方程。

例如，在 Sobolev 空间 $H^1_0(\Omega)$ 中，有界序列不一定在范数拓扑下收敛，但必有弱收敛子列。这使得我们可以通过取弱极限来获得极小化序列的极限，是能量泛函极小化存在性证明的核心工具。

### 与概率论的联系

在概率论中，Helly 选择定理是 Bolzano-Weierstrass 精神在测度论中的体现：任何一致有界的分布函数序列都有子列弱收敛到一个单调右连续函数。Prokhorov 定理进一步刻画了度量空间中概率测度族的弱紧致性条件（胎紧性）。

## 参考

- Rudin, W. (1976). *Principles of Mathematical Analysis* (3rd ed.). McGraw-Hill.
- Bolzano, B. (1817). Rein analytischer Beweis des Lehrsatzes, dass zwischen je zwei Werthen, die ein entgegengesetztes Resultat gewähren, wenigstens eine reelle Wurzel der Gleichung liege. *Prague*.
- Weierstrass, K. (1874). *Einleitung in die Theorie der analytischen Funktionen*. Vorlesung, Berlin.
- Conway, J. B. (1990). *A Course in Functional Analysis* (2nd ed.). Springer.
