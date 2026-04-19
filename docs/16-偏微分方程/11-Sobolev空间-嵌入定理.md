---
title: Sobolev空间-嵌入定理
description: 系统介绍Sobolev嵌入定理、Rellich-Kondrachov紧嵌入、Morrey不等式与Hölder连续性、Sobolev不等式与最佳常数，建立Sobolev分析的核心结果。
msc_primary:
  - 46E35
msc_secondary:
  - 46E30
  - 35B45
  - 35A23
processed_at: '2026-04-20'
references:
  textbooks:
    - id: evans_pde
      type: textbook
      title: Partial Differential Equations
      authors:
        - Lawrence C. Evans
      publisher: American Mathematical Society
      year: 2010
      msc: 35-01
    - id: adams_sobolev
      type: textbook
      title: Sobolev Spaces
      authors:
        - Robert A. Adams
        - John J. F. Fournier
      publisher: Academic Press
      year: 2003
      msc: 46E35
---

# Sobolev空间-嵌入定理

**从可积性到连续性 — Sobolev嵌入的阶梯**

---

## 1. 嵌入定理的动机

Sobolev空间 $W^{k,p}(\Omega)$ 中的函数仅有 $L^p$ 可积的各阶弱导数。嵌入定理回答：这些函数是否自动具有更高的可积性、连续性甚至光滑性？答案依赖于空间的维数 $n$、可积指数 $p$ 与正则阶数 $k$ 的关系。

---

## 2. Gagliardo-Nirenberg-Sobolev不等式

### 2.1 $W^{1,p}$ 嵌入 $L^{p^*}$

设 $1 \leq p < n$。定义**Sobolev共轭指数**
$$p^* = \frac{np}{n-p}$$

**定理（Gagliardo-Nirenberg-Sobolev不等式）**：存在 $C = C(n,p)$ 使得
$$\|u\|_{L^{p^*}(\mathbb{R}^n)} \leq C\|\nabla u\|_{L^p(\mathbb{R}^n)}, \quad \forall u \in C_c^1(\mathbb{R}^n)$$

由此，$W^{1,p}(\mathbb{R}^n) \hookrightarrow L^{p^*}(\mathbb{R}^n)$ 连续嵌入。

*证明概要*（$p=1$ 情形）：对 $u \in C_c^1$，
$$|u(x)| \leq \int_{-\infty}^{x_i} |\partial_i u| dx_i$$
对所有 $i$ 乘积后取 $n/(n-1)$ 次根，积分得 $\|u\|_{L^{n/(n-1)}} \leq \prod_i \|\partial_i u\|_{L^1}^{1/n} \leq C\|\nabla u\|_{L^1}$。对一般 $p$，以 $|u|^\gamma$ 代替 $u$ 并优化 $\gamma$。$\square$

### 2.2 最佳常数

对 $p=2$，最佳常数由Talenti（1976）给出，极值函数为
$$u(x) = (1 + |x|^2)^{-(n-2)/2}$$
（经放缩与平移）。这与Yamabe问题有深刻联系。

---

## 3. Sobolev嵌入定理

### 3.1 连续嵌入

设 $\Omega \subset \mathbb{R}^n$ 为有界 $C^1$ 域。

**定理（Sobolev嵌入）**：

1. 若 $k < n/p$，则 $W^{k,p}(\Omega) \hookrightarrow L^q(\Omega)$ 对任意 $q \leq p^* = \frac{np}{n-kp}$；
2. 若 $k = n/p$，则 $W^{k,p}(\Omega) \hookrightarrow L^q(\Omega)$ 对任意 $q < \infty$；
3. 若 $k > n/p$，则 $W^{k,p}(\Omega) \hookrightarrow C^{k-[n/p]-1,\gamma}(\overline{\Omega})$，其中 $\gamma = [n/p] + 1 - n/p$（若 $n/p$ 非整数）或任意 $\gamma < 1$（若 $n/p$ 为整数）。

**关键指数**：$k - n/p$ 称为**Sobolev数**。嵌入的靶空间取决于其符号：负（$L^q$）、零（临界 $L^q$ 或 BMO）、正（Hölder连续）。

### 3.2 临界情形 $p = n$

当 $kp = n$ 时，$W^{k,p}$ 几乎但不完全连续嵌入。Trudinger证明：$W^{1,n}(\Omega) \hookrightarrow L_\varphi(\Omega)$，其中 $L_\varphi$ 为Orlicz空间，$
abla f$ 为 $\exp(\alpha |u|^{n/(n-1)})$ 型。特别地，$e^{\alpha |u|^{n/(n-1)}} \in L^1$ 对某 $\alpha > 0$。

---

## 4. Morrey不等式

### 4.1 $p > n$ 的情形

**定理（Morrey不等式）**：设 $n < p \leq \infty$。存在 $C = C(n,p)$ 使得
$$\|u\|_{C^{0,\gamma}(\mathbb{R}^n)} \leq C\|u\|_{W^{1,p}(\mathbb{R}^n)}, \quad \gamma = 1 - \frac{n}{p}$$
对所有 $u \in C^1(\mathbb{R}^n)$。

即 $W^{1,p}(\Omega) \hookrightarrow C^{0,\gamma}(\overline{\Omega})$。

*证明*：对球 $B(x,r)$，由Hölder，
$$\int_{B(x,r)} |\nabla u| \leq Cr^{n(1-1/p)}\|\nabla u\|_{L^p}$$
利用Poincaré不等式与 Campanato 空间刻画，得Hölder连续性。$\square$

### 4.2 意义

$p > n$ 时，$W^{1,p}$ 函数不仅连续，且具有一致Hölder连续模。这在非线性PDE的先验估计中极为重要。

**例1**：$n=1$ 时，$W^{1,1}(\mathbb{R}) \hookrightarrow L^\infty(\mathbb{R})$（因 $u(x) - u(y) = \int_y^x u'$，取 $y \to -\infty$ 得 $|u(x)| \leq \|u'\|_{L^1}$）。故一维 $W^{1,p}$ 函数连续。

**例2**：$n=2$ 时，$W^{1,2}$ 不嵌入 $L^\infty$（存在无界Sobolev函数，如 $\log\log(1/|x|)$ 在二维）。需要 $p > 2$ 才保证连续。

---

## 5. Rellich-Kondrachov紧嵌入

### 5.1 紧性

连续嵌入 $X \hookrightarrow Y$ 称为**紧的**，若闭单位球的像为 $Y$ 中的相对紧集。

**定理（Rellich-Kondrachov）**：设 $\Omega$ 有界且 $C^1$。

1. 若 $k < n/p$ 且 $q < p^*$，则 $W^{k,p}(\Omega) \hookrightarrow L^q(\Omega)$ **紧**；
2. 若 $k > n/p$，则 $W^{k,p}(\Omega) \hookrightarrow C^{m,\alpha}(\overline{\Omega})$ **紧**（对适当的 $m,\alpha$）。

### 5.2 意义

紧嵌入是椭圆方程谱理论与Galerkin近似的关键。由Riesz定理，紧算子的谱为离散趋于零的序列，这直接导出Laplace算子的特征值离散性。

---

## 6. 高阶嵌入

### 6.1 一般规律

对 $W^{k,p}(\Omega)$，有效正则性由 $k - n/p$ 决定：
- $k - n/p < 0$：嵌入 $L^q$，$q = np/(n-kp)$；
- $k - n/p = 0$：嵌入任意 $L^q$（$q < \infty$）或临界Orlicz/指数空间；
- $k - n/p > 0$：嵌入 $C^{m,\alpha}$，$m = \lfloor k - n/p \rfloor$。

### 6.2 插值不等式

**Gagliardo-Nirenberg插值**：对 $0 \leq j < k$，$1 \leq q, r \leq \infty$，
$$\|D^j u\|_{L^p} \leq C\|D^k u\|_{L^r}^\alpha \|u\|_{L^q}^{1-\alpha}$$
其中 $1/p = j/n + \alpha(1/r - k/n) + (1-\alpha)/q$。

这允许用低阶范数与高阶范数控制中间阶范数。

---

## 7. 小结

Sobolev嵌入定理是分析中最深刻也最有用的结果之一。它以精确的方式量化了"积分多少阶导数可换取多少可积性或连续性"。Gagliardo-Nirenberg-Sobolev不等式与Morrey不等式分别覆盖了 $p < n$ 与 $p > n$ 的情形，Rellich-Kondrachov紧嵌入则赋予这一理论以谱论与逼近论的力量。临界情形的精细分析（Trudinger不等式、Brezis-Merle估计等）仍在当代几何分析中扮演着中心角色。
