---
title: Atiyah-Singer指标定理简介
description: 系统介绍椭圆算子的解析指标与拓扑指标、Atiyah-Singer指标定理的陈述与证明思路，以及其在Gauss-Bonnet、Hirzebruch符号差定理中的应用。
msc_primary:
  - 53C05
msc_secondary:
  - 58J20
  - 19K56
  - 58J22
processed_at: '2026-04-20'
references:
  textbooks:
    - id: lawson_michelsohn
      type: textbook
      title: Spin Geometry
      authors:
        - H. Blaine Lawson Jr.
        - Marie-Louise Michelsohn
      publisher: Princeton University Press
      year: 1989
      msc: 53-02
    - id: berline_getzler_vergne
      type: textbook
      title: Heat Kernels and Dirac Operators
      authors:
        - Nicole Berline
        - Ezra Getzler
        - Michèle Vergne
      publisher: Springer
      year: 2004
      msc: 58J35
---

# Atiyah-Singer指标定理简介

**椭圆算子的分析与拓扑 — 从Dirac算子到指标公式**

---

## 1. 椭圆微分算子

### 1.1 定义与基本性质

设 $M$ 为紧流形，$E, F \to M$ 为光滑向量丛。线性微分算子 $D: \Gamma(E) \to \Gamma(F)$ 在局部坐标下形如
$$(D\sigma)(x) = \sum_{|\alpha| \leq m} A_\alpha(x) \partial^\alpha \sigma(x)$$
其中 $A_\alpha(x) \in \text{Hom}(E_x, F_x)$。

**主符号**（principal symbol）定义为最高阶项的Fourier变换：
$$\sigma_m(D)(x, \xi) = \sum_{|\alpha| = m} A_\alpha(x) (i\xi)^\alpha \in \text{Hom}(E_x, F_x), \quad \xi \in T_x^*M$$

**定义**：$D$ 称为**椭圆算子**，若对任意 $x \in M$ 及非零 $\xi \in T_x^*M$，$\sigma_m(D)(x, \xi)$ 为可逆同构。

**例1（Laplace算子）**：$\Delta: C^\infty(M) \to C^\infty(M)$ 为二阶算子，主符号 $\sigma_2(\Delta)(x,\xi) = -|\xi|^2$，在 $\xi \neq 0$ 时可逆（作为 $\mathbb{R} \to \mathbb{R}$ 的数乘），故为椭圆算子。

**例2（Dirac算子）**：在旋量丛 $S \to M$ 上，Dirac算子 $\slashed{D} = \sum_i e^i \cdot \nabla_{e_i}$ 为一阶椭圆算子，主符号 $\sigma_1(\slashed{D})(x,\xi) = i\xi \cdot$（Clifford乘法），满足 $\sigma_1(\slashed{D})^2 = |\xi|^2 I$，故可逆。

### 1.2 Fredholm性质

**定理**：紧流形上的椭圆算子 $D: \Gamma(E) \to \Gamma(F)$ 为**Fredholm算子**，即
- $\ker D$ 有限维
- $\text{coker}\, D = \Gamma(F) / \text{im}\, D$ 有限维

**解析指标**定义为
$$\text{ind}(D) = \dim \ker D - \dim \text{coker}\, D = \dim \ker D - \dim \ker D^*$$
其中 $D^*$ 为形式伴随算子。

---

## 2. 拓扑指标

### 2.1 K-理论中的指标

Atiyah与Singer将解析指标提升到拓扑范畴。设 $K(M)$ 为 $M$ 的拓扑K-群（向量丛形式差的Grothendieck群）。符号 $\sigma(D)$ 定义了 $T^*M$ 上的K-理论类 $[\sigma(D)] \in K(T^*M)$（通过紧支集K-理论或球丛上的差丛）。

**拓扑指标**定义为Thom同构与推进的复合：
$$\text{ind}_t(D) = \text{ch}([\sigma(D)]) \smile \text{Td}(TM \otimes \mathbb{C}) / [M]$$
更精确地，通过Thom同构 $\phi: K(M) \to K(T^*M)$ 与Bott周期性，有同态
$$\text{ind}_t: K(T^*M) \to \mathbb{Z}$$

### 2.2 指标定理的陈述

**定理（Atiyah-Singer指标定理，1963）**：对紧流形 $M$ 上的任意椭圆微分算子 $D$，
$$\text{ind}(D) = \text{ind}_t(D)$$
即解析指标等于拓扑指标。

在可定向偶维流形上，若 $D: \Gamma(E) \to \Gamma(F)$，拓扑指标公式为
$$\text{ind}(D) = \int_M \text{ch}(E - F) \smile \frac{\text{Td}(TM \otimes \mathbb{C})}{e(TM)}$$
（具体形式依赖于算子类型与维数）。

---

## 3. 经典应用

### 3.1 Gauss-Bonnet-Chern定理

考虑de Rham算子 $D = d + d^*: \Omega^{\text{even}}(M) \to \Omega^{\text{odd}}(M)$。其核与余核满足
$$\ker D = \mathcal{H}^{\text{even}}(M), \quad \ker D^* = \mathcal{H}^{\text{odd}}(M)$$
故
$$\text{ind}(D) = \sum_{k} (-1)^k b_k = \chi(M)$$

Atiyah-Singer定理给出
$$\chi(M) = \int_M e(TM)$$
即**Gauss-Bonnet-Chern定理**。

### 3.2 Hirzebruch符号差定理

设 $M^{4k}$ 为定向闭流形。定义**符号差**（signature）为对称双线性形式
$$Q(\alpha, \beta) = \int_M \alpha \wedge \beta, \quad \alpha, \beta \in H^{2k}(M; \mathbb{R})$$
的符号（正特征值个数减负特征值个数），记为 $\sigma(M)$。

考虑算子 $D = d + d^*: \Omega^+ \to \Omega^-$，其中 $\Omega^\pm$ 为 $\pm 1$ 特征空间（由Hodge星 $*$ 在 middle degree 上的作用定义）。则
$$\text{ind}(D) = \sigma(M)$$

Atiyah-Singer给出**Hirzebruch符号差定理**：
$$\sigma(M) = \int_M L(M)$$
其中 $L$-类为Pontryagin类的形式积
$$L(M) = \prod_i \frac{x_i/2}{\tanh(x_i/2)}$$
$x_i$ 为形式Pontryagin根。

**例3（$\mathbb{CP}^{2k}$）**：$\sigma(\mathbb{CP}^{2k}) = 1$（因 $H^{2k}(\mathbb{CP}^{2k}) = \mathbb{R}$ 且 $Q$ 正定）。由Hirzebruch定理可验证 $L$-类的积分。

### 3.3 Riemann-Roch定理

对紧复流形 $M$ 及全纯向量丛 $E$，Dolbeault算子 $\bar{\partial} + \bar{\partial}^*: \Omega^{0,\text{even}}(E) \to \Omega^{0,\text{odd}}(E)$ 的指标为Euler特征
$$\text{ind}(\bar{\partial}_E) = \sum_q (-1)^q \dim H^q(M, \mathcal{O}(E)) = \chi(M, E)$$

Atiyah-Singer约化为**Hirzebruch-Riemann-Roch定理**：
$$\chi(M, E) = \int_M \text{ch}(E) \smile \text{Td}(TM)$$

**例4（曲线情形）**：对紧Riemann面 $C$（亏格 $g$）及线丛 $L = \mathcal{O}(D)$，
$$\chi(C, L) = \deg L + 1 - g$$
即经典Riemann-Roch定理。

---

## 4. 证明思路概述

### 4.1 热核方法

对自伴椭圆算子 $\Delta = D^*D \oplus DD^*$，热算子 $e^{-t\Delta}$ 为迹类。利用**McKean-Singer公式**：
$$\text{ind}(D) = \text{Tr}(e^{-tD^*D}) - \text{Tr}(e^{-tDD^*})$$
当 $t \to 0^+$，热核有渐近展开
$$\text{Tr}(e^{-t\Delta}) \sim \sum_{k \geq 0} t^{(k-n)/2} a_k(\Delta)$$
对 $D^*D$ 与 $DD^*$，$a_k$ 的差在 $k=n$ 时给出局部示性类积分，即拓扑指标。

### 4.2 公理化方法

Atiyah-Singer原始证明利用：
1. **K-理论提升**：将椭圆算子嵌入 $K$-理论框架；
2. **Thom同构**：$K(T^*M) \cong K(M)$（对紧流形需适当紧化）；
3. **Bott周期性**：$K(S^2) \cong K(\text{pt})$；
4. **函子性**：验证 $\text{ind}$ 与 $\text{ind}_t$ 满足相同的函子公理（切除、同伦不变性等），由唯一性定理得二者相等。

---

## 5. 推广与影响

### 5.1 等变指标定理

设紧Lie群 $G$ 作用在 $M$ 上且与 $D$ 交换。则 $\ker D$ 与 $\text{coker}\, D$ 为 $G$-表示，**等变指标**为虚拟表示的差。Atiyah-Segal等变指标定理将其表达为不动点集上的局部贡献之和（Atiyah-Bott-Berline-Vergne局部化公式）。

### 5.2 非交换几何指标定理

Connes将指标理论推广到非交换空间（由 $C^*$-代数描述），建立了非交换微分几何的指标定理，在叶状结构、动力系统等场景有重要应用。

---

## 6. 小结

Atiyah-Singer指标定理是二十世纪数学的里程碑之一，它将椭圆分析的Fredholm指标与示性类的拓扑积分统一起来。Gauss-Bonnet、Riemann-Roch、Hirzebruch符号差等经典定理均成为其特例，展示了指标理论的深刻统一力量。热核局部化与K-理论公理化两种证明途径分别代表了分析与代数的最高成就，至今仍激励着几何分析与非交换几何的前沿发展。
