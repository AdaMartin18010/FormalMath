---
msc_primary: 47A53
msc_secondary:
  - 47B06
  - 58J20
processed_at: '2026-04-20'
title: Fredholm理论
---

# Fredholm理论

## 1. 引言

Fredholm理论起源于瑞典数学家Erik Ivar Fredholm在1903年对积分方程的系统研究。他建立的"Fredholm择一性"揭示了第二类积分方程的深刻结构：解的存在性与唯一性二者必居其一。这一理论在20世纪被F. Riesz、Schauder、Atkinson等人推广到Banach空间上的一般算子，形成了现代Fredholm算子理论。其核心思想是：尽管无穷维空间中的算子可能既非单射也非满射，但存在一类"几乎可逆"的算子——Fredholm算子，它们具有有限维的核与余核，且其"亏量"（指标）在紧扰动下保持不变。这一理论在指标定理、椭圆型偏微分方程以及数学物理中具有基础性地位。

## 2. Fredholm算子的定义

### 2.1 基本定义

**定义 2.1**。设 $X, Y$ 为Banach空间。有界线性算子 $T \in \mathcal{B}(X,Y)$ 称为**Fredholm算子**，若：
1. 核（零空间）$\ker T = \{x \in X : Tx = 0\}$ 有限维；
2. 值域 $\operatorname{ran} T = \{Tx : x \in X\}$ 闭；
3. 余核 $\operatorname{coker} T = Y / \operatorname{ran} T$ 有限维。

**定义 2.2**。Fredholm算子 $T$ 的**指标**（index）定义为
$$\operatorname{ind}(T) = \dim \ker T - \dim \operatorname{coker} T = \dim \ker T - \dim \ker T^*.$$

**注记 2.3**。条件(2)（值域闭）实际上是冗余的：若 $\ker T$ 有限维且 $\operatorname{coker} T$ 有限维，则 $\operatorname{ran} T$ 自动闭。但在实际验证中常需单独检验。

### 2.2 等价刻画

**定理 2.4**。$T \in \mathcal{B}(X,Y)$ 为Fredholm算子，当且仅当存在 $S \in \mathcal{B}(Y,X)$ 使得
$$ST - I_X \in \mathcal{K}(X), \quad TS - I_Y \in \mathcal{K}(Y).$$
此时 $S$ 称为 $T$ 的**参数化子**（parametrix）。

*证明概要*。必要性：设 $T$ Fredholm。因 $\ker T$ 有限维，存在闭补空间 $X_1$ 使 $X = \ker T \oplus X_1$。$T|_{X_1}: X_1 \to \operatorname{ran} T$ 为双射，由逆算子定理其逆有界。因 $\operatorname{coker} T = Y / \operatorname{ran} T$ 有限维，取有限维补 $Y_1$ 使 $Y = \operatorname{ran} T \oplus Y_1$。定义 $S$ 为 $(T|_{X_1})^{-1}$ 在 $\operatorname{ran} T$ 上的延拓（在 $Y_1$ 上任意定义）。则 $ST - I$ 投影到 $\ker T$，$TS - I$ 投影到 $Y_1$，二者皆有限秩（从而紧）。

充分性：设 $ST = I + K_1$，$TS = I + K_2$，$K_1, K_2$ 紧。由Fredholm择一，$I + K_1$ 有有限维核与闭值域，故 $\ker T \subseteq \ker(ST)$ 有限维。类似，$\ker T^* \subseteq \ker(TS)^*$ 有限维。$\square$

## 3. Atkinson定理

**定理 3.1**（Atkinson）。设 $X, Y, Z$ 为Banach空间，$T \in \mathcal{B}(X,Y)$，$S \in \mathcal{B}(Y,Z)$ 为Fredholm算子。则 $ST \in \mathcal{B}(X,Z)$ 也是Fredholm算子，且
$$\operatorname{ind}(ST) = \operatorname{ind}(S) + \operatorname{ind}(T).$$

*证明概要*。设 $T_1, S_1$ 分别为 $T, S$ 的参数化子。则
$$T_1 S_1 ST - I = T_1(S_1 S - I)T + (T_1 T - I),$$
为紧算子之和，故紧。类似 $ST T_1 S_1 - I$ 紧。由定理2.4，$ST$ Fredholm。

指标公式：考虑正合列
$$0 \to \ker T \to \ker(ST) \to \ker S \cap \operatorname{ran} T \to 0$$
和
$$0 \to \frac{\ker S}{\ker S \cap \operatorname{ran} T} \to \operatorname{coker} T \to \operatorname{coker}(ST) \to \operatorname{coker} S \to 0.$$
通过维数计算可得指标加性。$\square$

**推论 3.2**。若 $T$ Fredholm 且 $K$ 紧，则 $T + K$ Fredholm，且 $\operatorname{ind}(T + K) = \operatorname{ind}(T)$。

*证明*。$T + K = T(I + T^{-1}K)$（在参数化子意义下），$I + T^{-1}K$ 为指标零的Fredholm算子（因紧算子的指标扰动）。$\square$

## 4. 指标的同伦不变性

**定理 4.1**。Fredholm算子的指标在范数拓扑下局部常值：若 $T$ Fredholm，则存在 $\varepsilon > 0$ 使得当 $\|S - T\| < \varepsilon$ 时，$S$ Fredholm且 $\operatorname{ind}(S) = \operatorname{ind}(T)$。

*证明*。设 $T_1$ 为 $T$ 的参数化子，$T_1 T = I + K$。取 $\varepsilon = \|T_1\|^{-1}$。当 $\|S - T\| < \varepsilon$，
$$T_1 S = T_1 T + T_1(S - T) = I + K + T_1(S - T).$$
因 $\|T_1(S - T)\| < 1$，$I + T_1(S - T)$ 可逆。故 $T_1 S = (I + T_1(S - T)) + K$ 为可逆算子的紧扰动，从而Fredholm且指标为 $\operatorname{ind}(I + K) = 0$。由Atkinson定理，$\operatorname{ind}(S) = -\operatorname{ind}(T_1) = \operatorname{ind}(T)$。$\square$

**推论 4.2**。若 $t \mapsto T_t$ 为 $[0,1] \to \mathcal{B}(X,Y)$ 的连续路径，且每个 $T_t$ Fredholm，则 $\operatorname{ind}(T_t)$ 为常数。

## 5. 半Fredholm算子

**定义 5.1**。$T \in \mathcal{B}(X,Y)$ 称为**上半Fredholm**，若 $\ker T$ 有限维且 $\operatorname{ran} T$ 闭。**下半Fredholm**，若 $\operatorname{coker} T$ 有限维（等价于 $\operatorname{ran} T$ 闭且有余有限维闭补）。

**命题 5.2**。$T$ 上半Fredholm当且仅当 $T^*$ 下半Fredholm，此时 $\operatorname{ind}(T) = -\operatorname{ind}(T^*)$（在指标有定义时）。

## 6. 在偏微分方程中的应用

### 6.1 椭圆算子作为Fredholm算子

**例 6.1**。设 $\Omega \subseteq \mathbb{R}^n$ 为有界光滑区域，考虑椭圆型微分算子
$$Lu = -\sum_{i,j=1}^n \partial_i(a_{ij}(x) \partial_j u) + \sum_{i=1}^n b_i(x) \partial_i u + c(x)u,$$
其中 $(a_{ij})$ 一致正定。则 $L: H^2(\Omega) \cap H_0^1(\Omega) \to L^2(\Omega)$ 是Fredholm算子。

*证明概要*。由椭圆正则性，存在参数化子（拟基本解）$G: L^2(\Omega) \to H^2(\Omega) \cap H_0^1(\Omega)$ 使得 $LG - I$ 和 $GL - I$ 为光滑化算子（从而紧）。由定理2.4，$L$ Fredholm。$\square$

### 6.2 指标的计算

Atiyah-Singer指标定理给出了紧流形上椭圆伪微分算子指标的拓扑公式：
$$\operatorname{ind}(D) = \int_M \hat{A}(M) \wedge \operatorname{ch}(E),$$
其中 $\hat{A}$ 为A-类，$\operatorname{ch}$ 为陈特征。这超越了本文范围，但表明Fredholm指标的拓扑本质是深刻而丰富的。

## 7. 与项目其他部分的关联

Fredholm理论直接建立在紧算子理论（见[05-紧算子](05-紧算子.md)）之上，是泛函分析通向微分几何与拓扑的桥梁。在椭圆型偏微分方程中，Fredholm性质保证了在适当边界条件下解空间的有限维性（见[10-Sobolev空间](10-Sobolev空间.md)）。指标定理更将分析指标与拓扑指标统一，是20世纪数学的重大成就之一。在层上同调与代数几何中，Euler特征数也可视为某种"指标"（见`docs/12-代数拓扑/`和`docs/02-代数结构/范畴论/`）。

## 8. 参考文献

1. E.I. Fredholm, "Sur une classe d'équations fonctionnelles", *Acta Math.* 27 (1903), 365–390.
2. F.V. Atkinson, "The normal solvability of linear equations in normed spaces", *Mat. Sb.* 28 (1951), 3–14.
3. M.F. Atiyah & I.M. Singer, "The index of elliptic operators on compact manifolds", *Bull. AMS* 69 (1963), 422–433.
4. B. Booss & D.D. Bleecker, *Topology and Analysis: The Atiyah-Singer Index Formula and Gauge-Theoretic Physics*, Springer, 1985.
5. 齐民友、徐超江，《偏微分方程引论》，武汉大学出版社，1994。
