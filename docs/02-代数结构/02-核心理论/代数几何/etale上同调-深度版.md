---
title: "etale上同调 - 深度版"
msc_primary: "14F20"
msc_secondary: ["14F30", "14F40", "14G15", "14G20", "11G25"]
processed_at: '2026-04-05'
---

# etale上同调 - 深度版

## 目录

- [etale上同调 - 深度版](#etale上同调---深度版)
  - [目录](#目录)
  - [📚 概述](#概述)
  - [🕰️ 历史发展与Weil猜想](#历史发展与weil猜想)
    - [Weil的洞见与猜想](#weil的洞见与猜想)
    - [格洛腾迪克的革命性方法](#格洛腾迪克的革命性方法)
    - [Deligne的证明与现代发展](#deligne的证明与现代发展)
  - [🏗️ 平展拓扑与平展层](#平展拓扑与平展层)
    - [平展态射的定义与性质](#平展态射的定义与性质)
    - [Grothendieck拓扑的公理](#grothendieck拓扑的公理)
    - [平展层的范畴](#平展层的范畴)
  - [🔬 平展上同调的基本构造](#平展上同调的基本构造)
    - [截面函子与导出函子](#截面函子与导出函子)
    - [茎与严格Hensel化](#茎与严格hensel化)
    - [与经典上同调的比较](#与经典上同调的比较)
  - [📐 有限系数与l-adic上同调](#有限系数与l-adic上同调)
    - [l进完备化](#l进完备化)
    - [l-adic层的性质](#l-adic层的性质)
    - [高维Lefschetz迹公式](#高维lefschetz迹公式)
  - [🔄 格洛腾迪克纲领的核心成就](#格洛腾迪克纲领的核心成就)
    - [函数方程与Poincaré对偶](#函数方程与poincaré对偶)
    - [比较定理](#比较定理)
    - [特殊化与基变换](#特殊化与基变换)
  - [⚡ 深入应用](#深入应用)
    - [Riemann假设的类比](#riemann假设的类比)
    - [L函数与特殊值](#l函数与特殊值)
    - [算术几何中的应用](#算术几何中的应用)
  - [📊 与其他上同调理论的关系](#与其他上同调理论的关系)
    - [与晶体上同调的联系](#与晶体上同调的联系)
    - [与de Rham上同调的比较](#与de-rham上同调的比较)
    - [motivic解释](#motivic解释)
  - [📚 参考文献](#参考文献)

---

## 📚 概述

平展上同调（Étale Cohomology）是格洛腾迪克为证明Weil猜想而发明的上同调理论，是20世纪数学最伟大的成就之一。它为代数簇在任意特征下提供了类似奇异上同调的工具，成功证明了有限域上代数簇的Riemann假设类比。

本深度版将系统阐述平展拓扑的构造、平展上同调的理论基础，并深入探讨其在格洛腾迪克纲领中的核心地位——特别是与Weil猜想证明的关系。

---

## 🕰️ 历史发展与Weil猜想

### Weil的洞见与猜想

**Weil的问题**（1949）：关于有限域$\mathbb{F}_q$上代数簇的zeta函数。

**zeta函数**：
$$Z(X, t) = \exp\left(\sum_{n=1}^{\infty} \frac{\#X(\mathbb{F}_{q^n})}{n}t^n\right) = \prod_{x \in |X|} \frac{1}{1 - t^{\deg(x)}}$$

**Weil猜想**：
1. 有理性：$Z(X, t)$是$t$的有理函数
2. 函数方程：$Z(X, q^{-d}/t) = \pm q^{dE/2} t^E Z(X, t)$
3. Riemann假设：$Z(X, t) = \frac{P_1(t)P_3(t)\cdots}{P_0(t)P_2(t)\cdots}$，其中$P_i$根在$|q^{-i/2}|$
4. Betti数：$\deg P_i$等于经典Betti数

### 格洛腾迪克的革命性方法

**关键洞见**（1958-64）：
- 需要一种新的上同调理论，满足：
  - Poincaré对偶
  - Lefschetz迹公式
  - 与经典理论的比较

**平展拓扑的发明**：在概形上定义比Zariski更精细的拓扑。

**SGA 4-5**：系统阐述平展上同调理论。

### Deligne的证明与现代发展

**Deligne的突破**（1974）：
- 完成Weil猜想（特别是Riemann假设）的证明
- 使用平展上同调和Hard Lefschetz

**后续发展**：
- 混合层与权理论（Deligne）
- l-adic Fourier变换
- 置换层与几何表示论

---

## 🏗️ 平展拓扑与平展层

### 平展态射的定义与性质

**定义**：概形态射$f: X \to Y$称为**平展**，如果：
1. 平坦
2. 局部有限表现
3. 相对维数为0（几何纤维离散）

**等价条件**：局部形如$\text{Spec}(B) \to \text{Spec}(A)$，其中$B = A[t]_g/(f)$，$f'$可逆。

### Grothendieck拓扑的公理

**Grothendieck拓扑**：范畴$\mathcal{C}$上的覆盖族集合，满足：
1. **同构是覆盖**
2. **拉回稳定**：覆盖的拉回仍是覆盖
3. **复合封闭**：覆盖的覆盖是覆盖

**平展拓扑（Étale site）**：$X_{\text{\'et}}$，对象为平展$U \to X$，覆盖为满射族。

### 平展层的范畴

**定义**：平展层是平展拓扑上的集合（或Abel群、模等）层。

**与Zariski层的区别**：
- 更多开集：包括平展覆盖
- 可捕获非分歧扩张的信息

**常值层**：对于集合$\Lambda$，常值层$\underline{\Lambda}$满足$\underline{\Lambda}(U) = \Lambda^{\pi_0(U)}$。

---

## 🔬 平展上同调的基本构造

### 截面函子与导出函子

**整体截面**：$\Gamma(X, -): \text{Sh}(X_{\text{\'et}}, \Lambda) \to \Lambda\text{-mod}$

**平展上同调**：
$$H^i_{\text{\'et}}(X, \mathcal{F}) = R^i\Gamma(X, \mathcal{F})$$

### 茎与严格Hensel化

**几何点**：$\bar{x}: \text{Spec}(\Omega) \to X$，$\Omega$可分闭。

**严格Hensel化**：$\mathcal{O}_{X, \bar{x}}^{sh}$，局部环的严格Hensel化。

**茎**：$\mathcal{F}_{\bar{x}} = \varinjlim_{(U, \bar{u})} \mathcal{F}(U)$。

**定理**：层的态射是同构当且仅当在所有几何点诱导茎的同构。

### 与经典上同调的比较

**Artin的比较定理**：对于复代数簇$X$和有限系数群$\Lambda$：
$$H^i_{\text{\'et}}(X, \underline{\Lambda}) \cong H^i_{sing}(X^{an}, \Lambda)$$

**意义**：平展上同调确实推广了奇异上同调。

---

## 📐 有限系数与l-adic上同调

### l进完备化

**问题**：$\mathbb{Z}/\ell^n$系数的上同调随$n$变化。

**射影系统**：$(\mathcal{F}_n)$，$\mathcal{F}_{n+1} \to \mathcal{F}_n$。

**l-adic层**：$\mathbb{Z}_\ell$-层是$(\mathbb{Z}/\ell^n)$-层的射影系统，满足适当光滑条件。

### l-adic层的性质

**$\mathbb{Q}_\ell$-层**：$\mathbb{Z}_\ell$-层的局部化。

**重要性质**：
- 对于光滑射影簇，维数与经典Betti上同调相同
- Poincaré对偶成立
- Künneth公式成立

### 高维Lefschetz迹公式

**Grothendieck迹公式**：
$$\sum_{x \in X(\mathbb{F}_{q^n})} \text{Tr}(F_x^* | \mathcal{F}_{\bar{x}}) = \sum_i (-1)^i \text{Tr}(F^* | H^i_c(X, \mathcal{F}))$$

**应用于常值层**：得到Weil的迹公式，证明zeta函数的有理性。

---

## 🔄 格洛腾迪克纲领的核心成就

### 函数方程与Poincaré对偶

**Poincaré对偶**：对于光滑射影$X/\mathbb{F}_q$，维度$d$：
$$H^i_{\text{\'et}}(X, \mathbb{Q}_\ell) \times H^{2d-i}_{\text{\'et}}(X, \mathbb{Q}_\ell(d)) \to \mathbb{Q}_\ell$$

完美配对。

**函数方程**：由Poincaré对偶和Hard Lefschetz推出。

### 比较定理

**Artin**：与奇异上同调比较。

**Bergeron**：与de Rham上同调比较（特征0）。

**M. Artin & Mazur**：与晶体上同调比较（特征p）。

### 特殊化与基变换

**光滑基变换**：在一定条件下，上同调与基变换交换。

**特殊化**：从一般纤维到特殊纤维的约化。

---

## ⚡ 深入应用

### Riemann假设的类比

**Deligne定理**：$P_i(t)$的根$\alpha$满足$|\alpha| = q^{i/2}$。

**证明概要**：
1. 迹公式给出特征多项式
2. Poincaré对偶给出根的分布
3. 最难部分：证明$|\alpha| = q^{i/2}$

**关键引理**：Hard Lefschetz + 正定性论证。

### L函数与特殊值

**Hasse-Weil L函数**：
$$L(X, s) = \prod_{v} \frac{1}{P_v(N(v)^{-s})}$$

**Beilinson猜想**：特殊值与motivic上同调的关系。

### 算术几何中的应用

**类域论**：高维类域论的基础。

**椭圆曲线**：BSD猜想、模性提升。

**Langlands纲领**：几何Langlands对应。

---

## 📊 与其他上同调理论的关系

### 与晶体上同调的联系

**比较同构**：
$$H^i_{\text{\'et}}(X, \mathbb{Q}_p) \otimes_{\mathbb{Q}_p} B_{\text{crys}} \cong H^i_{\text{crys}}(X) \otimes_{W(k)} B_{\text{crys}}$$

**p进Hodge理论**：联系三种上同调（Betti、de Rham、平展）。

### 与de Rham上同调的比较

**特征0**：$H^i_{\text{\'et}}(X, \mathbb{Q}_\ell) \cong H^i_{dR}(X) \otimes \mathbb{Q}_\ell$。

**特征p**：需要额外的结构（晶体上同调）。

### motivic解释

**共同源头**：所有上同调理论都是某种motive的"实现"。

**周期**：不同上同调之间的比较同构给出周期。

---

## 📚 参考文献

1. **Deligne** - "La Conjecture de Weil I, II" (1974, 1980)
2. **Milne** - "Étale Cohomology" (Princeton, 1980)
3. **Freitag & Kiehl** - "Étale Cohomology and the Weil Conjecture" (Springer, 1988)
4. **Tamme** - "Introduction to Étale Cohomology" (Springer, 1994)
5. **SGA 4-5** - "Théorie des topos et cohomologie étale des schémas" (Springer LNM)

---

**相关概念**：
- [概形理论-深度版](概形理论-深度版.md)
- [晶体上同调-深度版](晶体上同调-深度版.md)
- [p进Hodge理论-深度版](p进Hodge理论-深度版.md)

**格洛腾迪克关联**：
- [motive理论-深度版](motive理论-深度版.md)
- [层论基础-深度版](层论基础-深度版.md)
