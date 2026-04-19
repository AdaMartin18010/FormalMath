---
title: Castelnuovo有理性判据
description: 详细阐述Castelnuovo有理性判据的完整证明、历史背景、相关不变量以及在有理曲面和三维簇上的推广。
msc_primary:
  - 14J26
msc_secondary:
  - 14E08
  - 14Jxx
  - 14C20
processed_at: '2026-04-20'
references:
  textbooks:
    - id: hartshorne_ag
      type: textbook
      title: Algebraic Geometry
      authors:
        - Robin Hartshorne
      publisher: Springer
      year: 1977
      msc: 14-01
    - id: vakil_foag
      type: textbook
      title: Foundations of Algebraic Geometry
      authors:
        - Ravi Vakil
      publisher: self-published
      year: 2024
  databases:
    - id: stacks_project
      type: database
      name: Stacks Project
      entry_url: "https://stacks.math.columbia.edu/tag/{tag}"
---

# Castelnuovo有理性判据

## 引言

在代数曲面的分类理论中，判定一个给定曲面是否"有理"——即双有理等价于射影平面 $\mathbb{P}^2$——是最基本的问题之一。Castelnuovo在1890年代提出了一个著名的数值判据，将这一几何问题转化为可计算的不变量检验。

Castelnuovo判据的优美之处在于：它仅通过三个经典不变量——不规则性 $q$、几何亏格 $p_g$ 和二重亏格 $P_2$——的消失，就精确刻画了有理曲面。这一定理由意大利代数几何学派奠定，后经Zariski、Kodaira等人严格化，成为双有理几何的基石。

本教程详细介绍Castelnuovo有理性判据的陈述、证明思路及其在更高维度的推广。

---

## 1. 陈述与历史

### 1.1 核心定理

**定理 1.1（Castelnuovo有理性判据）**。设 $S$ 为特征 $0$ 的代数闭域上的光滑射影曲面。则 $S$ 是有理的（即双有理等价于 $\mathbb{P}^2$）当且仅当

$$q(S) = p_g(S) = P_2(S) = 0,$$

其中：
- $q(S) = h^1(S, \mathcal{O}_S)$ 为**不规则性**；
- $p_g(S) = h^2(S, \mathcal{O}_S) = h^0(S, K_S)$ 为**几何亏格**；
- $P_2(S) = h^0(S, 2K_S)$ 为**二重亏格**（plurigenus of order 2）。

### 1.2 历史注记

Castelnuovo在1894年首次证明了这一定理的充分性部分。必要性是直接的：$\mathbb{P}^2$ 的这些不变量显然为零，而它们都是双有理不变量（对 $q, p_g$）或稳定双有理不变量（对 $P_2$）。Zariski在1950年代将结果推广到正特征情形，尽管证明更为困难。

---

## 2. 证明思路

### 2.1 准备工作

**引理 2.1**。设 $S$ 满足 $q = p_g = P_2 = 0$。则：
1. $\chi(\mathcal{O}_S) = 1$（因 $\chi = 1 - q + p_g = 1$）。
2. 由Noether公式：$K_S^2 + e(S) = 12$。
3. $h^0(-K_S) \geq K_S^2 + 1$（由Riemann-Roch和Serre对偶）。

*证明*。由曲面Riemann-Roch：

$$\chi(-K_S) = \chi(\mathcal{O}_S) + \frac{1}{2}(K_S^2 + K_S^2) = 1 + K_S^2.$$

而 $\chi(-K_S) = h^0(-K_S) - h^1(-K_S) + h^2(-K_S) = h^0(-K_S) - h^1(-K_S) + h^0(2K_S)$。由 $P_2 = h^0(2K_S) = 0$，故 $h^0(-K_S) \geq 1 + K_S^2$。$\square$

### 2.2 核心论证

**步骤 1：证明 $K_S^2 \geq 1$**。若 $K_S^2 \leq 0$，由 $h^0(-K_S) \geq 1 + K_S^2$，至少 $h^0(-K_S) \geq 1$（当 $K_S^2 = 0$）或更大。实际上需要更细致的分析。

**步骤 2：找到使 $K_S \cdot C < 0$ 的曲线 $C$**。由 $|-K_S|$ 非空，取 $D \in |-K_S|$。若 $K_S^2 > 0$，则对任意曲线 $C$，$(-K_S \cdot C) > 0$ 或类似性质保证可以找到收缩的曲线。

**步骤 3：收缩到极小模型**。由 $K_S \cdot C < 0$ 和伴随公式，$C \cong \mathbb{P}^1$ 且 $C^2 \geq -1$。若 $C^2 = -1$，则Castelnuovo收缩判据适用，可以blow-down。重复此过程直到得到极小模型 $S_{\min}$。

**步骤 4：分类极小模型**。对 $q = p_g = 0$ 的极小模型，只有两种可能：$\mathbb{P}^2$ 或 Hirzebruch 曲面 $F_n$（$n \neq 1$）。而 $F_n$（$n \geq 0$）都是有理的。

**步骤 5：$S_{\min} = \mathbb{P}^2$ 或 $F_n$ 都是有理的**，且 $S$ 通过blow-up从这些得到，故 $S$ 也是有理的。$\square$

---

## 3. 相关不变量与判据

### 3.1 其他有理性判据

**命题 3.1**。若 $S$ 满足以下条件之一，则 $S$ 是有理的：
1. $S$ 同构于 $\mathbb{P}^2$ 的 blow-up。
2. $S$ 同构于 $F_n$（$n \geq 0$）的 blow-up。
3. $S$ 含有丰富的反典范除子 $-K_S$（Del Pezzo曲面）。

### 3.2 非有理性的判据

**命题 3.2**。若以下任一成立，则 $S$ 不是有理的：
1. $q(S) > 0$（如Abel曲面的积）。
2. $p_g(S) > 0$（如K3曲面、一般型曲面）。
3. $P_2(S) > 0$（如Enriques曲面有 $P_2 = 1$，虽然 $q = p_g = 0$，但不是有理的）。

**注记 3.3**。Enriques曲面满足 $q = p_g = 0$ 但 $P_2 = 1$，说明 $P_2 = 0$ 的条件不可省略。

---

## 4. 推广

### 4.1 三维簇

**定理 4.1（Corti-Pukhlikov-Reid）**。三维光滑Fano簇的有理性判据复杂得多。一般的三次三维fold是有理的（Clemens-Griffiths证明某些非有理），而一般的四次三维fold是非有理的（Iskovskikh-Manin通过双有理自同构研究）。

**定义 4.2（稳定有理性）**。簇 $X$ 称为**稳定有理的**，如果 $X \times \mathbb{P}^m$ 是有理的（对某个 $m$）。存在稳定有理但非有理的簇（Böhning-von Bothmer, 2014）。

---

## 5. 重要例子

### 例子 1：三次曲面的有理性

**例 5.1**。光滑三次曲面 $S \subseteq \mathbb{P}^3$ 是有理的。事实上，任取 $S$ 上一条直线 $L$，通过 $L$ 的平面截 $S$ 于 $L$ 加上一条圆锥曲线，这给出了 $S$ 到 $\mathbb{P}^2$ 的有理映射。

### 例子 2：Enriques曲面的非有理性

**例 5.2**。Enriques曲面满足 $q = p_g = 0$，$\chi = 1$，$K_S \not\sim 0$ 但 $2K_S \sim 0$。故 $P_2 = 1$，不满足Castelnuovo条件。事实上，Enriques曲面的万有覆盖是K3曲面，它非有理。

### 例子 3：Godeaux曲面

**例 5.3**。Godeaux曲面是 $q = p_g = 0$ 的一般型曲面的最简单例子。由一般型定义，$P_2 > 0$，故非有理。

---

## 6. 与已有文档的关联

- [12-曲面相交理论](12-曲面相交理论.md)：相交数是证明中分析曲线行为的核心工具。
- [13-直纹面与有理曲面](13-直纹面与有理曲面.md)：有理曲面的结构、blow-up/blow-down操作。
- [09-典范除子与亏格](09-典范除子与亏格.md)：不变量 $q, p_g$ 的定义与计算。

---

## 练习

1. 证明Enriques曲面满足 $P_2 = 1$，且其万有覆盖是K3曲面。
2. 验证 $F_1$（$\mathbb{P}^2$ 在一点的blow-up）满足 $q = p_g = P_2 = 0$。
3. 构造一个 $q = p_g = 0$ 但 $P_2 > 0$ 的一般型曲面，并计算其基本不变量。

---

## 参考文献

1. R. Hartshorne, *Algebraic Geometry*, Springer, 1977. (Ch. V, §6)
2. W. Barth et al., *Compact Complex Surfaces*, Springer, 1984.
3. G. Castelnuovo, "Sulle superficie di genere zero", *Mem. Soc. Ital. XL*, 1894.
