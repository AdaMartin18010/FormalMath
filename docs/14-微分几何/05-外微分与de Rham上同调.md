---
title: 外微分与de Rham上同调
description: 介绍外微分运算、Poincaré引理、de Rham定理的陈述与证明思路，建立微分形式同调理论与拓扑上同调的联系。
msc_primary:
  - 58A12
msc_secondary:
  - 55N05
  - 53Cxx
processed_at: '2026-04-20'
references:
  textbooks:
    - id: lee_sm
      type: textbook
      title: Introduction to Smooth Manifolds
      authors:
        - John M. Lee
      publisher: Springer
      year: 2013
      msc: 53-01
    - id: bott_tu
      type: textbook
      title: Differential Forms in Algebraic Topology
      authors:
        - Raoul Bott
        - Loring W. Tu
      publisher: Springer
      year: 1982
      msc: 55-01
  databases:
    - id: nlab
      type: database
      name: nLab
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
---

# 外微分与de Rham上同调

## 引言

外微分（exterior derivative）是微分形式上的一阶微分算子，它将 $k$-形式映为 $(k+1)$-形式，且满足 $d^2 = 0$。这一性质使得微分形式构成上链复形，其同调群——de Rham上同调——是流形的拓扑不变量。

de Rham定理建立了de Rham上同调与奇异上同调（从而与拓扑）的等价性，这是分析学与拓扑学之间最深刻、最优美的联系之一。它不仅提供了计算拓扑不变量的解析工具，也揭示了几何对象（微分形式）与拓扑对象（上同调类）之间的深层对应。

本教程介绍外微分、Poincaré引理、de Rham上同调的定义以及de Rham定理。

---

## 1. 外微分

### 1.1 定义

**定义 1.1**。设 $\omega$ 为 $k$-形式。**外微分** $d\omega$ 是唯一的 $(k+1)$-形式，满足：
1. $d(f) = df$ 对0-形式（普通微分）；
2. $d(\omega \wedge \eta) = d\omega \wedge \eta + (-1)^k \omega \wedge d\eta$（分次Leibniz法则）；
3. $d(d\omega) = 0$（即 $d^2 = 0$）。

局部上，若 $\omega = \sum \omega_I dx^I$，则

$$d\omega = \sum_I d\omega_I \wedge dx^I = \sum_{I,j} \frac{\partial \omega_I}{\partial x^j} dx^j \wedge dx^I.$$

### 1.2 基本性质

**命题 1.2**。$d^2 = 0$。

*证明*。由定义直接：$d(df) = d(\sum \partial f/\partial x^i dx^i) = \sum_{i,j} \partial^2 f/\partial x^j \partial x^i dx^j \wedge dx^i = 0$（由对称性与反对称性抵消）。$\square$

**命题 1.3**。$F^*(d\omega) = d(F^*\omega)$（外微分与 pullback 交换）。

---

## 2. de Rham上同调

### 2.1 定义

**定义 2.1**。因 $d^2 = 0$，$\Omega^k(M) \xrightarrow{d} \Omega^{k+1}(M)$ 构成上链复形。**de Rham上同调群**

$$H^k_{\mathrm{dR}}(M) := \frac{\ker(d: \Omega^k \to \Omega^{k+1})}{\operatorname{im}(d: \Omega^{k-1} \to \Omega^k)}.$$

- **闭形式**（closed）：$d\omega = 0$。
- **恰当形式**（exact）：$\omega = d\eta$ 对某 $\eta$。

### 2.2 Poincaré引理

**定理 2.2（Poincaré引理）**。若 $U \subseteq \mathbb{R}^n$ 是星形的（star-shaped），则 $H^k_{\mathrm{dR}}(U) = 0$ 对 $k > 0$。即星形区域上每个闭形式都是恰当的。

*证明*。构造同伦算子 $K: \Omega^k(U) \to \Omega^{k-1}(U)$ 使得 $dK + Kd = \operatorname{id}$（在 $k > 0$ 时）。由星形性，可沿径向积分定义 $K$。$\square$

---

## 3. de Rham定理

### 3.1 陈述

**定理 3.1（de Rham）**。对光滑流形 $M$，

$$H^k_{\mathrm{dR}}(M) \cong H^k_{\mathrm{sing}}(M; \mathbb{R}),$$

其中右侧为实系数的奇异上同调。

### 3.2 证明思路

*证明概要*。
1. 定义积分映射 $I: H^k_{\mathrm{dR}}(M) \to H^k_{\mathrm{sing}}(M; \mathbb{R})$，$[\omega] \mapsto [\sigma \mapsto \int_\sigma \omega]$。
2. 证明 $I$ 良定义且自然（Stokes定理保证恰当形式在闭链上积分为零）。
3. 用Mayer-Vietoris序列和五角引理对开覆盖归纳，将问题局部化到 $\mathbb{R}^n$。
4. 在 $\mathbb{R}^n$ 上，由Poincaré引理和奇异上同调的计算，$I$ 是同构。$\square$

---

## 4. 重要例子

### 例子 1：圆周的de Rham上同调

**例 4.1**。$H^0_{\mathrm{dR}}(S^1) = \mathbb{R}$（常值函数）。$H^1_{\mathrm{dR}}(S^1) = \mathbb{R}$，由 $d\theta$ 生成（$d\theta$ 闭但不恰当，因 $\theta$ 不是全局定义函数）。

### 例子 2：球面

**例 4.2**。$H^k_{\mathrm{dR}}(S^n) = \begin{cases} \mathbb{R} & k = 0, n \\ 0 & \text{否则} \end{cases}$。

### 例子 3：环面

**例 4.3**。$H^k_{\mathrm{dR}}(T^n) = \Lambda^k \mathbb{R}^n$，维数 $\binom{n}{k}$。基由 $dx^{i_1} \wedge \dots \wedge dx^{i_k}$ 给出。

---

## 5. 与已有文档的关联

- [04-微分形式基础](04-微分形式基础.md)：外微分是微分形式上的核心运算。
- [01-微分流形定义](01-微分流形定义.md)：de Rham上同调是流形的拓扑不变量。
- [08-曲率张量](08-曲率张量.md)：曲率形式是闭形式，其de Rham类是示性类的基础。

---

## 练习

1. 证明 $S^2$ 上的面积形式 $dA$ 是闭的，并证明其de Rham类非零。
2. 验证Poincaré引理对 $\omega = y dx + x dy$ 在 $\mathbb{R}^2$ 上的应用。
3. 计算 $H^k_{\mathrm{dR}}(\mathbb{R}P^n)$（提示：考虑定向覆盖 $S^n \to \mathbb{R}P^n$）。

---

## 参考文献

1. J. M. Lee, *Introduction to Smooth Manifolds*, Springer, 2013. (Ch. 14-18)
2. R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, Springer, 1982.
3. G. de Rham, *Variétés Différentiables*, Hermann, 1955.
