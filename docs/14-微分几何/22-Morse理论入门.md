---
title: Morse理论入门
description: 系统介绍Morse函数、Morse引理、胞腔分解定理与Morse不等式，以及Morse同调的基本构造，建立用临界点附近度量流形拓扑的方法。
msc_primary:
  - 53C05
msc_secondary:
  - 57R19
  - 58E05
  - 55U15
processed_at: '2026-04-20'
references:
  textbooks:
    - id: milnor_morse
      type: textbook
      title: Morse Theory
      authors:
        - John Milnor
      publisher: Princeton University Press
      year: 1963
      msc: 57R19
    - id: audin_damian
      type: textbook
      title: Morse Theory and Floer Homology
      authors:
        - Michèle Audin
        - Mihai Damian
      publisher: Springer
      year: 2014
      msc: 57R58
---

# Morse理论入门

**临界点的拓扑学 — 从Morse引理到Morse同调**

---

## 1. Morse函数的定义

### 1.1 Hessian与临界点

设 $M$ 为光滑流形，$f: M \to \mathbb{R}$ 为光滑函数。点 $p \in M$ 称为**临界点**（critical point），若 $df_p = 0$。在临界点处，定义**Hessian**为对称双线性形式
$$\text{Hess}_p(f)(X,Y) = X(Y(f))|_p = Y(X(f))|_p$$
其中 $X,Y$ 为 $p$ 附近的向量场。在局部坐标下，
$$\text{Hess}_p(f) = \left(\frac{\partial^2 f}{\partial x^i \partial x^j}(p)\right)$$

临界点 $p$ 称为**非退化**的，若 $\text{Hess}_p(f)$ 非奇异。非退化临界点的**指标**（index）定义为Hessian的负特征值个数（计重数），记为 $\text{ind}(p)$。

**定义**：光滑函数 $f: M \to \mathbb{R}$ 称为**Morse函数**，若其所有临界点均非退化。

**例1（环面 $T^2$）**：将 $T^2$ 竖直放置（如甜甜圈），高度函数 $f$ 有4个临界点：
- 底部（最小值）：指标 $0$
- 两个"鞍点"：指标 $1$
- 顶部（最大值）：指标 $2$

### 1.2 Morse引理

**定理（Morse引理）**：设 $p$ 为 $f$ 的指标 $\lambda$ 的非退化临界点。则存在局部坐标 $(x^1, \dots, x^n)$ 使得 $p$ 对应原点，且
$$f(x) = f(p) - (x^1)^2 - \dots - (x^\lambda)^2 + (x^{\lambda+1})^2 + \dots + (x^n)^2$$

*证明概要*：由Taylor定理，$f(x) = f(p) + \sum_{i,j} h_{ij}(x) x^i x^j$。通过归纳地对坐标施行线性变换完成平方，利用非退化性保证每一步的可逆性。$\square$

---

## 2. 胞腔分解与拓扑变化

### 2.1 水平集的同伦型

设 $M^a = f^{-1}((-\infty, a])$ 为**子水平集**。Morse理论的核心是描述当 $a$ 经过临界值时 $M^a$ 的同伦型变化。

**定理（胞腔粘贴）**：设 $f$ 在 $[a,b]$ 上仅有唯一的临界点 $p$，$f(p) = c \in (a,b)$，指标为 $\lambda$。则 $M^b$ 同伦等价于 $M^a$ 粘贴一个 $\lambda$-维胞腔 $e^\lambda$：
$$M^b \simeq M^a \cup_{\varphi} e^\lambda$$
其中粘贴映射 $\varphi: \partial e^\lambda \to M^a$ 由稳定流形给出。

**直观**：指标 $\lambda$ 的临界点对应" attaching a $\lambda$-handle"。指标 $0$ 添加连通分支，指标 $1$ 添加环柄，指标 $n$ 填充洞。

**例2（球面 $S^n$）**：高度函数 $f(x^0, \dots, x^n) = x^0$ 在北极（最大值，指标 $n$）和南极（最小值，指标 $0$）有临界点。$M^{-\varepsilon}$ 为一点（0-胞腔），$M^{\varepsilon}$ 同伦等价于 $D^n$（$n$-胞腔），$S^n \simeq e^0 \cup e^n$。

### 2.2 CW复形结构

**定理**：闭流形 $M$ 上任何Morse函数给出 $M$ 的CW复形结构，其中 $\lambda$-胞腔恰对应指标 $\lambda$ 的临界点。

---

## 3. Morse不等式

### 3.1 弱Morse不等式

设 $c_\lambda$ 为 $f$ 的指标 $\lambda$ 临界点个数，$b_\lambda = \dim H_\lambda(M; \mathbb{F})$ 为Betti数（$\mathbb{F}$ 为域）。

**定理（弱Morse不等式）**：$c_\lambda \geq b_\lambda$ 对所有 $\lambda$ 成立。

*证明*：由胞腔分解，链复形 $C_\lambda$ 由 $c_\lambda$ 个生成元自由生成。$H_\lambda$ 为 $C_\lambda$ 的子商，故 $\dim H_\lambda \leq \dim C_\lambda = c_\lambda$。$\square$

### 3.2 强Morse不等式

**定理（强Morse不等式）**：对任意 $k \geq 0$，
$$\sum_{\lambda=0}^k (-1)^{k-\lambda} c_\lambda \geq \sum_{\lambda=0}^k (-1)^{k-\lambda} b_\lambda$$
且取 $k = n$ 时等号成立（Euler示性数）：
$$\sum_{\lambda=0}^n (-1)^\lambda c_\lambda = \sum_{\lambda=0}^n (-1)^\lambda b_\lambda = \chi(M)$$

*证明*：由胞腔链复形 $C_*$ 的秩关系及 $\text{rank}(H_\lambda) = \text{rank}(Z_\lambda) - \text{rank}(B_\lambda)$，$\text{rank}(C_\lambda) = \text{rank}(Z_\lambda) + \text{rank}(B_{\lambda-1})$，消去边界项后得不等式。$\square$

**例3（环面 $T^2$）**：$c_0 = 1, c_1 = 2, c_2 = 1$，$\chi(T^2) = 0$。Betti数 $b_0 = 1, b_1 = 2, b_2 = 1$。弱不等式取等号，$f$ 为**完美Morse函数**。

**例4（实射影平面 $\mathbb{RP}^2$）**：$\mathbb{RP}^2$ 的标准高度函数有 $c_0 = 1, c_1 = 1, c_2 = 1$。但 $H_1(\mathbb{RP}^2; \mathbb{Z}_2) = \mathbb{Z}_2$，$H_2(\mathbb{RP}^2; \mathbb{Z}_2) = \mathbb{Z}_2$（$\mathbb{Z}_2$ 系数），而 $H_1(\mathbb{RP}^2; \mathbb{Q}) = 0$。这说明系数域的选择影响不等式的尖锐性。

---

## 4. Morse同调

### 4.1 梯度流与稳定/不稳定流形

设 $f$ 为Morse函数，$g$ 为Riemann度量。定义**负梯度流**
$$\frac{d}{dt}\gamma(t) = -\nabla f(\gamma(t))$$
对临界点 $p$，定义
- **稳定流形**：$W^s(p) = \{x \in M \mid \lim_{t \to +\infty} \phi_t(x) = p\}$
- **不稳定流形**：$W^u(p) = \{x \in M \mid \lim_{t \to -\infty} \phi_t(x) = p\}$

$W^u(p)$ 微分同胚于 $\mathbb{R}^{\text{ind}(p)}$，$W^s(p)$ 微分同胚于 $\mathbb{R}^{n - \text{ind}(p)}$。

### 4.2 Morse-Smale条件

称 $(f,g)$ 满足**Morse-Smale条件**，若对所有临界点 $p,q$，$W^u(p)$ 与 $W^s(q)$ 横截相交。此时连接 $p$ 到 $q$ 的梯度流轨迹空间
$$\mathcal{M}(p,q) = W^u(p) \cap W^s(q) / \mathbb{R}$$
（模去时间平移）为 $\text{ind}(p) - \text{ind}(q) - 1$ 维光滑流形。

### 4.3 链复形与同调

设 $\text{Crit}_\lambda(f)$ 为指标 $\lambda$ 临界点集。定义**Morse链复形**
$$CM_\lambda = \bigoplus_{p \in \text{Crit}_\lambda(f)} \mathbb{Z} \cdot p$$
边缘算子 $\partial: CM_\lambda \to CM_{\lambda-1}$ 由计数梯度流轨迹给出：
$$\partial p = \sum_{q \in \text{Crit}_{\lambda-1}(f)} n(p,q) \, q$$
其中 $n(p,q) \in \mathbb{Z}$ 为从 $p$ 到 $q$ 的定向轨迹数（模2时取 $\mathbb{Z}_2$）。

**定理**：$\partial^2 = 0$，且 $HM_*(M) \cong H_*(M; \mathbb{Z})$。

*证明概要*：$\partial^2 = 0$ 对应指标差2的临界点对的破断梯度流轨迹的紧致化边界为空（由横截性与定向相容性）。同构由将Morse临界点对应到胞腔链实现。$\square$

**例5（$S^n$ 的Morse同调）**：两个临界点 $p$（指标0）和 $q$（指标 $n$）。$CM_0 = \mathbb{Z}\langle p \rangle$，$CM_n = \mathbb{Z}\langle q \rangle$。当 $n > 1$，无指标1临界点，$\partial = 0$。$HM_0 = \mathbb{Z}$，$HM_n = \mathbb{Z}$，与奇异同调一致。

---

## 5. Lusternik-Schnirelmann理论

**定理（Lusternik-Schnirelmann）**：设 $M$ 为紧流形，$\text{cat}(M)$ 为 $M$ 的**畴数**（覆盖 $M$ 所需可缩开集的最小个数）。则 $M$ 上任何光滑函数的临界点个数至少为 $\text{cat}(M)$。

对 $T^2$，$\text{cat}(T^2) = 3$，但Morse函数要求至少 $b_0 + b_1 + b_2 = 4$ 个临界点（非退化）。若允许退化临界点，可构造只有3个临界点的函数。

---

## 6. 小结

Morse理论揭示了光滑函数的临界点与流形拓扑之间的深刻联系。Morse不等式给出了Betti数的下界估计，胞腔分解提供了计算同调的具体几何手段，Morse同调则将这一切纳入同调代数的框架，并为Floyd同调等现代理论奠定基础。从球面的高度函数到环面上的复杂梯度流，Morse理论始终是联系分析与拓扑的桥梁。
