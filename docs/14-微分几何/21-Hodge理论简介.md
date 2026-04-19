---
title: Hodge理论简介
description: 系统介绍Riemann流形上的Hodge星算子、Laplace-de Rham算子、Hodge分解定理与Hodge同构，以及Kähler流形上的Hodge分解，建立调和形式与上同调的联系。
msc_primary:
  - 53C05
msc_secondary:
  - 58A14
  - 32Q15
  - 55N20
processed_at: '2026-04-20'
references:
  textbooks:
    - id: warner_foundation
      type: textbook
      title: Foundations of Differentiable Manifolds and Lie Groups
      authors:
        - Frank W. Warner
      publisher: Springer
      year: 1983
      msc: 58-01
    - id: wells_dca
      type: textbook
      title: Differential Analysis on Complex Manifolds
      authors:
        - Raymond O. Wells Jr.
      publisher: Springer
      year: 1980
      msc: 32-02
---

# Hodge理论简介

**调和形式与上同调 — 从Laplace算子到Hodge分解**

---

## 1. Hodge星算子

### 1.1 定义与基本性质

设 $(M^n, g)$ 为定向Riemann流形，$\text{vol}_g$ 为体积形式。对 $k$-形式 $\alpha, \beta \in \Omega^k(M)$，定义**点内积**
$$\langle \alpha, \beta \rangle = \frac{1}{k!} g^{i_1j_1} \cdots g^{i_kj_k} \alpha_{i_1\dots i_k} \beta_{j_1\dots j_k}$$

**Hodge星算子** $*: \Omega^k(M) \to \Omega^{n-k}(M)$ 由以下等价条件刻画：
$$\alpha \wedge *\beta = \langle \alpha, \beta \rangle \, \text{vol}_g, \quad \forall \alpha, \beta \in \Omega^k(M)$$

局部地，若 $\{e^i\}$ 为定向正交余标架，则
$$*(e^{i_1} \wedge \dots \wedge e^{i_k}) = \varepsilon_{i_1\dots i_k j_1\dots j_{n-k}} e^{j_1} \wedge \dots \wedge e^{j_{n-k}}$$

**性质**：
- $*^2 = (-1)^{k(n-k)}$ 在 $\Omega^k(M)$ 上
- 对偶形式：$\alpha \wedge *\alpha = |\alpha|^2 \text{vol}_g$

**例1（三维空间）**：在 $\mathbb{R}^3$ 配备标准度量，设 $\alpha = A_i dx^i$ 为1-形式，则
$$*\alpha = A_1 dx^2 \wedge dx^3 + A_2 dx^3 \wedge dx^1 + A_3 dx^1 \wedge dx^2$$
$*$ 将1-形式对应到2-形式，恰为向量分析中 $\mathbf{A} \mapsto *\mathbf{A}$ 的推广。

---

## 2. 余微分与Laplace-de Rham算子

### 2.1 余微分

外微分 $d: \Omega^k(M) \to \Omega^{k+1}(M)$ 的**形式伴随**定义为
$$\delta = (-1)^{n(k+1)+1} * d *: \Omega^k(M) \to \Omega^{k-1}(M)$$
在紧支集形式空间上，$\delta$ 满足
$$(d\alpha, \beta)_{L^2} = (\alpha, \delta\beta)_{L^2}$$
其中 $(\alpha, \beta)_{L^2} = \int_M \langle \alpha, \beta \rangle \, \text{vol}_g$。

对定向紧Riemann流形，$\delta$ 也可写为 $\delta = -*d*$（当度数为 $k$ 且 $n$ 为奇数或特定情形下）。

### 2.2 Laplace-de Rham算子

**Laplace-de Rham算子**（或Hodge Laplacian）定义为
$$\Delta = d\delta + \delta d: \Omega^k(M) \to \Omega^k(M)$$

**性质**：
- $\Delta$ 为二阶椭圆自伴算子；
- $(\Delta \alpha, \alpha) = \|d\alpha\|^2 + \|\delta\alpha\|^2 \geq 0$；
- $\Delta \alpha = 0 \iff d\alpha = 0$ 且 $\delta\alpha = 0$。

满足 $\Delta \alpha = 0$ 的形式称为**调和形式**（harmonic form），记空间为 $\mathcal{H}^k(M)$。

**例2（函数上的Laplace算子）**：对 $k=0$，$\delta = 0$（因无 $-1$-形式），故
$$\Delta f = \delta df = -*d*df$$
在 $\mathbb{R}^n$ 上，$\Delta f = -\sum_i \frac{\partial^2 f}{\partial (x^i)^2}$，与通常 Laplacian 差一个符号（几何 Laplacian 为正算子）。

---

## 3. Hodge分解定理

### 3.1 定理陈述

**定理（Hodge分解）**：设 $(M, g)$ 为闭（紧无边界）定向Riemann流形。则对任意 $k$，有 $L^2$-正交分解：
$$\Omega^k(M) = \mathcal{H}^k(M) \oplus d\Omega^{k-1}(M) \oplus \delta\Omega^{k+1}(M)$$
即任意 $k$-形式 $\omega$ 可唯一写为
$$\omega = h + d\alpha + \delta\beta$$
其中 $h \in \mathcal{H}^k(M)$，$\alpha \in \Omega^{k-1}(M)$，$\beta \in \Omega^{k+1}(M)$。

*证明概要*：由椭圆正则性，$\Delta$ 的 Green 算子 $G$ 紧自伴。令 $H$ 为到 $\ker\Delta = \mathcal{H}^k(M)$ 的 $L^2$-投影，则
$$\omega = H\omega + \Delta G\omega = H\omega + d(\delta G\omega) + \delta(dG\omega)$$
正交性由 $d$ 与 $\delta$ 的形式伴随关系保证。$\square$

### 3.2 Hodge同构

**推论（Hodge同构）**：$\mathcal{H}^k(M) \cong H^k_{dR}(M; \mathbb{R})$。

*证明*：考虑映射 $\Phi: \mathcal{H}^k(M) \to H^k_{dR}(M)$，$h \mapsto [h]$。
- **单射**：若 $h = d\eta$，则 $\|h\|^2 = (h, d\eta) = (\delta h, \eta) = 0$，故 $h = 0$。
- **满射**：对闭形式 $\omega$（$d\omega = 0$），由Hodge分解 $\omega = h + d\alpha + \delta\beta$。取 $d$ 得 $0 = d\delta\beta$，故 $\|\delta\beta\|^2 = (\beta, d\delta\beta) = 0$，即 $\delta\beta = 0$。因此 $\omega = h + d\alpha$，$[\omega] = [h]$。$\square$

**例3（环面 $T^2$）**：$T^2 = \mathbb{R}^2 / \mathbb{Z}^2$ 配备平坦度量。调和1-形式恰为常系数形式 $a dx + b dy$（$a,b \in \mathbb{R}$），故 $\mathcal{H}^1(T^2) \cong \mathbb{R}^2 \cong H^1_{dR}(T^2)$。

---

## 4. Poincaré对偶的Hodge实现

### 4.1 Hodge星与对偶

**定理**：$*: \mathcal{H}^k(M) \to \mathcal{H}^{n-k}(M)$ 为同构。

*证明*：$\Delta * = * \Delta$（由 $d$ 与 $\delta$ 的 $*$-共轭关系），故 $*$ 保持调和性。$\square$

这给出Poincaré对偶 $H^k_{dR}(M) \cong H^{n-k}_{dR}(M)$ 的显式 representatives。

### 4.2 相交配对

对 $[\alpha] \in H^k_{dR}(M)$，$[\beta] \in H^{n-k}_{dR}(M)$，配对
$$\langle [\alpha], [\beta] \rangle = \int_M \alpha \wedge \beta$$
由Hodge理论，取调和代表 $h_\alpha, h_\beta$，则
$$\int_M h_\alpha \wedge h_\beta = (h_\alpha, *h_\beta)_{L^2}$$
非退化性由 $*$ 的同构性保证。

---

## 5. Kähler流形上的Hodge分解

### 5.1 Kähler流形的基本设定

设 $(M^{2n}, J, g)$ 为**Kähler流形**，即 $J$ 为可积复结构，$g$ 为Hermite度量，且Kähler形式 $\omega(X,Y) = g(JX,Y)$ 为闭形式（$d\omega = 0$）。

### 5.2 算子代数

定义
- **L算子**：$L: \Omega^{p,q}(M) \to \Omega^{p+1,q+1}(M)$，$L(\alpha) = \omega \wedge \alpha$
- **Λ算子**：$\Lambda = L^*$（关于 $L^2$ 内积的形式伴随）
- **复Laplace算子**：$\Delta_\partial = \partial\partial^* + \partial^*\partial$，$\Delta_{\bar{\partial}} = \bar{\partial}\bar{\partial}^* + \bar{\partial}^*\bar{\partial}$

**定理（Kähler恒等式）**：
$$[\Lambda, \bar{\partial}] = -i\partial^*, \quad [\Lambda, \partial] = i\bar{\partial}^*$$

**推论**：在Kähler流形上，
$$\Delta = 2\Delta_\partial = 2\Delta_{\bar{\partial}}$$
故 $\Delta$ 保持 $(p,q)$-分次：$\Delta(\Omega^{p,q}) \subset \Omega^{p,q}$。

### 5.3 Hodge分解

**定理（Hodge $(p,q)$-分解）**：对紧Kähler流形 $M$，
$$\mathcal{H}^k(M) \otimes \mathbb{C} = \bigoplus_{p+q=k} \mathcal{H}^{p,q}(M)$$
其中 $\mathcal{H}^{p,q}(M) = \{\alpha \in \Omega^{p,q}(M) \mid \Delta\alpha = 0\}$。

这诱导上同调的**Hodge分解**：
$$H^k(M; \mathbb{C}) = \bigoplus_{p+q=k} H^{p,q}(M)$$
满足**Hodge对称性** $H^{p,q}(M) = \overline{H^{q,p}(M)}$。

**例4（复射影空间）**：$\mathbb{CP}^n$ 的Hodge数为
$$h^{p,q} = \dim H^{p,q}(\mathbb{CP}^n) = \begin{cases} 1 & p = q \\ 0 & p \neq q \end{cases}$$
$H^{2k}(\mathbb{CP}^n; \mathbb{C}) = H^{k,k}(\mathbb{CP}^n)$ 由 $\omega^k$ 生成。

---

## 6. 应用：Bochner技巧

**定理（Bochner）**：设 $M$ 为闭定向Riemann流形，$\text{Ric} \geq 0$。则任何调和1-形式 $\eta$ 满足 $\nabla \eta = 0$（平行）。若 $\text{Ric} > 0$ 在某点成立，则 $H^1_{dR}(M) = 0$。

*证明概要*：对1-形式，Weitzenböck公式给出
$$\Delta \eta = \nabla^*\nabla \eta + \text{Ric}(\eta^\sharp)^\flat$$
两边与 $\eta$ 内积并积分：
$$0 = \|\nabla\eta\|^2 + \int_M \text{Ric}(\eta^\sharp, \eta^\sharp) \, \text{vol}$$
若 $\text{Ric} \geq 0$，则 $\|\nabla\eta\| = 0$。若 $\text{Ric} > 0$ 在某点，则 $\eta = 0$。$\square$

**例5（球面 $S^n$）**：$S^n$（$n \geq 2$）具有正Ricci曲率的标准度量，故 $H^1_{dR}(S^n) = 0$，与已知一致。

---

## 7. 小结

Hodge理论通过椭圆分析在微分形式与de Rham上同调之间架起桥梁。调和形式作为几何上"最优"的上同调代表，使Poincaré对偶获得显式实现。在Kähler几何中，Hodge分解将拓扑、复结构与度量和谐统一，是复代数几何与算术几何的基石。Bochner技巧则展示了曲率如何约束调和形式的存在性，是几何分析的经典范例。
