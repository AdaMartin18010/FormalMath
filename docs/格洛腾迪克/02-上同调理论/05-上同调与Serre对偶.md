---
title: 上同调与Serre对偶
description: 深入介绍Serre对偶定理的陈述、证明思路、推广到Grothendieck对偶，以及在射影概形上的具体计算应用。
msc_primary: 14F17
msc_secondary:
- 14F05
- 32C35
processed_at: '2026-04-16'
---

# 上同调与 Serre 对偶

## 引言

Serre 对偶是代数几何中最优美、最实用的定理之一。它将一个凝聚层的上同调群与其对偶层的上同调群联系起来，形式为：

$$H^i(X, \mathcal{F})^* \cong H^{n-i}(X, \mathcal{F}^\vee \otimes \omega_X)$$

这一定理不仅是计算上同调的有力工具，也是代数曲线 Riemann-Roch 定理证明的核心。格洛腾迪克后来将 Serre 对偶推广为**Grothendieck 对偶**，适用于更一般的固有态射，成为现代对偶理论的基石。

本教程将系统介绍 Serre 对偶定理及其推广。

---

## 一、Serre 对偶定理

### 1.1 陈述

设 $X$ 是域 $k$ 上 $n$ 维光滑射影概形（或更一般地，Cohen-Macaulay 射影概形），$\omega_X = \bigwedge^n \Omega_{X/k}^1$ 是**典则层**（canonical sheaf）。对任意局部自由层（或更一般地，凝聚层）$\mathcal{F}$，有自然同构：

$$H^i(X, \mathcal{F})^* \cong H^{n-i}(X, \mathcal{F}^\vee \otimes \omega_X)$$

其中 $V^* = \text{Hom}_k(V, k)$ 是 $k$-向量空间 $V$ 的对偶空间。

等价地，可以用 Ext 来表示：

$$\text{Ext}^i(\mathcal{F}, \omega_X) \cong H^{n-i}(X, \mathcal{F})^*$$

### 1.2 特殊情形

**曲线的情形**：设 $C$ 是光滑射影曲线，亏格为 $g$。则 $\omega_C = \Omega_{C/k}^1$ 是微分形式层，$\deg(\omega_C) = 2g-2$。Serre 对偶给出：

$$H^0(C, \mathcal{F})^* \cong H^1(C, \mathcal{F}^\vee \otimes \omega_C)$$

特别地，当 $\mathcal{F} = \mathcal{O}_C$ 时：

$$H^0(C, \omega_C) \cong H^1(C, \mathcal{O}_C)^*$$

因此 $h^0(\omega_C) = h^1(\mathcal{O}_C) = g$。

### 1.3 射影空间的情形

对 $X = \mathbb{P}^n_k$，典则层为 $\omega_X = \mathcal{O}(-n-1)$。Serre 对偶给出：

$$H^i(\mathbb{P}^n, \mathcal{O}(d))^* \cong H^{n-i}(\mathbb{P}^n, \mathcal{O}(-d-n-1))$$

这与直接计算的结果完全一致。例如：

$$H^0(\mathbb{P}^n, \mathcal{O}(d))^* \cong H^n(\mathbb{P}^n, \mathcal{O}(-d-n-1))$$

当 $d \geq 0$ 时，左边维数为 $\binom{n+d}{n}$，右边也可以通过 Bott 公式验证。

---

## 二、Serre 对偶的证明思路

### 2.1 Yoneda 配对

Serre 对偶的核心是**Yoneda 配对**（cup product）：

$$H^i(X, \mathcal{F}) \times H^{n-i}(X, \mathcal{F}^\vee \otimes \omega_X) \longrightarrow H^n(X, \omega_X)$$

关键在于：$H^n(X, \omega_X) \cong k$（对连通光滑射影 $n$ 维簇），因此上述配对给出映射：

$$H^{n-i}(X, \mathcal{F}^\vee \otimes \omega_X) \longrightarrow H^i(X, \mathcal{F})^*$$

Serre 对偶断言这一映射是同构。

### 2.2 归纳法

Serre 的原始证明使用归纳法：
1. 先对 $\mathbb{P}^n$ 证明（直接计算验证）；
2. 对一般射影簇 $X \subseteq \mathbb{P}^N$，利用闭浸入 $i: X \hookrightarrow \mathbb{P}^N$ 和正合列
   $$0 \to \mathcal{I}_X \to \mathcal{O}_{\mathbb{P}^N} \to \mathcal{O}_X \to 0$$
   通过长正合列和归纳完成证明。

### 2.3 现代观点：导出范畴

在现代观点中，Serre 对偶可以表述为：存在**迹映射**

$$\text{Tr}: H^n(X, \omega_X) \xrightarrow{\sim} k$$

使得对任意 $\mathcal{F} \in D^b_{\text{coh}}(X)$，自然映射

$$\text{RHom}(\mathcal{F}, \omega_X[n]) \longrightarrow \text{RHom}(H^*(X, \mathcal{F}), k)$$

是同构。这直接推广到 Grothendieck 对偶的框架中。

---

## 三、Grothendieck 对偶

### 3.1 相对 Serre 对偶

设 $f: X \to Y$ 是 $n$ 维光滑射影态射（即相对维数为 $n$ 的光滑固有态射）。定义**相对典则层**（或对偶层）为：

$$\omega_{X/Y} = \bigwedge^n \Omega_{X/Y}^1$$

**相对 Serre 对偶**断言：对 $Y$ 上的局部自由层（或凝聚层）$\mathcal{F}$，存在自然同构：

$$R^i f_* (\mathcal{F})^\vee \cong R^{n-i} f_* (\mathcal{F}^\vee \otimes \omega_{X/Y})$$

### 3.2 Grothendieck 对偶的一般形式

对更一般的固有态射 $f: X \to Y$（不要求光滑），Grothendieck 证明了对偶层（或对偶化复形）$\omega_{X/Y}^\bullet$ 的存在性。核心定理是：存在**右伴随**

$$f^!: D^+(Y) \longrightarrow D^+(X)$$

使得对 $\mathcal{F} \in D_{\text{qcoh}}(X)$ 和 $\mathcal{G} \in D_{\text{qcoh}}(Y)$，有：

$$\text{RHom}_Y(Rf_* \mathcal{F}, \mathcal{G}) \cong \text{RHom}_X(\mathcal{F}, f^! \mathcal{G})$$

当 $f$ 是光滑的时，$f^! \mathcal{G} \cong Lf^* \mathcal{G} \otimes \omega_{X/Y}[n]$，从而恢复相对 Serre 对偶。

### 3.3 应用

Grothendieck 对偶在以下领域有重要应用：
- **相交理论**：剩余相交公式（residue formula）；
- **形变理论**：余切复形的对偶性；
- **算术几何**：算术簇上的对偶理论；
- **导出代数几何**：导出范畴中的 Serre 函子。

---

## 四、习题

### 习题 1
利用 Serre 对偶证明：对光滑射影曲线 $C$，$h^0(K_C) = g$ 且 $h^1(K_C) = 1$。

### 习题 2
设 $X$ 是 $n$ 维光滑射影簇，$\mathcal{L}$ 是丰富线丛。证明：对充分大的 $m \gg 0$，$H^i(X, \mathcal{L}^{\otimes m}) = 0$ 对所有 $i > 0$（Serre 消失定理），并用 Serre 对偶解释 $H^i(X, \mathcal{L}^{\otimes (-m)})$ 的消失行为。

### 习题 3
设 $X$ 是 K3 曲面（即二维 Calabi-Yau 簇，$\omega_X \cong \mathcal{O}_X$）。用 Serre 对偶计算 $h^0(\mathcal{O}_X)$, $h^1(\mathcal{O}_X)$, $h^2(\mathcal{O}_X)$。

### 习题 4
设 $f: X \to Y$ 是光滑固有曲线族，亏格为 $g$。利用相对 Serre 对偶证明：$R^1 f_* \mathcal{O}_X \cong (f_* \omega_{X/Y})^\vee$。

---

## 延伸阅读

- **教材推荐**：Hartshorne, R. *Algebraic Geometry*, Chap. III.7, Springer, 1977.
- **网络资源**：Stacks Project, Tag [0A6A](https://stacks.math.columbia.edu/tag/0A6A).
- **项目内延伸阅读**：
  - [数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/21-上同调与Serre对偶](../../../../数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/21-上同调与Serre对偶.md)
  - [数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/22-上同调与Grothendieck对偶](../../../../数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/22-上同调与Grothendieck对偶.md)

---

**文档状态**：✅ 完成  
**字数**：约 2,500 字  
**最后更新**：2026-04-16
