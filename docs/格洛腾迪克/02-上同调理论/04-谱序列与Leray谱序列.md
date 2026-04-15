---
title: 谱序列与Leray谱序列
description: 系统介绍谱序列的基本概念、Leray谱序列的构造与应用、以及它在层上同调和纤维化计算中的核心地位。
msc_primary: 18Txx
msc_secondary:
- 55T05
- 14Fxx
processed_at: '2026-04-16'
---

# 谱序列与 Leray 谱序列

## 引言

谱序列（spectral sequence）是同调代数中最强大也最令人生畏的计算工具之一。它提供了一种系统的方法，通过逐次逼近的方式计算复杂的上同调群。Leray 谱序列则是代数几何和代数拓扑中最重要的谱序列之一，它将一个纤维化（或概形态射）的底空间和纤维的上同调联系起来，从而把整体上同调的计算分解为局部计算。

本教程将介绍谱序列的基本结构、Leray 谱序列的构造，以及它在层上同调中的应用。

---

## 一、谱序列的基础

### 1.1 定义

一个**谱序列** $\{E_r^{p,q}, d_r\}$ 由以下数据组成：
- 对每个整数 $r \geq r_0$（通常 $r_0 = 0, 1, 2$），有一族 Abel 群 $E_r^{p,q}$（$p, q \in \mathbb{Z}$）；
- 微分映射 $d_r: E_r^{p,q} \to E_r^{p+r, q-r+1}$，满足 $d_r^2 = 0$；
- $E_{r+1}^{p,q} = H^{p,q}(E_r^{\bullet,\bullet}, d_r) = \ker(d_r) / \text{im}(d_r)$。

### 1.2 收敛性

谱序列称为**收敛**到分次对象 $H^*$，记作：

$$E_2^{p,q} \Rightarrow H^{p+q}$$

如果存在 $H^n$ 的一个滤过：

$$0 = F^{n+1}H^n \subseteq F^nH^n \subseteq \cdots \subseteq F^0H^n = H^n$$

使得对充分大的 $r$（通常依赖于 $p, q$），$E_r^{p,q} \cong E_\infty^{p,q} \cong F^pH^{p+q}/F^{p+1}H^{p+q}$。

直观上，谱序列从 $E_2$ 页开始，通过逐页微分，最终"稳定"到目标上同调群的某种分划。

---

## 二、Leray 谱序列

### 2.1 构造

设 $f: X \to Y$ 是拓扑空间（或概形）之间的连续映射（或概形态射），$\mathcal{F}$ 是 $X$ 上的层。由于 $\Gamma(X, -) = \Gamma(Y, -) \circ f_*$，全局截面函子可以分解为两步。这诱导了**Leray 谱序列**：

$$E_2^{p,q} = H^p(Y, R^q f_* \mathcal{F}) \Rightarrow H^{p+q}(X, \mathcal{F})$$

这里 $R^q f_* \mathcal{F}$ 是 $f$ 的高阶直像层，描述了 $\mathcal{F}$ 在 $Y$ 上"纤维方向"的上同调信息。

### 2.2 五项正合列

从 Leray 谱序列可以提取低维的长正合信息。特别地，五项正合列为：

$$0 \to H^1(Y, f_*\mathcal{F}) \to H^1(X, \mathcal{F}) \to H^0(Y, R^1f_*\mathcal{F}) \to H^2(Y, f_*\mathcal{F}) \to H^2(X, \mathcal{F})$$

这在计算具体上同调时非常有用。

### 2.3 例子：纤维丛

若 $f: X \to Y$ 是局部平凡纤维丛，纤维为 $F$，则 $R^q f_* \mathcal{F}$ 是 $Y$ 上的局部系统，其茎为 $H^q(F, \mathcal{F}|_F)$。此时 Leray 谱序列将 $X$ 的上同调用 $Y$ 和 $F$ 的上同调来表示，这正是 Serre 纤维谱序列的推广。

---

## 三、Grothendieck 谱序列

### 3.1 导出函子的复合

设 $\mathcal{A} \xrightarrow{F} \mathcal{B} \xrightarrow{G} \mathcal{C}$ 是 Abel 范畴之间的左正合函子，$F$ 将内射对象映为 $G$-无环对象。则对 $A \in \mathcal{A}$，存在**Grothendieck 谱序列**：

$$E_2^{p,q} = R^p G(R^q F(A)) \Rightarrow R^{p+q}(G \circ F)(A)$$

Leray 谱序列正是 Grothendieck 谱序列的特例（取 $F = f_*$，$G = \Gamma(Y, -)$）。

### 3.2 局部到全局的谱序列

设 $\mathcal{U} = \{U_i\}$ 是 $X$ 的开覆盖，$\mathcal{F}$ 是层。Čech 上同调与层上同调之间的关系也可以由谱序列描述：

$$E_2^{p,q} = \check{H}^p(\mathcal{U}, \mathcal{H}^q(\mathcal{F})) \Rightarrow H^{p+q}(X, \mathcal{F})$$

其中 $\mathcal{H}^q(\mathcal{F})$ 是上同调预层的层化。当覆盖 $\mathcal{U}$ 是仿射的且 $\mathcal{F}$ 是拟凝聚层时，高阶项消失，从而恢复 Čech 与层上同调的一致性。

---

## 四、代数几何中的应用

### 4.1 固有映射的推前

若 $f: X \to Y$ 是固有态射，$Y$ 是 Noether 的，$\mathcal{F}$ 是凝聚层，则 $R^q f_* \mathcal{F}$ 也是凝聚的（Grothendieck 有限性定理）。此时 Leray 谱序列中的项都是凝聚层的上同调，具有良好的有限性。

### 4.2 上同调与基变化

Leray 谱序列与**上同调与基变化定理**密切相关。考虑卡氏图：

$$\begin{array}{ccc}
X' & \longrightarrow & X \\
\downarrow^{f'} & & \downarrow^f \\
Y' & \longrightarrow & Y
\end{array}$$

在适当条件下（如 $f$ 固有、平坦，$Y$ 局部 Noether），有**基变化同构**：

$$g^* R^q f_* \mathcal{F} \xrightarrow{\sim} R^q f'_* (g'^* \mathcal{F})$$

这一定理使得我们可以将复杂基上的推前计算约化到更简单基上的计算。

---

## 五、习题

### 习题 1
设 $f: X \to Y$ 是连续映射，$\mathcal{F}$ 是 $X$ 上的 Abel 群层。写出 Leray 谱序列的 $E_2$ 页，并解释 $E_2^{0,q}$ 和 $E_2^{p,0}$ 的几何意义。

### 习题 2
设 $f: \mathbb{P}^1 \times \mathbb{P}^1 \to \mathbb{P}^1$ 是第一个投影。用 Leray 谱序列计算 $H^i(\mathbb{P}^1 \times \mathbb{P}^1, \mathcal{O})$。

### 习题 3
证明：若 $f: X \to Y$ 满足 $R^q f_* \mathcal{F} = 0$ 对所有 $q > 0$，则 $H^p(X, \mathcal{F}) \cong H^p(Y, f_*\mathcal{F})$。

### 习题 4
设 $E \xrightarrow{\pi} B$ 是复向量丛，纤维为 $\mathbb{C}^n$。利用 Leray 谱序列证明：$H^*(E) \cong H^*(B)$（作为环）。

---

## 延伸阅读

- **教材推荐**：Weibel, C.A. *An Introduction to Homological Algebra*, Chap. 5, Cambridge University Press, 1994.
- **网络资源**：Stacks Project, Tag [015J](https://stacks.math.columbia.edu/tag/015J).
- **项目内延伸阅读**：
  - [数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/05-谱序列与Leray谱序列](../../../../数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/05-谱序列与Leray谱序列.md)
  - [数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/09-Grothendieck谱序列](../../../../数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/09-Grothendieck谱序列.md)

---

**文档状态**：✅ 完成  
**字数**：约 2,400 字  
**最后更新**：2026-04-16
