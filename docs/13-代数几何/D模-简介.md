---
title: D模简介
description: 系统介绍微分算子层、D模的定义、导出范畴中的D模、Riemann-Hilbert对应及其在代数几何与表示论中的应用。
msc_primary: 14F10
msc_secondary:
- 32C38
- 35A27
processed_at: '2026-04-16'
---

# D 模简介

## 引言

D 模（D-module）理论是代数几何、微分方程和表示论的交汇点。它将线性偏微分方程的研究转化为层论和导出范畴的语言，使得现代代数几何的工具可以系统应用于微分方程理论。Bernstein、Kashiwara、Sato 等人在 1970–1980 年代奠定了 D 模理论的基础，而格洛腾迪克的六函子理论和导出范畴框架为 D 模提供了完美的舞台。

本教程将系统介绍 D 模的基本概念、Riemann-Hilbert 对应以及其在代数几何中的应用。

---

## 一、微分算子层 $\mathcal{D}_X$

### 1.1 定义

设 $X$ 是光滑复代数簇（或复流形）。$X$ 上的**微分算子层**$\mathcal{D}_X$ 是一个拟凝聚 $\mathcal{O}_X$-代数层，局部上由 $\mathcal{O}_X$ 和切向量场生成，满足关系：

- $[f, g] = 0$（$f, g \in \mathcal{O}_X$）
- $[\xi, f] = \xi(f)$（$\xi$ 是向量场）
- $[\xi, \eta] = [\xi, \eta]_{\text{Lie}}$（Lie 括号）

在局部坐标 $(x_1, \ldots, x_n)$ 下：

$$\mathcal{D}_X = \mathcal{O}_X\left[\frac{\partial}{\partial x_1}, \ldots, \frac{\partial}{\partial x_n}\right]$$

即由全纯函数和对各坐标的偏导数生成的非交换代数层。

### 1.2 滤过与特征簇

$\mathcal{D}_X$ 带有自然的**滤过**（order filtration）：

$$F_0 \mathcal{D}_X = \mathcal{O}_X \subseteq F_1 \mathcal{D}_X \subseteq F_2 \mathcal{D}_X \subseteq \cdots$$

其中 $F_k \mathcal{D}_X$ 由阶数 $\leq k$ 的微分算子组成。相应的分次代数为：

$$\text{gr}^F \mathcal{D}_X \cong \text{Sym}(T_X) \cong \mathcal{O}_{T^*X}$$

即余切丛 $T^*X$ 上的函数层。对相干 $\mathcal{D}_X$-模 $M$，可以定义其**特征簇**（characteristic variety）：

$$\text{Char}(M) = \text{Supp}(\text{gr}^F M) \subseteq T^*X$$

这是 $T^*X$ 中的锥形闭子簇，其维数至少为 $n = \dim X$。若 $\dim \text{Char}(M) = n$，则称 $M$ 是**全纯的**（holonomic）。

---

## 二、D 模的定义与基本性质

### 2.1 左 D 模与右 D 模

$X$ 上的**左 D 模**是拟凝聚 $\mathcal{O}_X$-模 $M$ 配以左 $\mathcal{D}_X$-模结构。类似可定义**右 D 模**。通过典则同构

$$\omega_X \otimes_{\mathcal{O}_X} M \cong M^r$$

可以在左 D 模和右 D 模之间转换（$\omega_X = \Omega_X^n$ 是最高次微分形式层）。

### 2.2 相干 D 模

$\mathcal{D}_X$-模 $M$ 称为**相干的**（coherent），如果它局部上可以由有限生成元生成，且关系模也是有限型的。相干 D 模范畴记为 $\mathbf{Coh}(\mathcal{D}_X)$，它是一个 Abel 范畴。

### 2.3 全纯 D 模

**全纯 D 模**是最重要的子类。它们的特征簇是 Lagrangian 的（即维数最小化），对应于微分方程理论中的"正则奇点"系统。全纯 D 模构成一个 Abel 子范畴，且在 D 模的六函子操作中封闭。

---

## 三、导出范畴中的 D 模

### 3.1 导出范畴

$\mathcal{D}_X$-模的导出范畴记为 $D^b(\mathcal{D}_X)$，其中的对象是有界复形的 $\mathcal{D}_X$-模。相干 D 模的导出范畴记为 $D^b_{\text{coh}}(\mathcal{D}_X)$。

### 3.2 推前与拉回

设 $f: X \to Y$ 是光滑态射。可以定义 D 模的**推前**和**拉回**：
- **推前**：$f_+ M = Rf_*(\mathcal{D}_{Y \leftarrow X} \otimes_{\mathcal{D}_X}^L M)$
- **拉回**：$f^! N = \mathcal{D}_{X \to Y} \otimes_{f^{-1}\mathcal{D}_Y}^L f^{-1}N$

这构成了 D 模的六函子形式体系，与层上同调的六函子完全平行。

### 3.3 对偶

D 模理论中有自然的**对偶函子** $\mathbb{D}$，类似于 Verdier 对偶。对相干 D 模 $M$：

$$\mathbb{D}(M) = \text{RHom}_{\mathcal{D}_X}(M, \mathcal{D}_X) \otimes_{\mathcal{O}_X} \omega_X^{-1}[n]$$

其中 $n = \dim X$。对全纯 D 模，$\mathbb{D}(M)$ 仍是全纯的，且 $\mathbb{D}^2 \cong \text{id}$。

---

## 四、Riemann-Hilbert 对应

### 4.1 问题的陈述

经典的 Riemann-Hilbert 问题问：微分方程的解空间与拓扑单值群之间有什么关系？在 D 模理论的框架下，这被提升为一个范畴等价：

**正则全纯 D 模** $\longleftrightarrow$ **Perverse 层**

### 4.2 de Rham 函子

**de Rham 函子** $DR$ 将 D 模映为复形层：

$$DR(M) = \Omega_X^\bullet \otimes_{\mathcal{O}_X} M$$

其中微分由联络给出。对全纯 D 模，$DR(M)$ 是一个 constructible 复形层。

### 4.3 Riemann-Hilbert 对应

**定理**（Kashiwara, Mebkhout）： de Rham 函子给出范畴等价：

$$DR: D^b_{\text{rh}}(\mathcal{D}_X) \xrightarrow{\sim} D^b_c(X^{\text{an}}, \mathbb{C})$$

左边是**正则全纯 D 模**的有界导出范畴，右边是**可构造复形层**的导出范畴。进一步地，这一等价限制为：

$$DR: \{\text{全纯 D 模}\} \xrightarrow{\sim} \{\text{Perverse 层}\}$$

其中 Perverse 层是可构造复形层的一个特殊子范畴，由中间 perversity 条件定义。

### 4.4 几何意义

Riemann-Hilbert 对应揭示了微分方程与拓扑之间的深刻对偶：
- D 模描述的是"微分"结构；
- Perverse 层描述的是"拓扑"结构；
- de Rham 函子建立了两者之间的桥梁。

这一定理在 Hodge 理论、表示论和镜对称中都有重要应用。

---

## 五、应用

### 5.1 表示论中的 D 模

Beilinson-Bernstein 对应将 Lie 代数表示与旗簇上的 D 模联系起来：

$$\mathbf{Mod}(\mathfrak{g}, \chi) \cong \mathbf{Coh}(\mathcal{D}_{G/B})$$

这是表示论中最深刻的几何化结果之一，将无穷维表示论转化为有限维代数几何问题。

### 5.2 相交上同调

对奇异代数簇 $X$，其**相交上同调** $IH^*(X)$ 可以用 Perverse 层（从而用 D 模）来定义和计算。这为奇异簇的 Hodge 理论和 Poincaré 对偶提供了自然的框架。

---

## 六、习题

### 习题 1
证明：对光滑簇 $X$，$\mathcal{D}_X$ 作为左 $\mathcal{D}_X$-模是相干的。

### 习题 2
设 $M$ 是全纯 D 模。解释为什么其特征簇 $\text{Char}(M)$ 是 $T^*X$ 中的 Lagrangian 子簇。

### 习题 3
描述 de Rham 函子 $DR$ 在局部坐标下的显式形式。

### 习题 4
解释 Beilinson-Bernstein 对应如何将 Verma 模与旗簇上的某些 D 模联系起来。

---

## 延伸阅读

- **教材推荐**：Hotta, R., Takeuchi, K., & Tanisaki, T. *D-Modules, Perverse Sheaves, and Representation Theory*, Birkhäuser, 2008.
- **网络资源**：nLab, "D-module".
- **项目内延伸阅读**：
  - [数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/06-其他数学贡献/09-六函子理论](../../../../数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/06-其他数学贡献/09-六函子理论.md)

---

**文档状态**：✅ 完成  
**字数**：约 2,700 字  
**最后更新**：2026-04-16
