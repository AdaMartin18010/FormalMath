---
title: 上同调与Grothendieck对偶
description: 介绍Grothendieck对偶理论的一般框架、对偶化复形、残余复形以及在固有态射上的应用，是现代对偶理论的系统总结。
msc_primary: 14F17
msc_secondary:
- 14B15
- 13D45
processed_at: '2026-04-16'
---

# 上同调与 Grothendieck 对偶

## 引言

Serre 对偶是光滑射影簇上凝聚层上同调的一个优美定理，但它依赖于光滑性条件。格洛腾迪克在1960年代致力于将对偶理论推广到更一般的固有态射，最终发展为**Grothendieck 对偶**。这一理论不仅统一了 Serre 对偶、Poincaré 对偶和局部对偶，还引入了**对偶化复形**和**残余复形**等深刻概念，成为现代代数几何、算术几何和导出范畴理论的基石。

本教程将介绍 Grothendieck 对偶的核心思想和主要结果。

---

## 一、Grothendieck 对偶的框架

### 1.1 问题的提出

设 $f: X \to Y$ 是固有态射，$\mathcal{F}$ 是 $X$ 上的凝聚层。我们希望找到 $Y$ 上的一个对象（复形），使得 $Rf_* \mathcal{F}$ 与其 Hom 给出 $X$ 上的对偶信息。Serre 对偶对应于 $Y = \text{Spec}(k)$ 且 $f$ 光滑的特殊情形。

### 1.2 右伴随 $f^!$

**Grothendieck 对偶定理**：设 $f: X \to Y$ 是有限型分离态射，且 $Y$ 是拟紧拟分离的。则导出推前函子

$$Rf_*: D_{\text{qcoh}}(X) \longrightarrow D_{\text{qcoh}}(Y)$$

有一个右伴随

$$f^!: D_{\text{qcoh}}^+(Y) \longrightarrow D_{\text{qcoh}}^+(X)$$

即对 $\mathcal{F} \in D_{\text{qcoh}}(X)$ 和 $\mathcal{G} \in D_{\text{qcoh}}^+(Y)$，存在自然同构：

$$\text{RHom}_Y(Rf_* \mathcal{F}, \mathcal{G}) \cong \text{RHom}_X(\mathcal{F}, f^! \mathcal{G})$$

### 1.3 对偶化复形

若 $Y = \text{Spec}(k)$，则 $\mathcal{G} = k$（视为复形），此时 $f^! k$ 称为 $X$ 的**对偶化复形**，记为 $\omega_X^\bullet$。对光滑 $n$ 维簇，$\omega_X^\bullet \cong \omega_X[n]$，恢复 Serre 对偶。

对一般情形，$\omega_X^\bullet$ 是一个复形，其第 $i$ 个上同调层描述了 $X$ 的"对偶信息"。

---

## 二、$f^!$ 的计算

### 2.1 光滑态射

若 $f: X \to Y$ 是光滑的，相对维数为 $n$，则：

$$f^! \mathcal{G} \cong Lf^* \mathcal{G} \otimes \omega_{X/Y}[n]$$

其中 $\omega_{X/Y} = \bigwedge^n \Omega_{X/Y}^1$ 是相对典则层。这直接给出相对 Serre 对偶。

### 2.2 有限态射

若 $f: X \to Y$ 是有限态射，则：

$$f^! \mathcal{G} \cong \overline{\mathcal{H}om}_{\mathcal{O}_Y}(f_*\mathcal{O}_X, \mathcal{G})$$

这是有限态射下的对偶化公式，与局部对偶理论一致。

### 2.3 一般分解

对一般的固有态射，可以通过分解为光滑态射和闭浸入的复合来计算 $f^!$。若 $f = g \circ i$，其中 $i$ 是闭浸入，$g$ 是光滑的，则：

$$f^! = i^! \circ g^!$$

而闭浸入的 $i^!$ 可以通过局部上同调来计算。

---

## 三、残余复形与局部对偶

### 3.1 残余复形

Hartshorne 在《Residues and Duality》中系统发展了 Grothendieck 对偶，引入了**残余复形**（residue complex）。残余复形 $K_X^\bullet$ 是对偶化复形 $\omega_X^\bullet$ 的一种特殊代表，具有极佳的局部性质：

- 它是一个内射复形；
- 其第 $i$ 项由余维数为 $i$ 的点上的"残余模"组成；
- 微分由残余映射给出。

### 3.2 局部对偶

对局部环 $(A, \mathfrak{m})$，局部对偶定理断言：若 $A$ 是 Cohen-Macaulay 的，维数为 $n$，则：

$$H_{\mathfrak{m}}^i(M)^\vee \cong \text{Ext}_A^{n-i}(M, \omega_A)$$

其中 $H_{\mathfrak{m}}^i(M)$ 是局部上同调，$\omega_A$ 是典则模。这一定理是 Grothendieck 对偶在局部环上的体现。

---

## 四、应用

### 4.1 相交理论中的剩余公式

Grothendieck 对偶为相交理论中的**剩余公式**提供了理论基础。例如，在计算代数曲线上的留数时，残余复形给出了系统的计算方法。

### 4.2 导出代数几何

在 Lurie 的导出代数几何中，Grothendieck 对偶被推广到**导出环层空间**。$f^!$ 函子在导出范畴和 $\infty$-范畴框架中都存在，是导出对偶理论的核心。

### 4.3 算术几何

对算术簇（如定义在 $\mathbb{Z}$ 上的概形），Grothendieck 对偶与**算术对偶**（arithmetic duality）相结合，形成了研究算术上同调和李-塔特配对的重要工具。

---

## 五、习题

### 习题 1
设 $f: X \to Y$ 是 $n$ 维光滑射影态射。利用 Grothendieck 对偶证明相对 Serre 对偶：
$$R^i f_* \mathcal{F} \cong R^{n-i} f_* (\mathcal{F}^\vee \otimes \omega_{X/Y})^\vee$$

### 习题 2
设 $i: Z \hookrightarrow X$ 是闭浸入，余维数为 $c$。证明：$i^! \mathcal{O}_X \cong \omega_{Z/X}[-c]$，其中 $\omega_{Z/X}$ 是相对对偶层。

### 习题 3
解释为什么对非 Cohen-Macaulay 概形，对偶化复形 $\omega_X^\bullet$ 不能简单地用一个层（而不是复形）来表示。

### 习题 4
设 $C$ 是光滑射影曲线，$D$ 是有效除子。利用 Grothendieck 对偶解释 Riemann-Roch 定理中 $h^0(K_C - D) = h^1(D)$ 的出现。

---

## 延伸阅读

- **经典文献**：Hartshorne, R. *Residues and Duality*. Lecture Notes in Math. 20, Springer, 1966.
- **现代文献**：Neeman, A. "The Grothendieck duality theorem via Bousfield's techniques and Brown representability." *J. Amer. Math. Soc.* 9 (1996): 205–236.
- **项目内延伸阅读**：
  - [数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/22-上同调与Grothendieck对偶](../../../../数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/22-上同调与Grothendieck对偶.md)
  - [数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/21-上同调与Serre对偶](../../../../数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/21-上同调与Serre对偶.md)

---

**文档状态**：✅ 完成  
**字数**：约 2,200 字  
**最后更新**：2026-04-16
