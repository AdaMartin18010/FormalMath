---
title: 分类Topos与几何点
description: 深入讲解分类Topos的泛性质、几何点的分类、局部环分类子以及代数几何中常见的分类Topos例子。
msc_primary: 18

  - 18B25
  - 03C35
  - 14D23
processed_at: '2026-04-16'
---

# 分类 Topos 与几何点

## 引言

Grothendieck Topos 理论中最令人惊叹的成就之一，是 Joyal 和 Reyes 证明的**分类 Topos 定理**：每个几何理论都对应一个唯一的 Topos，使得到该 Topos 的几何态射一一对应于目标 Topos 中的模型。这一结果将逻辑、代数和几何完美地统一在一起。

**几何点**（geometric point）则是研究 Topos 局部结构的核心工具。在代数几何中，平展 Topos 的几何点对应于几何点 $\bar{x} \to X$，是定义平展茎和平展局部化的基础。本教程将深入介绍分类 Topos 和几何点的理论。

---

## 一、分类 Topos 的泛性质

### 1.1 陈述

设 $\mathbb{T}$ 是一个几何理论（由几何句子公理化）。存在唯一的（在同构意义下）Grothendieck Topos $\mathcal{B}(\mathbb{T})$，称为 $\mathbb{T}$ 的**分类 Topos**（classifying topos），使得对任意 Grothendieck Topos $\mathcal{E}$，有自然等价：

$$\text{Geom}(\mathcal{E}, \mathcal{B}(\mathbb{T})) \simeq \mathbf{Mod}(\mathbb{T}, \mathcal{E})$$

这里左边是到 $\mathcal{B}(\mathbb{T})$ 的几何态射范畴，右边是 $\mathbb{T}$ 在 $\mathcal{E}$ 中的模型范畴。

### 1.2 万有模型

分类 Topos $\mathcal{B}(\mathbb{T})$ 携带一个**万有模型**（universal model）$M_{\text{univ}}$。任何其他 Topos $\mathcal{E}$ 中的模型 $M$ 都可以通过唯一几何态射 $f: \mathcal{E} \to \mathcal{B}(\mathbb{T})$ 拉回万有模型得到：

$$M \cong f^*(M_{\text{univ}})$$

### 1.3 构造

分类 Topos 可以显式构造为某个 site 上的层范畴。具体地：
- 取范畴 $\mathcal{C}_\mathbb{T}$，其对象是 $\mathbb{T}$ 的公式（在某种适当意义下）；
- 覆盖由 $\mathbb{T}$ 中的可证蕴涵关系给出；
- 则 $\mathcal{B}(\mathbb{T}) = \mathbf{Sh}(\mathcal{C}_\mathbb{T}, J_\mathbb{T})$。

---

## 二、重要的分类 Topos

### 2.1 对象分类子

分类"有一个对象"的几何理论的 Topos 称为**对象分类子**（object classifier）。它的显式模型为：

$$\mathcal{S}[O] = \mathbf{PSh}(\mathbf{Fin}^{\text{op}})$$

即有限集范畴的对偶上的预层范畴。到 $\mathcal{S}[O]$ 的几何态射对应于目标 Topos 中的对象。

更精确地说，若 $f: \mathcal{E} \to \mathcal{S}[O]$ 是几何态射，则 $f^*(U) \in \mathcal{E}$ 就是对应的"对象"，其中 $U$ 是万有对象。

### 2.2 环分类子

分类交换环理论的 Topos 是：

$$\mathcal{S}[\text{Ring}] = \mathbf{Sh}(\mathbf{CRing}^{\text{op}}, \text{Zariski})$$

即到交换环反范畴上的 Zariski 层。万有模型就是结构层 $\mathcal{O}$，它在对象 $\text{Spec}(A)$ 上的截面为 $A$ 本身。

### 2.3 局部环分类子

局部环理论是环理论加上额外的几何句子：$0 \neq 1$ 和 $\forall x. (x \text{ 可逆}) \vee (1-x \text{ 可逆})$。局部环的分类 Topos 为：

$$\mathcal{S}[\text{LocRing}] = \mathbf{Sh}(\mathbf{CRing}^{\text{op}}, \text{Zariski})$$

但这里的 site 有所不同：它是局部环的 Zariski 位型上的层。到它的几何态射对应于局部环层空间（locally ringed space）。

### 2.4 代数几何中的分类 Topos

许多代数几何对象都可以用分类 Topos 描述：
- 向量丛分类子；
- 概形分类子；
- 模空间分类子（在一定条件下）。

这揭示了模空间理论与 Topos 理论之间的深刻联系。

---

## 三、几何点

### 3.1 定义

Grothendieck Topos $\mathcal{E}$ 的一个**点**是一个几何态射：

$$p: \mathbf{Set} \longrightarrow \mathcal{E}$$

由一对伴随 $p^* \dashv p_*$ 给出。$p^*$ 称为在该点上的**茎函子**。

### 3.2 点的集合

$\mathcal{E}$ 的所有点构成的范畴记为 $\text{Pt}(\mathcal{E})$。对层 Topos $\mathbf{Sh}(X)$，若 $X$ 是 Sober 空间，则 $\text{Pt}(\mathbf{Sh}(X)) \cong X$。

但对一般 Topos（如平展 Topos），可能存在"非经典"的点，即不来自拓扑空间中点的点。

### 3.3 平展 Topos 的点

设 $X$ 是概形。平展 Topos $X_{\text{ét}}^\sim$ 的点可以描述为**几何点**的等价类：

$$\bar{x}: \text{Spec}(k) \longrightarrow X$$

其中 $k$ 是代数闭域。每个几何点 $\bar{x}$ 给出点 $p_{\bar{x}}: \mathbf{Set} \to X_{\text{ét}}^\sim$，其茎函子为：

$$p_{\bar{x}}^*(\mathcal{F}) = \mathcal{F}_{\bar{x}} = \varinjlim_{(U, \bar{u})} \mathcal{F}(U)$$

这里极限取遍所有平展邻域 $(U, \bar{u})$，其中 $U \to X$ 平展且 $\bar{u}$ 提升 $\bar{x}$。

### 3.4 点的充分性

Topos $\mathcal{E}$ 称为**有充分点**的，若层的态射 $\varphi: \mathcal{F} \to \mathcal{G}$ 是同构当且仅当在所有点上的茎映射 $\varphi_p: \mathcal{F}_p \to \mathcal{G}_p$ 都是同构。

平展 Topos 是有充分点的。这类似于拓扑空间上的层：一个层映射是同构当且仅当它在所有茎上是同构。

---

## 四、应用：平展局部化

### 4.1 严格 Hensel 局部环

对几何点 $\bar{x} \to X$，其平展茎的环结构为：

$$\mathcal{O}_{X, \bar{x}}^{\text{sh}} = \varinjlim_{(U, \bar{u})} \Gamma(U, \mathcal{O}_U)$$

这是一个**严格 Hensel 局部环**。它是 Hensel 局部环，且其剩余域是代数闭的。

### 4.2 局部性质

许多代数几何中的局部性质可以通过平展局部化来定义。例如：
- 概形光滑当且仅当它在每个几何点的平展局部化上光滑；
- 层平坦当且仅当它在每个平展茎上平坦。

这反映了平展拓扑比 Zariski 拓扑更适合研究局部性质的深刻事实。

---

## 五、习题

### 习题 1
证明：对 sober 拓扑空间 $X$，$\text{Pt}(\mathbf{Sh}(X)) \cong X$。

### 习题 2
设 $\mathbb{T}$ 是群的理论。描述分类 Topos $\mathcal{B}(\mathbb{T})$ 的显式构造。

### 习题 3
设 $\bar{x}: \text{Spec}(k) \to X$ 是几何点，$\mathcal{F}$ 是 $X$ 上的平展层。证明：$\mathcal{F}_{\bar{x}}$ 只依赖于 $\bar{x}$ 的像点 $x \in X$ 和剩余域扩张 $k(x) \subseteq k$。

### 习题 4
解释为什么平展 Topos 中存在"非经典"点（即不来自 $X$ 中点的点），并给出一个例子。

---

## 延伸阅读

- **教材推荐**：Mac Lane, S. & Moerdijk, I. *Sheaves in Geometry and Logic*, Chap. VIII, Springer, 1992.
- **网络资源**：nLab, "Classifying topos".
- **项目内延伸阅读**：
  - [数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/04-Topos理论/10-分类Topos与几何点](../../../../数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/04-Topos理论/10-分类Topos与几何点.md)
  - [数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/04-Topos理论/11-分类定理与Topos分类](../../../../数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/04-Topos理论/11-分类定理与Topos分类.md)

---

**文档状态**：✅ 完成  
**字数**：约 2,600 字  
**最后更新**：2026-04-16
