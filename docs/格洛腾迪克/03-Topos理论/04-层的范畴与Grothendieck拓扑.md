---
title: 层的范畴与Grothendieck拓扑
description: 系统讲解Grothendieck拓扑的公理化定义、覆盖族、层条件、层化函子以及不同位型上的层范畴之间的联系。
msc_primary: 18

  - 18F10
  - 18B25
  - 14F20
processed_at: '2026-04-16'
---

# 层的范畴与 Grothendieck 拓扑

## 引言

Grothendieck 拓扑是经典拓扑概念的范畴论推广。在经典拓扑中，开集构成了空间的"局部结构"；而在 Grothendieck 拓扑中，覆盖的概念被推广到任意范畴上，使得我们可以在更广泛的数学对象上谈论"局部性质"和"层"。这一理论不仅是平展上同调、晶体上同调等现代几何理论的基石，也是 Grothendieck Topos 定义的核心。

本教程将系统介绍 Grothendieck 拓扑的定义、层的构造、层化过程以及不同拓扑之间的比较。

---

## 一、Grothendieck 拓扑的公理化

### 1.1 筛（Sieve）

设 $\mathcal{C}$ 是小范畴，$U \in \mathcal{C}$。$U$ 上的**筛** $S$ 是 $\mathcal{C}/U$ 的一个满子范畴，满足：若 $(V \xrightarrow{f} U) \in S$ 且 $W \xrightarrow{g} V$，则 $(W \xrightarrow{f \circ g} U) \in S$。

等价地，$U$ 上的筛是一个子预层 $S \subseteq y(U) = \text{Hom}_\mathcal{C}(-, U)$。

### 1.2 Grothendieck 拓扑

$\mathcal{C}$ 上的 **Grothendieck 拓扑** $J$ 为每个对象 $U$ 指定一族覆盖筛 $J(U)$，满足：

**G1（极大性）**：$y(U) \in J(U)$。

**G2（稳定性）**：若 $S \in J(U)$，$f: V \to U$，则 $f^*S = \{W \xrightarrow{g} V \mid f \circ g \in S\} \in J(V)$。

**G3（传递性）**：若 $S \in J(U)$，$T$ 是 $U$ 上的筛，且对所有 $(V \xrightarrow{f} U) \in S$ 有 $f^*T \in J(V)$，则 $T \in J(U)$。

### 1.3 Site（位型）

对 $(\mathcal{C}, J)$ 称为一个 **site**。site 是层论的 workspace。

---

## 二、层的定义

### 2.1 层条件

设 $(\mathcal{C}, J)$ 是 site，$F: \mathcal{C}^{\text{op}} \to \mathbf{Set}$ 是预层。$F$ 称为 **$J$-层**，如果对每个对象 $U \in \mathcal{C}$ 和每个覆盖筛 $S \in J(U)$，自然映射

$$F(U) \longrightarrow \text{Hom}_{\mathbf{PSh}(\mathcal{C})}(S, F)$$

是同构。

等价地，$F$ 是层当且仅当对每个覆盖筛 $S \in J(U)$，下图是等化子：

$$F(U) \longrightarrow \prod_{(V \to U) \in S} F(V) \rightrightarrows \prod_{(V \to U), (W \to U) \in S} F(V \times_U W)$$

### 2.2 层的例子

**Zariski 位型**：设 $\mathcal{C}$ 是概形范畴（或某个固定概形的开子概形范畴），覆盖由 Zariski 开覆盖给出。层就是通常的 Zariski 层。

**平展位型**：设 $\mathcal{C}$ 是固定概形 $X$ 上的平展概形范畴 $X_{\text{ét}}$，覆盖由平展满射族给出。层就是平展层。

**fpqc 位型**：覆盖由 fpqc（忠实平坦、拟紧）态射族给出。这是 most general 的代数几何拓扑，其层范畴非常重要。

---

## 三、层化

### 3.1 层化函子

设 $\mathbf{PSh}(\mathcal{C})$ 是预层范畴，$\mathbf{Sh}(\mathcal{C}, J)$ 是层范畴。包含函子 $i: \mathbf{Sh}(\mathcal{C}, J) \to \mathbf{PSh}(\mathcal{C})$ 有左伴随

$$a: \mathbf{PSh}(\mathcal{C}) \longrightarrow \mathbf{Sh}(\mathcal{C}, J)$$

称为**层化函子**（sheafification）。对预层 $F$，$a(F)$ 是满足泛性质的"最近"的层。

### 3.2 层化的显式构造

层化可以通过两次加号构造实现：

$$F^+(U) = \varinjlim_{S \in J(U)} \text{Hom}(S, F)$$

即 $F^+$ 在 $U$ 上的截面是覆盖筛到 $F$ 的相容族的正向极限。一般地，$F^{++} = a(F)$ 是层。

### 3.3 层范畴的性质

$\mathbf{Sh}(\mathcal{C}, J)$ 是一个 Grothendieck Topos，因此具有：
- 所有小极限和小余极限；
- 子对象分类器；
- 幂对象；
- 指数对象。

---

## 四、不同拓扑之间的比较

### 4.1 细化与态射

设 $J, J'$ 是 $\mathcal{C}$ 上的两个 Grothendieck 拓扑。若 $J' \supseteq J$（即 $J'$ 的覆盖筛更多），则称 $J'$ **细于** $J$。此时每个 $J'$-层都是 $J$-层，从而有包含：

$$\mathbf{Sh}(\mathcal{C}, J') \subseteq \mathbf{Sh}(\mathcal{C}, J)$$

### 4.2 典范拓扑

**典范拓扑**（canonical topology）是使所有可表预层都成为层的最大 Grothendieck 拓扑。它非常重要，因为任何可表函子在这个拓扑下自动是层。

### 4.3 态射诱导的拓扑

设 $u: \mathcal{C} \to \mathcal{D}$ 是函子，$J$ 是 $\mathcal{D}$ 上的拓扑。可以拉回 $J$ 得到 $\mathcal{C}$ 上的拓扑 $u^{-1}(J)$。这诱导了几何态射：

$$\mathbf{Sh}(\mathcal{C}, u^{-1}(J)) \longrightarrow \mathbf{Sh}(\mathcal{D}, J)$$

---

## 五、习题

### 习题 1
验证：拓扑空间 $X$ 的开集范畴上的 Grothendieck 拓扑（由通常开覆盖给出）满足 G1–G3。

### 习题 2
设 $\mathcal{C}$ 是有终对象的范畴。证明：若 $J$ 是 Grothendieck 拓扑，且 $J$ 包含空筛，则每个 $J$-层都是常值层。

### 习题 3
设 $F$ 是预层。证明：$F^+$ 满足粘接条件的"单值性"部分（即若局部截面相容，则整体截面唯一）。

### 习题 4
证明：Zariski 拓扑细于 fpqc 拓扑在概形开子集范畴上的限制。

---

## 延伸阅读

- **教材推荐**：Mac Lane, S. & Moerdijk, I. *Sheaves in Geometry and Logic*, Chap. III, Springer, 1992.
- **网络资源**：Stacks Project, Tag [00VH](https://stacks.math.columbia.edu/tag/00VH).
- **项目内延伸阅读**：
  - [数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/04-Topos理论/05-层的范畴与Grothendieck拓扑](../../../../数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/04-Topos理论/05-层的范畴与Grothendieck拓扑.md)
  - [数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/04-Topos理论/04-étale Topos与平展上同调](../../../../数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/04-Topos理论/04-étale Topos与平展上同调.md)

---

**文档状态**：✅ 完成  
**字数**：约 2,400 字  
**最后更新**：2026-04-16
