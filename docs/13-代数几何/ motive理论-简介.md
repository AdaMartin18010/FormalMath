---
title: Motive理论简介
description: 系统介绍Grothendieck的motive理论愿景、纯motive与混合motive的构造、上同调实现函子以及标准猜想的历史背景与现代意义。
msc_primary: 14F42
msc_secondary:
- 14C15
- 14G10
processed_at: '2026-04-16'
references:
  textbooks:
    - id: hartshorne_ag
      type: textbook
      title: Algebraic Geometry
      authors:
      - Robin Hartshorne
      publisher: Springer
      edition: 1st
      year: 1977
      isbn: 978-0387902449
      msc: 14-01
      chapters: []
      url: ~
    - id: vakil_foag
      type: textbook
      title: Foundations of Algebraic Geometry
      authors:
      - Ravi Vakil
      publisher: self-published
      edition: draft
      year: 2024
      isbn: ~
      msc: 14-01
      chapters: []
      url: "https://math.stanford.edu/~vakil/216blog/"
  databases:
    - id: nlab
      type: database
      name: nLab
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
      consulted_at: 2026-04-17
    - id: stacks_project
      type: database
      name: Stacks Project
      entry_url: "https://stacks.math.columbia.edu/tag/{tag}"
      consulted_at: 2026-04-17
    - id: zbmath
      type: database
      name: zbMATH Open
      entry_url: "https://zbmath.org/?q=an:{zb_id}"
      consulted_at: 2026-04-17
---

# Motive 理论简介

## 引言

1960年代，格洛腾迪克在创立 étale 上同调的同时，提出了一个更为宏大的愿景——**motive 理论**（motive theory）。他发现，对于同一个代数簇，存在多种不同的上同调理论：Betti 上同调、de Rham 上同调、étale 上同调、晶体上同调等。这些理论都给出相似的数值不变量（如 Betti 数），但它们的系数域不同，结构也各有特色。格洛腾迪克问道：是否存在一个"普适的上同调理论"，使得所有这些具体理论都是它的"实现"？

这个普适的对象，他称之为 **motive**——源自法语 "motif"，意为"动机"或"主题"。Motive 理论至今仍是代数几何中最深刻、最神秘的领域之一。本教程将系统介绍 motive 的基本概念、构造方法以及与之相伴的**标准猜想**。

---

## 一、Motive 的动机：上同调的统一

### 1.1 多种上同调理论

设 $X$ 是复代数簇。我们有以下上同调理论：

- **Betti 上同调**：$H_B^i(X) = H^i(X(\mathbb{C}), \mathbb{Q})$，拓扑方法；
- **de Rham 上同调**：$H_{\text{dR}}^i(X) = \mathbb{H}^i(X, \Omega_X^\bullet)$，代数微分形式；
- **étale 上同调**：$H_{\text{ét}}^i(X, \mathbb{Q}_\ell)$，$\ell \neq \text{char}$，算术方法；
- **晶体上同调**：$H_{\text{cris}}^i(X/W)$，特征 $p$ 方法。

比较定理告诉我们，这些理论在复数域上密切相关：

$$H_B^i(X) \otimes_{\mathbb{Q}} \mathbb{C} \cong H_{\text{dR}}^i(X), \quad H_B^i(X) \otimes_{\mathbb{Q}} \mathbb{Q}_\ell \cong H_{\text{ét}}^i(X, \mathbb{Q}_\ell)$$

### 1.2 格洛腾迪克的愿景

格洛腾迪克设想存在一个**motive 范畴** $\mathbf{Mot}(k)$，使得对每个上同调理论 $H^*$，存在**实现函子**（realization functor）：

$$r_H: \mathbf{Mot}(k) \longrightarrow \mathbf{Vec}_K$$

且对任意光滑射影簇 $X$，存在对象 $h(X) \in \mathbf{Mot}(k)$（$X$ 的 motive），满足：

$$r_H(h(X)) = H^*(X)$$

换言之，$h(X)$ 是所有上同调理论的共同"源头"。

---

## 二、纯 Motive 的构造

### 2.1 代数对应

设 $X, Y$ 是域 $k$ 上的光滑射影簇，维数分别为 $d_X, d_Y$。**代数对应**（algebraic correspondence）是 $X \times Y$ 上的代数圈的某种等价类：

$$\text{Corr}^r(X, Y) = A^{d_X + r}(X \times Y)$$

其中 $A^*$ 表示 Chow 群（代数圈模去有理等价），$r$ 是对应次数。

### 2.2 等价关系

为了构造 motive 范畴，需要对代数圈施加适当的等价关系。常用的等价关系有：

- **有理等价**（rational equivalence）：最粗的等价；
- **代数等价**（algebraic equivalence）；
- **同调等价**（homological equivalence）：两个圈在所有上同调理论中给出相同的类；
- **数值等价**（numerical equivalence）：两个圈与任意余维互补圈的相交数相同。

我们有包含关系：

$$\text{rat} \subseteq \text{alg} \subseteq \text{hom} \subseteq \text{num}$$

### 2.3 纯 Motive 范畴

**纯 motive 范畴** $\mathbf{Mot}_{\sim}(k)$ 定义如下：
- **对象**：三元组 $(X, p, m)$，其中 $X$ 是光滑射影簇，$p \in \text{Corr}^0(X, X)$ 是投影算子（$p^2 = p$），$m \in \mathbb{Z}$ 是 Tate 扭次数；
- **态射**：
  $$\text{Hom}((X, p, m), (Y, q, n)) = q \circ \text{Corr}^{n-m}(X, Y) \circ p$$

当使用数值等价时，$\mathbf{Mot}_{\text{num}}(k)$ 是一个**半单 Abel 范畴**（若标准猜想成立）。

### 2.4 例子

- **Tate motive**：$\mathbb{L} = (\mathbb{P}^1, p, 0)$，其中 $p$ 是某个投影。它对应于上同调中的 $H^2(\mathbb{P}^1)$。Tate 扭定义为 $\mathbb{L}^{\otimes m} = (\text{pt}, \text{id}, m)$。
- **Artin motive**：零维簇的 motive，对应于 Galois 表示。
- **Abel 簇的 motive**：由 Kimura-O'Sullivan 定理，Abel 簇的 motive 是有限维的。

---

## 三、Motive 的上同调实现

### 3.1 Betti 实现

对 $k \subseteq \mathbb{C}$，Betti 实现函子为：

$$H_B: \mathbf{Mot}(\mathbb{C}) \longrightarrow \mathbf{HS}_{\mathbb{Q}}, \quad h(X) \longmapsto H_B^*(X)$$

右边是 $
\text{Q}$-Hodge 结构的范畴。这是 motive 的 Hodge 实现。

### 3.2 étale 实现

对任意域 $k$，étale 实现为：

$$H_{\text{ét}}: \mathbf{Mot}(k) \longrightarrow \mathbf{Rep}(G_k, \mathbb{Q}_\ell)$$

其中 $G_k = \text{Gal}(k^{\text{sep}}/k)$ 是绝对 Galois 群，右边是 $G_k$ 的 $\ell$-进表示范畴。

### 3.3 de Rham 与晶体实现

- **de Rham 实现**：$H_{\text{dR}}: \mathbf{Mot}(k) \to \mathbf{Vec}_k$，带有 Hodge 滤过和 Frobenius 结构（若 $k$ 是 $p$-adic 域）。
- **晶体实现**：对特征 $p$ 的域，$H_{\text{cris}}: \mathbf{Mot}(k) \to \mathbf{F\text{-}Isoc}(k)$。

---

## 四、标准猜想

### 4.1 历史背景

格洛腾迪克在 1960 年代提出了**标准猜想**（standard conjectures），旨在保证 motive 范畴的良好性质。这些猜想若成立，将证明：
- 数值等价等于同调等价；
- 纯 motive 范畴是半单 Abel 范畴；
- Weil 猜想可以从 motive 理论直接推出。

### 4.2 标准猜想 A（Lefschetz 标准猜想）

设 $X$ 是 $n$ 维光滑射影簇，$L: H^i(X) \to H^{i+2}(X)$ 是 Lefschetz 算子（与超平面类的杯积）。

**标准猜想 A**：算子

$$L^{n-i}: H^i(X) \longrightarrow H^{n+i}(X)$$

是同构，且其逆 $L^{-(n-i)}$ 由代数圈给出。

### 4.3 标准猜想 B（Hodge 指标定理）

在 primitive 上同调上，由 Lefschetz 分解诱导的配对满足确定的符号性质。这一猜想在复几何中等价于经典的 Hodge-Riemann 双线性关系。

### 4.4 标准猜想 C 与 D

- **C（数值等价 = 同调等价）**：同调等价与数值等价一致。
- **D（Künneth 型）**：motive 的 Künneth 分解由代数圈给出。

### 4.5 现状

标准猜想在以下情形已证明：
- 曲线、Abel 簇；
- 某些类型的曲面（如 K3 曲面、完全交）；
- 特征零的部分情形。

但一般情形仍是开放问题，被认为是代数几何中最困难的问题之一。

---

## 五、混合 Motive

### 5.1 从纯到混合

纯 motive 只适用于光滑射影簇。对一般的（可能是奇异或非紧的）代数簇，Deligne 在 1970 年代发展了**混合 Hodge 结构**理论。Voevodsky、Levine、Hanamura 等人随后发展了**混合 motive 理论**。

### 5.2 Voevodsky 的三角范畴

Voevodsky 构造了**混合 motive 的三角范畴** $DM(k)$，其中的对象对应于代数簇的 motive，但允许权重分解：

$$M = \bigoplus_n \text{Gr}_n^W M$$

$DM(k)$ 是一个张量三角范畴，具有六函子形式体系。

### 5.3 应用

混合 motive 在以下领域有重要应用：
- 代数 K-理论（Bloch-Kato 猜想，后由 Voevodsky 证明）；
- 代数圈的 Chow 群；
- 代数几何中的同伦理论（$\mathbb{A}^1$-同伦论）。

---

## 六、习题

### 习题 1
解释为什么 motive 范畴需要代数对应作为态射，而不能简单地用簇的态射。

### 习题 2
设 $X$ 是光滑射影曲线。证明其 motive 可以分解为 $h(X) = h^0(X) \oplus h^1(X) \oplus h^2(X)$，其中 $h^2(X) \cong \mathbb{L}$。

### 习题 3
解释标准猜想 A 如何蕴涵 Hard Lefschetz 定理的"代数版本"。

### 习题 4
设 $X = \mathbb{P}^n$。计算 $h(X)$ 在 motive 范畴中的分解。

---

## 延伸阅读

- **综述文献**：Kleiman, S.L. "The standard conjectures." *Motives* (1994): 3–20.
- **教材推荐**：André, Y. *Une introduction aux motifs*, Panoramas et Synthèses 17, SMF, 2004.
- **网络资源**：nLab, "Motive".
- **项目内延伸阅读**：
  - [数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/06-其他数学贡献/08-Motive理论与标准猜想](../../../../数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/06-其他数学贡献/08-Motive理论与标准猜想.md)

---

**文档状态**：✅ 完成  
**字数**：约 3,200 字  
**最后更新**：2026-04-16
