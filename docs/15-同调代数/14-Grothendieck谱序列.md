---
title: Grothendieck谱序列
description: 介绍Grothendieck谱序列的构造、导出函子复合的谱序列理论，以及它在层上同调和群上同调中的应用。
msc_primary:
  - 18G40
msc_secondary:
  - 18G10
  - 18G15
processed_at: '2026-04-20'
references:
  textbooks:
    - id: weibel_ha
      type: textbook
      title: An Introduction to Homological Algebra
      authors:
        - Charles A. Weibel
      publisher: Cambridge University Press
      year: 1994
      msc: 18-01
    - id: rotman_ha
      type: textbook
      title: An Introduction to Homological Algebra
      authors:
        - Joseph J. Rotman
      publisher: Springer
      year: 2009
      msc: 18-01
  databases:
    - id: nlab
      type: database
      name: nLab
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
---

# Grothendieck谱序列

## 引言

Grothendieck谱序列是同调代数中最一般的谱序列构造之一。它处理的问题是：给定两个加性函子 $F: \mathcal{A} \to \mathcal{B}$ 和 $G: \mathcal{B} \to \mathcal{C}$，如何从左导出函子（或右导出函子）$L_pF$ 和 $L_qG$ 来计算复合函子 $G \circ F$ 的导出函子 $L_n(G \circ F)$？

Grothendieck在1957年的著名论文中给出了答案：在满足适当的兼容性条件（$F$ 将投射对象映为 $G$-acyclic对象）下，存在谱序列

$$E_2^{p,q} = (L_p G)(L_q F)(A) \Rightarrow L_{p+q}(G \circ F)(A).$$

这一定理统一了Leray谱序列、Lyndon/Hochschild-Serre谱序列等许多经典构造。

本教程介绍Grothendieck谱序列的构造、关键假设以及应用。

---

## 1. 基本设定

### 1.1 假设

设 $\mathcal{A}, \mathcal{B}, \mathcal{C}$ 为Abel范畴，有足够投射对象。$F: \mathcal{A} \to \mathcal{B}$，$G: \mathcal{B} \to \mathcal{C}$ 为右正合加性函子。

**关键假设**：$F$ 将投射对象映为 $G$-acyclic对象（即 $L_q G(FP) = 0$ 对 $q > 0$ 和投射 $P$）。

---

## 2. Grothendieck谱序列

**定理 2.1（Grothendieck）**。在上述假设下，对每个 $A \in \mathcal{A}$，存在第一象限谱序列

$$E_2^{p,q} = (L_p G)(L_q F)(A) \Rightarrow L_{p+q}(G \circ F)(A).$$

*构造*。取 $A$ 的投射分解 $P_\bullet$。则 $F(P_\bullet)$ 是 $G$-acyclic分解。对 $F(P_\bullet)$ 取Cartan-Eilenberg分解，得到双复形。两个边缘谱序列之一退化，另一给出Grothendieck谱序列。$\square$

---

## 3. 应用

### 3.1 Leray谱序列

**例 3.1**。$f: X \to Y$，$\Gamma_Y \circ f_* = \Gamma_X$。$f_*$ 将内射层映为 $\Gamma_Y$-acyclic层（在Noether情形）。Grothendieck谱序列给出Leray谱序列。

### 3.2 Hochschild-Serre谱序列

**例 3.2**。群扩张 $1 \to N \to G \to Q \to 1$。$G$-模的 $N$-不变量函子复合 $Q$-不变量给出Grothendieck谱序列：

$$E_2^{p,q} = H^p(Q, H^q(N, M)) \Rightarrow H^{p+q}(G, M).$$

---

## 4. 与已有文档的关联

- [12-谱序列基础](12-谱序列基础.md)：谱序列的一般理论。
- [13-Leray谱序列](13-Leray谱序列.md)：Leray谱序列是Grothendieck谱序列的特例。
- [17-群上同调](17-群上同调.md)：Hochschild-Serre谱序列。

---

## 练习

1. 验证Leray谱序列是Grothendieck谱序列的特例。
2. 从Grothendieck谱序列推导Hochschild-Serre谱序列。
3. 证明若 $F$ 正合，则Grothendieck谱序列在第一页退化。

---

## 参考文献

1. A. Grothendieck, "Sur quelques points d'algèbre homologique", *Tôhoku Math. J.*, 1957.
2. C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Univ. Press, 1994. (Ch. 5)
