---
title: Lie代数上同调
description: 介绍Lie代数上同调的Chevalley-Eilenberg复形、低维解释，以及它与Lie代数表示理论和形变理论的联系。
msc_primary:
  - 17B56
msc_secondary:
  - 17B10
  - 18G60
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
    - id: knapp_lie
      type: textbook
      title: Lie Groups, Lie Algebras, and Cohomology
      authors:
        - Anthony W. Knapp
      publisher: Princeton University Press
      year: 1988
      msc: 22-01
  databases:
    - id: nlab
      type: database
      name: nLab
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
---

# Lie代数上同调

## 引言

Lie代数上同调（Lie algebra cohomology）是群上同调的Lie代数类比。它由Chevalley和Eilenberg在1948年系统引入，使用外代数来构造上链复形。Lie代数上同调与Lie代数的表示理论、形变理论和特征标理论有深刻联系：$H^1$ 与导子相关，$H^2$ 分类Lie代数的形变，$H^3$ 与结构常数的Jacobi恒等式障碍相关。

本教程介绍Chevalley-Eilenberg复形的构造、低维解释以及典型计算。

---

## 1. Chevalley-Eilenberg复形

### 1.1 定义

设 $\mathfrak{g}$ 为Lie代数，$M$ 为 $\mathfrak{g}$-模。

**定义 1.1**。$C^n(\mathfrak{g}, M) := \operatorname{Hom}_k(\Lambda^n \mathfrak{g}, M)$。上边缘

$$d\omega(x_0, \dots, x_n) = \sum_{i<j} (-1)^{i+j} \omega([x_i, x_j], x_0, \dots, \widehat{x_i}, \dots, \widehat{x_j}, \dots, x_n) + \sum_i (-1)^i x_i \cdot \omega(x_0, \dots, \widehat{x_i}, \dots, x_n).$$

**定义 1.2**。$H^n(\mathfrak{g}, M) := H^n(C^\bullet(\mathfrak{g}, M), d)$。

---

## 2. 低维解释

### 2.1 $H^0$

$H^0(\mathfrak{g}, M) = M^{\mathfrak{g}} = \{m \mid x \cdot m = 0 \text{ 对所有 } x\}$。

### 2.2 $H^1$

**命题 2.1**。$H^1(\mathfrak{g}, M) = \operatorname{Der}(\mathfrak{g}, M) / \operatorname{IDer}(\mathfrak{g}, M)$。

### 2.3 $H^2$

**定理 2.2**。$H^2(\mathfrak{g}, M)$ 分类Lie代数扩张 $0 \to M \to \widetilde{\mathfrak{g}} \to \mathfrak{g} \to 0$。

---

## 3. Whitehead引理

**定理 3.1（Whitehead）**。设 $\mathfrak{g}$ 为半单Lie代数，$M$ 有限维。
1. $H^1(\mathfrak{g}, M) = 0$。
2. $H^2(\mathfrak{g}, M) = 0$。

*推论*。半单Lie代数的有限维表示完全可约（Weyl定理）。

---

## 4. 与已有文档的关联

- [17-群上同调](17-群上同调.md)：Lie代数上同调是群上同调的Lie类比。
- [19-Hochschild上同调](19-Hochschild上同调.md)：Hochschild上同调是结合代数类比。

---

## 练习

1. 计算 $H^*(\mathfrak{gl}(1), k)$。
2. 证明Abel Lie代数 $\mathfrak{a}$ 的 $H^n(\mathfrak{a}, k) \cong \Lambda^n \mathfrak{a}^*$。
3. 从Whitehead引理推导Weyl完全可约定理。

---

## 参考文献

1. C. Chevalley and S. Eilenberg, "Cohomology theory of Lie groups and Lie algebras", *Trans. AMS*, 1948.
2. A. W. Knapp, *Lie Groups, Lie Algebras, and Cohomology*, Princeton Univ. Press, 1988.
