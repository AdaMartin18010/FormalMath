---
title: Hochschild上同调
description: 介绍Hochschild上同调的定义、与代数形变的关系、Gerstenhaber代数结构，以及在非交换几何中的应用。
msc_primary:
  - 16E40
msc_secondary:
  - 16S80
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
    - id: gerstenhaber
      type: textbook
      title: Deformation Theory
      authors:
        - Robin Hartshorne
      publisher: Springer
      year: 2010
      msc: 14-01
  databases:
    - id: nlab
      type: database
      name: nLab
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
---

# Hochschild上同调

## 引言

Hochschild上同调（Hochschild cohomology）是研究结合代数及其双模的标准同调工具。它由Gerhard Hochschild在1945年引入，是群上同调和Lie代数上同调到结合代数范畴的推广。

Hochschild上同调最引人注目的应用之一是在代数形变理论中：$H^2(A,A)$ 分类代数的无穷小形变，$H^3(A,A)$ 包含形变的障碍。此外，Hochschild上同调具有Gerstenhaber代数结构（带Lie括号的交换代数），这一结构在弦论和镜像对称中有重要应用。

本教程介绍Hochschild上同调的定义、与形变理论的联系以及基本计算。

---

## 1. Hochschild复形

### 1.1 定义

设 $A$ 为 $k$-代数，$M$ 为 $A$-$A$-双模。

**定义 1.1**。$C^n(A, M) := \operatorname{Hom}_k(A^{\otimes n}, M)$。Hochschild上边缘

$$d f(a_1, \dots, a_{n+1}) = a_1 f(a_2, \dots) + \sum (-1)^i f(\dots, a_i a_{i+1}, \dots) + (-1)^{n+1} f(a_1, \dots, a_n) a_{n+1}.$$

**定义 1.2**。$HH^n(A, M) := H^n(C^\bullet(A, M), d)$。

---

## 2. 低维解释

### 2.1 $HH^0$

$HH^0(A, M) = M^A = \{m \mid am = ma \text{ 对所有 } a\}$（中心元素）。

### 2.2 $HH^1$

**命题 2.1**。$HH^1(A, M) = \operatorname{Der}(A, M) / \operatorname{InnDer}(A, M)$。

### 2.3 $HH^2$ 与形变

**定理 2.2**。$HH^2(A, A)$ 分类代数的无穷小形变（一阶形变）。

---

## 3. Gerstenhaber代数

**定理 3.1**。$HH^*(A, A)$ 具有Gerstenhaber代数结构：
- 杯积 $\smile$：分次交换；
- Gerstenhaber括号 $[-,-]$：Poisson括号结构。

---

## 4. 与已有文档的关联

- [17-群上同调](17-群上同调.md)：群代数 $kG$ 的Hochschild上同调与群上同调相关。
- [18-Lie代数上同调](18-Lie代数上同调.md)：包络代数 $U(\mathfrak{g})$ 的Hochschild上同调与Lie代数上同调相关。

---

## 练习

1. 计算 $HH^*(k[x], k[x])$。
2. 证明 $HH^2(A, A)$ 分类结合积的形变 $a \star b = ab + \epsilon f(a,b)$。
3. 证明半单代数的 $HH^n(A, A) = 0$ 对 $n > 0$。

---

## 参考文献

1. G. Hochschild, "On the cohomology groups of an associative algebra", *Ann. of Math.*, 1945.
2. M. Gerstenhaber, "The cohomology structure of an associative ring", *Ann. of Math.*, 1963.
