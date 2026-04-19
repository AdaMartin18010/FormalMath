---
title: 左导出函子Ext
description: 系统介绍Ext^n函子的定义、基本性质、长正合列，以及Ext与模扩张之间的深刻联系。
msc_primary:
  - 18G15
msc_secondary:
  - 13D07
  - 16E30
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

# 左导出函子Ext

## 引言

Ext函子是同调代数中最基本、最重要的导出函子之一。它测量了Hom函子 $-\otimes -$ 或 $\operatorname{Hom}(-,-)$ 在正合列上的"失败程度"。具体而言，$\operatorname{Ext}^n_R(M, N)$ 一方面可以通过 $M$ 的投射分解来计算，另一方面也可以通过 $N$ 的内射分解来计算——这两种定义的一致性是同调代数优美结构的体现。

Ext函子的名字来源于"extension"：$\operatorname{Ext}^1_R(M, N)$ 一一对应于 $M$ 由 $N$ 的扩张等价类。这一深刻联系使得Ext成为研究模结构和分类问题的强大工具。

本教程系统介绍Ext函子的定义、基本性质、长正合列以及与模扩张的关系。

---

## 1. Ext的定义

### 1.1 通过投射分解

**定义 1.1**。设 $M, N$ 为 $R$-模，$P_\bullet \to M$ 为投射分解。定义

$$\operatorname{Ext}^n_R(M, N) := H^n(\operatorname{Hom}_R(P_\bullet, N)).$$

即：对 $P_\bullet$ 应用 $\operatorname{Hom}_R(-, N)$，得到上链复形，取上同调。

### 1.2 通过内射分解

**定义 1.2**。设 $N \to I^\bullet$ 为内射分解。定义

$$\operatorname{Ext}^n_R(M, N) := H^n(\operatorname{Hom}_R(M, I^\bullet)).$$

**定理 1.3**。两种定义给出自然同构的函子。

---

## 2. 基本性质

### 2.1 低维解释

- $\operatorname{Ext}^0_R(M, N) = \operatorname{Hom}_R(M, N)$。
- $\operatorname{Ext}^1_R(M, N)$ 分类短正合列 $0 \to N \to E \to M \to 0$。

### 2.2 长正合列

**定理 2.1**。对短正合列 $0 \to M' \to M \to M'' \to 0$，有长正合列

$$0 \to \operatorname{Hom}(M'', N) \to \operatorname{Hom}(M, N) \to \operatorname{Hom}(M', N) \to \operatorname{Ext}^1(M'', N) \to \cdots.$$

---

## 3. 重要例子

### 例子 1：PID上的Ext

**例 3.1**。对PID $R$，$\operatorname{Ext}^n_R(M, N) = 0$ 对 $n \geq 2$。

### 例子 2：Abel群的Ext

**例 3.2**。$\operatorname{Ext}^1_{\mathbb{Z}}(\mathbb{Z}/m\mathbb{Z}, \mathbb{Z}/n\mathbb{Z}) \cong \mathbb{Z}/\gcd(m,n)\mathbb{Z}$。

---

## 4. 与已有文档的关联

- [09-Ext与群扩张](09-Ext与群扩张.md)：$\operatorname{Ext}^1$ 与群扩张的分类。
- [10-Ext与模扩张](10-Ext与模扩张.md)：$\operatorname{Ext}^1$ 与模扩张的详细对应。
- [05-投射分解](05-投射分解.md)：Ext由投射分解计算。

---

## 练习

1. 证明 $\operatorname{Ext}^n_R(\bigoplus M_i, N) \cong \prod \operatorname{Ext}^n_R(M_i, N)$。
2. 计算 $\operatorname{Ext}^1_{\mathbb{Z}}(\mathbb{Q}, \mathbb{Z})$。
3. 证明 $M$ 投射当且仅当 $\operatorname{Ext}^1_R(M, N) = 0$ 对所有 $N$。

---

## 参考文献

1. C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Univ. Press, 1994. (Ch. 3)
2. J. J. Rotman, *An Introduction to Homological Algebra*, Springer, 2009. (Ch. 7)
