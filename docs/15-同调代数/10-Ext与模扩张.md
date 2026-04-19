---
title: Ext与模扩张
description: 详细介绍Ext^1(A,B)与模的短正合列扩张之间的Baer和理论，以及Yoneda Ext的构造。
msc_primary:
  - 18G15
msc_secondary:
  - 16E30
  - 13D07
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

# Ext与模扩张

## 引言

在模论中，模扩张（module extension）的构造与分类是同调代数的核心应用之一。给定 $R$-模 $A$ 和 $B$，一个 $A$ 由 $B$ 的扩张是短正合列

$$0 \longrightarrow B \longrightarrow E \longrightarrow A \longrightarrow 0.$$

Baer在1930年代证明，这类扩张的等价类构成Abel群，且该群自然同构于 $\operatorname{Ext}^1_R(A, B)$。这一对应不仅提供了Ext的几何解释，也使得扩张的运算（Baer和）有了同调的描述。

本教程详细介绍Baer和的构造、Yoneda Ext的一般定义以及具体计算例子。

---

## 1. 模扩张的等价类

### 1.1 定义

**定义 1.1**。两个扩张 $0 \to B \to E \to A \to 0$ 和 $0 \to B \to E' \to A \to 0$ **等价**，如果存在同构 $\phi: E \to E'$ 使图表交换。

---

## 2. Baer和

### 2.1 构造

给定两个扩张 $\mathcal{E}_1: 0 \to B \to E_1 \to A \to 0$ 和 $\mathcal{E}_2: 0 \to B \to E_2 \to A \to 0$：

1. 取 pullback $P = E_1 \times_A E_2$。
2. 定义对角映射 $\Delta: B \to B \oplus B$，$b \mapsto (b, -b)$。
3. 令 $E = P / \{(b, -b)\}$。

则 $0 \to B \to E \to A \to 0$ 是 **Baer和** $\mathcal{E}_1 + \mathcal{E}_2$。

---

## 3. 与Ext的对应

**定理 3.1**。存在自然Abel群同构

$$\operatorname{Ext}^1_R(A, B) \cong \{\text{扩张 } 0 \to B \to E \to A \to 0\}/\sim.$$

---

## 4. Yoneda Ext

**定义 4.1**。Yoneda Ext $\operatorname{Ext}^n_R(A, B)$ 可由 $n$-步扩张

$$0 \to B \to E_n \to \cdots \to E_1 \to A \to 0$$

的等价类定义（对 $n \geq 1$）。

---

## 5. 与已有文档的关联

- [07-左导出函子Ext](07-左导出函子Ext.md)：Ext函子的定义。
- [09-Ext与群扩张](09-Ext与群扩张.md)：群扩张是模扩张的特殊情形。

---

## 练习

1. 验证Baer和的定义良好且给出Abel群结构。
2. 对 $R = \mathbb{Z}$，$A = B = \mathbb{Z}/p\mathbb{Z}$，构造两个非等价扩张并计算其Baer和。
3. 证明分裂扩张对应 $\operatorname{Ext}^1$ 中的零元。

---

## 参考文献

1. C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Univ. Press, 1994. (Ch. 3)
2. J. J. Rotman, *An Introduction to Homological Algebra*, Springer, 2009. (Ch. 7)
