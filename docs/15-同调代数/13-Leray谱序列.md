---
title: Leray谱序列
description: 详细介绍Leray谱序列的构造、与层上同调的关系，以及它在纤维丛和代数几何中的应用。
msc_primary:
  - 18G40
msc_secondary:
  - 14F25
  - 55R20
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
    - id: godement
      type: textbook
      title: Topologie Algébrique et Théorie des Faisceaux
      authors:
        - Roger Godement
      publisher: Hermann
      year: 1958
      msc: 55-01
  databases:
    - id: nlab
      type: database
      name: nLab
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
---

# Leray谱序列

## 引言

Leray谱序列是层上同调理论中最基本的谱序列。给定连续映射 $f: X \to Y$ 和 $X$ 上的层 $\mathcal{F}$，Leray谱序列将 $X$ 上的层上同调 $H^*(X, \mathcal{F})$ 与 $Y$ 上的"纤维上同调" $R^q f_* \mathcal{F}$ 联系起来：

$$E_2^{p,q} = H^p(Y, R^q f_* \mathcal{F}) \Rightarrow H^{p+q}(X, \mathcal{F}).$$

当 $f$ 是纤维丛时，$R^q f_* \mathcal{F}$ 的茎就是纤维的上同调，这使得Leray谱序列成为从纤维和底空间的上同调计算总空间上同调的标准工具。

本教程介绍Leray谱序列的构造、关键性质以及应用。

---

## 1. 高阶直接像

### 1.1 定义

**定义 1.1**。设 $f: X \to Y$，$\mathcal{F}$ 为 $X$ 上的层。**高阶直接像** $R^q f_* \mathcal{F}$ 是 $Y$ 上的层，与整体截面函子的复合的导出函子：

$$R^q f_* \mathcal{F} := H^q \circ f_* \text{ 的右导出函子。}$$

茎上：$(R^q f_* \mathcal{F})_y = H^q(f^{-1}(y), \mathcal{F}|_{f^{-1}(y)})$（在适当条件下）。

---

## 2. Leray谱序列

**定理 2.1（Leray）**。对连续映射 $f: X \to Y$ 和层 $\mathcal{F}$，存在第一象限谱序列

$$E_2^{p,q} = H^p(Y, R^q f_* \mathcal{F}) \Rightarrow H^{p+q}(X, \mathcal{F}).$$

*构造*。取 $\mathcal{F}$ 的内射分解 $\mathcal{I}^\bullet$。则 $f_* \mathcal{I}^\bullet$ 是 $Y$ 上的复形层。用 $Y$ 上的内射分解计算 $H^p(Y, -)$，得到双复形，其谱序列即为Leray谱序列。$\square$

---

## 3. 应用

### 例子 1：纤维丛

**例 3.1**。若 $f: E \to B$ 是纤维丛，纤维 $F$，则 $R^q f_* \underline{\mathbb{Z}}$ 是局部常值层（对应于 $\pi_1(B)$ 在 $H^q(F)$ 上的单值表示）。Leray谱序列从纤维和底空间的上同调计算 $H^*(E)$。

### 例子 2：投影的消灭

**例 3.2**。若 $f: X \to Y$ 的所有纤维上 $H^q = 0$ 对 $q > 0$（如 $f$ 有限），则 $E_2$ 退化，$H^p(X, \mathcal{F}) \cong H^p(Y, f_* \mathcal{F})$。

---

## 4. 与已有文档的关联

- [12-谱序列基础](12-谱序列基础.md)：谱序列的一般理论。
- [14-Grothendieck谱序列](14-Grothendieck谱序列.md)：Leray谱序列是Grothendieck谱序列的特例。

---

## 练习

1. 对平凡丛 $E = B \times F$，用Künneth公式验证Leray谱序列的退化。
2. 证明若 $f$ 是仿射态射且 $\mathcal{F}$ 拟凝聚，则 $R^q f_* \mathcal{F} = 0$ 对 $q > 0$（Serre消失）。
3. 用Leray谱序列计算 $H^*(\mathbb{P}^n, \mathcal{O}(k))$。

---

## 参考文献

1. R. Godement, *Topologie Algébrique et Théorie des Faisceaux*, Hermann, 1958.
2. C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Univ. Press, 1994. (Ch. 5)
3. J.-P. Serre, "Homologie singulière des espaces fibrés", *Ann. of Math.*, 1951.
