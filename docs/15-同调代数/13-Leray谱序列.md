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

谱序列是同调代数中最强大的计算工具之一，它将复杂的同调群计算分解为若干较简单的步骤。Leray谱序列是谱序列理论中最早且最重要的例子，它处理的问题是：给定连续映射 $f: X \to Y$ 和 $X$ 上的层 $\mathcal{F}$，如何从底空间 $Y$ 和纤维 $f^{-1}(y)$ 的上同调信息来重构总空间 $X$ 的上同调 $H^*(X, \mathcal{F})$？

Leray在1946-1950年间发展了层论与谱序列理论，其动机来自于研究纤维丛的上同调。当 $f: E \to B$ 是纤维丛时，高阶直接像层 $R^q f_* \mathcal{F}$ 的茎恰好是纤维的上同调，Leray谱序列因此提供了从纤维和底空间计算总空间上同调的系统框架。

本教程从Grothendieck谱序列的一般理论出发，导出Leray谱序列，分析其退化条件，并给出具体计算例子。

---

## 1. 高阶直接像层

### 1.1 直接像函子

设 $f: X \to Y$ 为拓扑空间之间的连续映射，$\mathcal{F}$ 为 $X$ 上的Abel群层。

**定义 1.1（直接像层）**。**直接像层** $f_* \mathcal{F}$ 是 $Y$ 上的层，定义为
$$(f_* \mathcal{F})(U) := \mathcal{F}(f^{-1}(U)) \quad \text{对开集 } U \subseteq Y.$$

**命题 1.1**。$f_*: \mathbf{Sh}(X) \to \mathbf{Sh}(Y)$ 是左正合函子。

### 1.2 高阶直接像

**定义 1.2（高阶直接像）**。由于 $\mathbf{Sh}(X)$ 有足够内射对象，$f_*$ 的右导出函子存在：
$$R^q f_* \mathcal{F} := H^q(f_* \mathcal{I}^\bullet),$$
其中 $\mathcal{F} \to \mathcal{I}^\bullet$ 为内射分解。

**定理 1.1（茎的计算）**。若 $f$ 为proper映射（或更一般地，在 $y$ 处满足适当条件），则
$$(R^q f_* \mathcal{F})_y \cong H^q(f^{-1}(y), \mathcal{F}|_{f^{-1}(y)}).$$

当 $f: E \to B$ 为纤维丛，纤维 $F$，则 $R^q f_* \underline{\mathbb{Z}}$ 是 $B$ 上的局部常值层，其茎为 $H^q(F, \mathbb{Z})$。

---

## 2. Leray谱序列的构造

### 2.1 复合函子的导出

**定理 2.1（Grothendieck谱序列）**。设 $F: \mathcal{A} \to \mathcal{B}$，$G: \mathcal{B} \to \mathcal{C}$ 为加性函子，$F$ 将内射对象映为 $G$-acyclic对象。则对每个 $A \in \mathcal{A}$，存在第一象限谱序列
$$E_2^{p,q} = (R^p G)(R^q F)(A) \Rightarrow R^{p+q}(G \circ F)(A).$$

**证明概要**：取 $A$ 的内射分解 $\mathcal{I}^\bullet$。则 $F(\mathcal{I}^\bullet)$ 是 $G$-acyclic复形。对 $F(\mathcal{I}^\bullet)$ 取Cartan-Eilenberg分解，得到双复形。一个边缘谱序列因 $G$-acyclic性而退化，给出 $R^n(G \circ F)(A)$；另一边缘谱序列给出 $E_2^{p,q} = (R^p G)(R^q F)(A)$。∎

### 2.2 Leray谱序列

取 $X \xrightarrow{f} Y \xrightarrow{g} \{\mathrm{pt}\}$，$G = g_* = \Gamma(Y, -)$（整体截面函子），$F = f_*$。则 $G \circ F = \Gamma(X, -)$。

**定理 2.2（Leray谱序列）**。对连续映射 $f: X \to Y$ 和 $X$ 上的层 $\mathcal{F}$，存在第一象限谱序列
$$E_2^{p,q} = H^p(Y, R^q f_* \mathcal{F}) \Rightarrow H^{p+q}(X, \mathcal{F}).$$

**验证Grothendieck条件**：$f_*$ 将内射层映为软层（soft sheaf）或松弛层（flabby sheaf），而软层/松弛层在 $Y$ 上是 $\Gamma(Y,-)$-acyclic的（对仿紧空间，如流形或CW复形）。

---

## 3. 退化条件与应用

### 3.1 纤维上同调消失

**命题 3.1**。若 $R^q f_* \mathcal{F} = 0$ 对所有 $q > 0$（即所有纤维的上同调在正维数消失），则Leray谱序列在 $E_2$ 退化，且
$$H^p(X, \mathcal{F}) \cong H^p(Y, f_* \mathcal{F}).$$

**例 3.1**。若 $f$ 有限（如覆叠映射的有限情形），则纤维为有限离散集，$H^q = 0$ 对 $q > 0$。故 $H^p(X, \mathcal{F}) \cong H^p(Y, f_* \mathcal{F})$。

### 3.2 底空间上同调消失

**命题 3.2**。若 $H^p(Y, \mathcal{G}) = 0$ 对所有 $p > 0$ 和适当的层 $\mathcal{G}$（如 $Y$ 为仿紧可缩空间），则
$$H^n(X, \mathcal{F}) \cong H^0(Y, R^n f_* \mathcal{F}) = \Gamma(Y, R^n f_* \mathcal{F}).$$

### 3.3 纤维丛的具体计算

设 $f: E \to B$ 为局部平凡纤维丛，纤维 $F$，$B$ 单连通（从而 $R^q f_* \underline{\mathbb{Z}}$ 为常值层 $\underline{H^q(F)}$）。

**例 3.2（Hopf纤维化 $S^3 \to S^2$，纤维 $S^1$）**。$H^p(S^2, R^q f_* \mathbb{Z})$：

- $q=0$：$R^0 f_* \mathbb{Z} = \mathbb{Z}$，$H^p(S^2, \mathbb{Z}) = \mathbb{Z}, 0, \mathbb{Z}$（$p=0,1,2$）。
- $q=1$：$R^1 f_* \mathbb{Z} = \mathbb{Z}$（因 $H^1(S^1) = \mathbb{Z}$），$H^p(S^2, \mathbb{Z})$ 同上。

$E_2$ 表：

| $q=1$ | $\mathbb{Z}$ | $0$ | $\mathbb{Z}$ |
| $q=0$ | $\mathbb{Z}$ | $0$ | $\mathbb{Z}$ |

总次数 $n = p+q$：$n=0$ 时 $E_2^{0,0} = \mathbb{Z}$；$n=1$ 时 $E_2^{1,0} = E_2^{0,1} = 0$；$n=2$ 时 $E_2^{2,0} = \mathbb{Z}$，$E_2^{1,1} = 0$，$E_2^{0,2} = 0$（因 $H^2(S^1)=0$）；$n=3$ 时 $E_2^{2,1} = \mathbb{Z}$。

由 $H^*(S^3, \mathbb{Z}) = (\mathbb{Z}, 0, 0, \mathbb{Z})$，微分 $d_2: E_2^{0,1} \to E_2^{2,0}$ 必须将 $\mathbb{Z} \to \mathbb{Z}$ 映为同构（以消去 $n=2$ 的额外 $\mathbb{Z}$），而 $d_2: E_2^{0,2} \to E_2^{2,1}$ 为零。最终 $E_\infty$ 给出 $H^3(S^3) = \mathbb{Z}$。这是Leray谱序列非平凡微分的经典例子。

---

## 4. 与已有文档的关联

- [12-谱序列基础](12-谱序列基础.md)：谱序列的一般理论与收敛性。
- [14-Grothendieck谱序列](14-Grothendieck谱序列.md)：Leray谱序列的母体理论。
- [05-层上同调基本定理](06-层上同调基本定理.md)：层上同调与内射分解。
- [04-层与结构层](../13-代数几何/04-层与结构层.md)：层论基础。

---

## 参考文献

1. J. Leray, "L'anneau spectral et l'anneau filtré d'homologie d'un espace localement compact et d'une application continue", *J. Math. Pures Appl.*, 29:1–139, 1950.
2. R. Godement, *Topologie Algébrique et Théorie des Faisceaux*, Hermann, 1958.
3. C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Univ. Press, 1994. (Ch. 5)
4. A. Borel, "Sur la cohomologie des espaces fibrés principaux et des espaces homogènes de groupes de Lie compacts", *Ann. of Math.*, 57:115–207, 1953.

---

**适用**：docs/15-同调代数/
