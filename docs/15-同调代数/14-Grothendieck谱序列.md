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

Grothendieck谱序列是同调代数中最一般的谱序列构造，它回答了一个基本问题：给定两个加性函子的复合 $G \circ F$，如何从各自的导出函子 $L_p G$ 和 $L_q F$（或右导出情形）来计算复合函子的导出函子 $L_n(G \circ F)$？

Grothendieck在1957年的Tôhoku论文中建立了这一理论，它不仅统一了此前已知的Leray谱序列、Lyndon-Hochschild-Serre谱序列等经典结果，更为后来的代数几何和拓扑学提供了系统工具。当 $F$ 将投射（或内射）对象映为 $G$-acyclic对象时，Grothendieck谱序列存在并收敛到目标群。

本教程严格陈述Grothendieck谱序列定理，推导其经典应用，并通过具体的双复形构造展示谱序列的收敛机制。

---

## 1. 基本设定与假设

设 $\mathcal{A}, \mathcal{B}, \mathcal{C}$ 为Abel范畴，$\mathcal{A}, \mathcal{B}$ 有足够投射对象（或对偶地，有足够内射对象）。设 $F: \mathcal{A} \to \mathcal{B}$，$G: \mathcal{B} \to \mathcal{C}$ 为右正合加性函子。

**关键假设**：$F$ 将投射对象映为 $G$-acyclic对象，即对 $\mathcal{A}$ 中任意投射对象 $P$，$L_q G(FP) = 0$ 对所有 $q > 0$。

---

## 2. Grothendieck谱序列定理

**定理 2.1（Grothendieck, 1957）**。在上述假设下，对每个对象 $A \in \mathcal{A}$，存在第一象限谱序列
$$E_{p,q}^2 = (L_p G)(L_q F)(A) \Rightarrow L_{p+q}(G \circ F)(A).$$

**构造概要**：

1. 取 $A$ 的投射分解 $P_\bullet \to A$。
2. $F(P_\bullet)$ 是 $\mathcal{B}$ 中的复形。由假设，$H_q(F(P_\bullet)) = L_q F(A)$，且每个 $F(P_n)$ 是 $G$-acyclic的。
3. 对复形 $F(P_\bullet)$ 取 **Cartan-Eilenberg分解**：即对每个 $F(P_n)$，取 $G$-acyclic分解（可用投射分解，因 $G$-acyclic对象包含投射对象），构造双复形 $Q_{\bullet,\bullet}$。
4. 对双复形应用两个谱序列：
   - **第一谱序列**（垂直方向）：$E'^1_{p,q} = L_q G(F(P_p))$。因 $F(P_p)$ 为 $G$-acyclic，$E'^1_{p,q} = 0$ 对 $q > 0$，$E'^1_{p,0} = G(F(P_p))$。故第一谱序列退化为全复形 $G(F(P_\bullet))$ 的同调，即 $L_n(G \circ F)(A)$。
   - **第二谱序列**（水平方向）：$E''^1_{p,q} = H_p^{\mathrm{hor}}(Q_{\bullet,q})$。在 $E^2$ 页，$E''^2_{p,q} = (L_p G)(H_q(F(P_\bullet))) = (L_p G)(L_q F)(A)$。

两个谱序列收敛到同一全复形同调，即给出Grothendieck谱序列。∎

---

## 3. 经典应用

### 3.1 Leray谱序列

设 $f: X \to Y$ 为拓扑空间间的连续映射，$\Gamma_Y: \mathbf{Sh}(Y) \to \mathbf{Ab}$ 为整体截面函子。则 $\Gamma_X = \Gamma_Y \circ f_*$。

- $F = f_*: \mathbf{Sh}(X) \to \mathbf{Sh}(Y)$，右正合。
- $G = \Gamma_Y: \mathbf{Sh}(Y) \to \mathbf{Ab}$，左正合。

**验证假设**：$\mathbf{Sh}(X)$ 的内射对象为松弛层（flabby sheaf）。$f_*$ 将松弛层映为松弛层（因 $(f_*\mathcal{F})(U) = \mathcal{F}(f^{-1}(U))$），而松弛层是 $\Gamma_Y$-acyclic的。故假设满足。

**Grothendieck谱序列**：
$$E_2^{p,q} = H^p(Y, R^q f_* \mathcal{F}) \Rightarrow H^{p+q}(X, \mathcal{F}).$$
此即 **Leray谱序列**。

### 3.2 Hochschild-Serre谱序列

设 $1 \to N \to G \to Q \to 1$ 为群扩张，$M$ 为 $G$-模。

- $F = (-)^N: G\text{-Mod} \to Q\text{-Mod}$（$N$-不变量函子），左正合。
- $G = (-)^Q: Q\text{-Mod} \to \mathbf{Ab}$（$Q$-不变量函子），左正合。

复合 $G \circ F = (-)^G$。$F$ 将内射 $G$-模映为内射 $Q$-模（因 $F$ 有精确左伴随 $-\otimes_{\mathbb{Z}Q} \mathbb{Z}G$），而内射模是 $G$-acyclic的。故假设满足。

**Grothendieck谱序列**：
$$E_2^{p,q} = H^p(Q, H^q(N, M)) \Rightarrow H^{p+q}(G, M).$$
此即 **Lyndon-Hochschild-Serre谱序列**，是计算群扩张上同调的核心工具。

### 3.3 局部上同调谱序列

设 $(R, \mathfrak{m})$ 为Noether局部环，$M$ 为 $R$-模。局部上同调 $H^i_{\mathfrak{m}}(M)$ 是 $\Gamma_{\mathfrak{m}}(-)$ 的右导出函子，$\Gamma_{\mathfrak{m}}(M) = \{m \in M : \mathfrak{m}^k m = 0 \text{ 对某 } k\}$。

Grothendieck谱序列在此框架下导出局部上同调与Ext的关系：对有限生成 $M$，
$$H^i_{\mathfrak{m}}(M) \cong \varinjlim_n \operatorname{Ext}^i_R(R/\mathfrak{m}^n, M).$$

---

## 4. 退化情形

### 4.1 $F$ 正合

若 $F$ 正合，则 $L_q F = 0$ 对 $q > 0$。谱序列在 $E^2$ 退化：仅有 $q=0$ 列非零，$E^2_{p,0} = L_p G(FA)$，直接给出
$$L_n(G \circ F)(A) \cong L_n G(FA).$$

### 4.2 $G$ 正合

若 $G$ 正合，则 $L_p G = 0$ 对 $p > 0$。谱序列退化到 $p=0$ 行：
$$L_n(G \circ F)(A) \cong G(L_n F(A)).$$

---

## 5. 具体例子：群上同调的计算

设 $G = \mathbb{Z}/2\mathbb{Z} \times \mathbb{Z}/2\mathbb{Z}$，$M = \mathbb{Z}/2\mathbb{Z}$（平凡模）。通过分解 $G = Q \times N$（$Q = N = \mathbb{Z}/2$），用Hochschild-Serre：
$$E_2^{p,q} = H^p(\mathbb{Z}/2, H^q(\mathbb{Z}/2, \mathbb{Z}/2)) \Rightarrow H^{p+q}(G, \mathbb{Z}/2).$$

已知 $H^q(\mathbb{Z}/2, \mathbb{Z}/2) = \mathbb{Z}/2$ 对所有 $q \geq 0$（由周期上同调）。故
$$E_2^{p,q} = H^p(\mathbb{Z}/2, \mathbb{Z}/2) = \mathbb{Z}/2 \quad \forall p, q \geq 0.$$

$E_2$ 页为全 $\mathbb{Z}/2$ 网格。微分 $d_2: E_2^{p,q} \to E_2^{p+2,q-1}$。由已知结果 $H^*(G, \mathbb{Z}/2) = H^*(\mathbb{R}P^\infty \times \mathbb{R}P^\infty, \mathbb{Z}/2) = (\mathbb{Z}/2)[x,y]$（两个1次元的多项式环），$\dim H^n(G) = n+1$。

谱序列的微分必须消去多余生成元，最终给出正确的维数。这展示了Grothendieck谱序列在即使简单例子中的计算威力。

---

## 6. 与已有文档的关联

- [12-谱序列基础](12-谱序列基础.md)：谱序列的一般理论、收敛性与微分。
- [13-Leray谱序列](13-Leray谱序列.md)：Grothendieck谱序列在层论中的具体实现。
- [17-群上同调](17-群上同调.md)：Hochschild-Serre谱序列与群扩张上同调。
- [07-左导出函子Ext](07-左导出函子Ext.md)：导出函子的基本理论。

---

## 参考文献

1. A. Grothendieck, "Sur quelques points d'algèbre homologique", *Tôhoku Math. J.*, 9:119–221, 1957.
2. C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Univ. Press, 1994. (Ch. 5)
3. H. Cartan, S. Eilenberg, *Homological Algebra*, Princeton Univ. Press, 1956. (Ch. XVI, XVII)
4. J. L. Verdier, "Des catégories dérivées des catégories abéliennes", *Astérisque*, 239, 1996.

---

**适用**：docs/15-同调代数/
