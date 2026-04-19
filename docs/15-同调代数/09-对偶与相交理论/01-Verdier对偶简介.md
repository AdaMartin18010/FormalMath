---
title: Verdier对偶简介
description: 系统介绍导出范畴中的Verdier对偶、反常层上同调、对偶复形与局部对偶性，建立Grothendieck对偶理论的同调代数框架。
msc_primary:
  - 18G80
msc_secondary:
  - 14F05
  - 32C38
  - 55U30
processed_at: '2026-04-20'
references:
  textbooks:
    - id: kashiwara_schapira
      type: textbook
      title: Sheaves on Manifolds
      authors:
        - Masaki Kashiwara
        - Pierre Schapira
      publisher: Springer
      year: 1990
      msc: 58A99
    - id: hartshorne_rd
      type: textbook
      title: Residues and Duality
      authors:
        - Robin Hartshorne
      publisher: Springer
      year: 1966
      msc: 14-02
---

# Verdier对偶简介

**导出范畴中的对偶 — 从Grothendieck到Verdier**

---

## 1. 动机：经典对偶的推广

### 1.1 Poincaré对偶

对闭定向 $n$-维流形 $M$，Poincaré对偶给出同构
$$H^k(M; \mathbb{Z}) \cong H_{n-k}(M; \mathbb{Z})$$
或系数 $\mathbb{R}$ 时
$$H^k(M; \mathbb{R}) \cong H^{n-k}(M; \mathbb{R})^*$$

### 1.2 Serre对偶

对光滑射影簇 $X$（维数 $n$）上的局部自由层 $E$，
$$H^i(X, E) \cong H^{n-i}(X, E^* \otimes \omega_X)^*$$
其中 $\omega_X = \Omega_X^n$ 为典则层。

**问题**：是否存在统一的对偶理论，将Poincaré对偶、Serre对偶及更一般的相对对偶纳入同一框架？

**答案**：Verdier对偶在导出范畴层面提供了这一统一。

---

## 2. 导出范畴与直接像

### 2.1 有界导出范畴

设 $X$ 为拓扑空间（或概形、解析空间），$\text{Sh}(X)$ 为Abel群层（或 $\mathcal{O}_X$-模层）范畴。其**有界导出范畴** $D^b(X)$ 由有界复形 $K^\bullet$（$K^i = 0$ 对 $|i| \gg 0$）模拟同构构造。

### 2.2 导出直接像

连续映射 $f: X \to Y$ 诱导左正合函子 $f_*: \text{Sh}(X) \to \text{Sh}(Y)$。其右导出函子
$$Rf_*: D^b(X) \to D^b(Y)$$
计算为 $Rf_* \mathcal{F}^\bullet = f_* \mathcal{I}^\bullet$，其中 $\mathcal{I}^\bullet$ 为内射消解。

类似地，有紧支集版本 $Rf_!: D^b(X) \to D^b(Y)$（当 $f$ 为局部紧空间间的真映射或适当定义时）。

---

## 3. Verdier对偶定理

### 3.1 对偶函子的存在性

**定理（Verdier对偶）**：设 $f: X \to Y$ 为局部紧空间间的连续映射。存在**右伴随**对偶函子
$$f^!: D^b(Y) \to D^b(X)$$
使得 $(Rf_!, f^!)$ 成为伴随对：
$$\text{Hom}_{D^b(Y)}(Rf_! \mathcal{F}^\bullet, \mathcal{G}^\bullet) \cong \text{Hom}_{D^b(X)}(\mathcal{F}^\bullet, f^! \mathcal{G}^\bullet)$$

特别地，当 $Y = \{\text{pt}\}$ 为一点，$a_X: X \to \{\text{pt}\}$，则
$$\mathbb{D}_X(\mathcal{F}^\bullet) = a_X^! \mathbb{Z} \otimes^L \mathcal{F}^\bullet$$
或对适当常数（dualizing complex），给出**对偶函子**
$$\mathbb{D}_X: D^b(X)^{\text{op}} \to D^b(X)$$

### 3.2 对偶复形

**定义**：$\omega_X^\bullet = a_X^! \mathbb{Z}$ 称为 $X$ 的**对偶复形**（dualizing complex）。

**定理**：对 $n$-维拓扑流形，$\omega_X^\bullet \cong \text{or}_X[n]$，即定向局部系（或常数层 $\mathbb{Z}$ 若可定向）平移 $n$ 位。

对复流形或光滑代数簇，对偶复形与典则层相关。

### 3.3 局部对偶性

**定理（局部Verdier对偶）**：对 $\mathcal{F}^\bullet, \mathcal{G}^\bullet \in D^b(X)$，
$$R\mathcal{H}om(\mathcal{F}^\bullet, \mathbb{D}_X(\mathcal{G}^\bullet)) \cong \mathbb{D}_X(\mathcal{F}^\bullet \otimes^L \mathcal{G}^\bullet)$$
取整体截面得上同调对偶。

---

## 4. 与经典对偶的关系

### 4.1 Poincaré对偶的重构

设 $M$ 为闭定向 $n$-维流形，$\mathbb{Z}_M$ 为常数层。则
$$\mathbb{D}_M(\mathbb{Z}_M) = \omega_M^\bullet = \mathbb{Z}_M[n]$$
由Verdier对偶，
$$R\Gamma(M, \mathbb{Z}_M)^* \cong R\Gamma(M, \mathbb{D}_M(\mathbb{Z}_M)) = R\Gamma(M, \mathbb{Z}_M[n])$$
取上同调得
$$H^k(M; \mathbb{Z})^* \cong H^{n-k}(M; \mathbb{Z})$$
即Poincaré对偶。

### 4.2 Serre对偶的重构

设 $X$ 为光滑射影 $n$-维簇，$E$ 为局部自由层。则
$$\mathbb{D}_X(E) = E^* \otimes \omega_X[n]$$
由Grothendieck对偶（代数几何版本），
$$R\Gamma(X, E)^* \cong R\Gamma(X, E^* \otimes \omega_X[n])$$
取上同调即得Serre对偶。

### 4.3 Alexander对偶

对紧集 $K \subset S^n$，Alexander对偶
$$\tilde{H}^k(K; \mathbb{Z}) \cong \tilde{H}_{n-k-1}(S^n \setminus K; \mathbb{Z})$$
可由相对Verdier对偶导出： inclusion $i: K \hookrightarrow S^n$ 的 exceptional pullback 与 exceptional pushforward 的伴随关系给出。

---

## 5. 反常层（Perverse Sheaves）

### 5.1 中介t-结构

在奇异代数簇或复解析空间上，通常的t-结构（$D^{\leq 0}$ = 上同调消灭于正次数）对奇异层不够精细。

**定义（中介t-结构）**：设 $X$ 为复代数簇（或解析空间），维数为 $n$。定义
$${}^p D^{\leq 0} = \{\mathcal{F}^\bullet \in D^b_c(X) \mid \dim \text{supp}\, H^j(\mathcal{F}^\bullet) \leq -j, \forall j\}$$
$${}^p D^{\geq 0} = \{\mathcal{F}^\bullet \in D^b_c(X) \mid \dim \text{supp}\, H^j(\mathbb{D}_X(\mathcal{F}^\bullet)) \leq -j, \forall j\}$$
这构成 $D^b_c(X)$（有界导出范畴，具紧支集与可构造上同调）上的t-结构。

### 5.2 反常层

**定义**：**反常层**是中介t-结构的心脏（heart）：
$$\text{Perv}(X) = {}^p D^{\leq 0} \cap {}^p D^{\geq 0}$$
即Abel范畴。

**性质**：
- $\text{Perv}(X)$ 是Noetherian与Artinian范畴；
- 简单对象由局部系与不可约闭子集的交上同调给出；
- Verdier对偶保持反常层范畴（即 $\mathbb{D}_X: \text{Perv}(X) \to \text{Perv}(X)$）。

**例1（光滑情形）**：若 $X$ 光滑，局部系 $L$（视为集中在度0的复形）是反常层。对奇异层，需要适当平移：若 $Z \subset X$ 余维 $c$，则 $i_* L[-c]$ 为反常层。

---

## 6. 应用：相交上同调

对奇异复射影簇 $X$，通常上同调 $H^*(X)$ 可能不满足Poincaré对偶（如锥形奇点）。

**定义（Goresky-MacPherson）**：$X$ 的**相交上同调**定义为
$$IH^k(X; \mathbb{Q}) = \mathbb{H}^k(X, IC_X^\bullet)$$
其中 $IC_X^\bullet$ 为**相交复形**，是特定的自对偶反常层（在光滑处约化为 $\mathbb{Q}_X[n]$）。

**定理**：对复射影簇 $X$，
1. **Poincaré对偶**：$IH^k(X) \cong IH^{2n-k}(X)^*$
2. **Lefschetz超平面定理**：对丰沛超平面截面 $Y \subset X$，$IH^k(X) \to IH^k(Y)$ 对 $k < n-1$ 为同构
3. **Hard Lefschetz**：$L^k: IH^{n-k}(X) \to IH^{n+k}(X)$ 为同构

这些性质对奇异上同调 $H^*$ 不成立，但对 $IH^*$ 成立，使 $IH^*$ 成为研究奇异代数簇的"正确"上同调理论。

---

## 7. 小结

Verdier对偶将Poincaré、Serre、Alexander等经典对偶统一于导出范畴的函子框架中。对偶复形 $a_X^! \mathbb{Z}$ 编码了空间的定向与奇异性信息，反常层与相交上同调则将这一理论推广到奇异代数簇，为Hodge理论、表示论与Langlands纲领提供了关键工具。Verdier对偶不仅是同调代数的杰作，更是现代代数几何与拓扑交汇的枢纽。
