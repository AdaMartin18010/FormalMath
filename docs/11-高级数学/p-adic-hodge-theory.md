---
title: "p进Hodge理论深度版 / p-adic Hodge Theory (Advanced)"
msc_primary: "14F30"
msc_secondary: ["14F20", "14G22", "11G25"]
processed_at: '2026-04-05'
---
# p进Hodge理论深度版 / p-adic Hodge Theory (Advanced)

**主题编号**: B.11.ADV.04  
**创建日期**: 2026年4月4日  
**最后更新**: 2026年4月4日  
**版本**: 深度版 (Advanced Version)

---

## 目录

- [1. 深入概念 / Deep Concepts](#1-深入概念--deep-concepts)
  - [1.1 p进周期环](#11-p进周期环)
  - [1.2 比较定理](#12-比较定理)
  - [1.3 (phi, Gamma)-模](#13-phi-gamma-模)
- [2. 现代观点 / Modern Perspectives](#2-现代观点--modern-perspectives)
  - [2.1 相对p进Hodge理论](#21-相对p进hodge理论)
  - [2.2 完美胚空间与p进Hodge理论](#22-完美胚空间与p进hodge理论)
  - [2.3 无穷范畴视角](#23-无穷范畴视角)
- [3. 研究前沿 / Research Frontiers](#3-研究前沿--research-frontiers)
  - [3.1 p进Simpson对应](#31-p进simpson对应)
  - [3.2 黎曼-Hilbert对应](#32-黎曼-hilbert对应)
  - [3.3 与Langlands纲领的联系](#33-与langlands纲领的联系)
- [4. 参考文献 / References](#4-参考文献--references)

---

## 1. 深入概念 / Deep Concepts

### 1.1 p进周期环

#### 1.1.1 Fontaine周期环

p进Hodge理论的核心是**周期环**的构造。设 $K$ 是p进域，$\mathbb{C}_K = \widehat{\overline{K}}$。

**基本环**:

- **$\mathbb{B}_{\text{dR}}$**: de Rham周期环
- **$\mathbb{B}_{\text{cris}}$**: 晶体周期环
- **$\mathbb{B}_{\text{st}}$**: 半稳定周期环

**de Rham周期环的构造**:

$$\mathbb{B}_{\text{dR}}^+ = \varprojlim_n W(R)[1/p]/(\ker(\theta)[1/p])^n$$

其中 $R = \varprojlim_{x \mapsto x^p} \mathcal{O}_{\mathbb{C}_K}/p$，$\theta: W(R) \to \mathcal{O}_{\mathbb{C}_K}$ 是标准投影。

#### 1.1.2 环的性质

| 环 | Frobenius | 单值性 |  filtration |
|-----|-----------|--------|-------------|
| $\mathbb{B}_{\text{dR}}$ | 否 | 否 | 是 |
| $\mathbb{B}_{\text{cris}}$ | 是 | 否 | 是 |
| $\mathbb{B}_{\text{st}}$ | 是 | 是 | 是 |

**定理** (Fontaine): 
$\mathbb{B}_{\text{dR}}$ 是离散赋值域，其剩余域为 $\mathbb{C}_K$。

### 1.2 比较定理

#### 1.2.1 de Rham比较定理

设 $X$ 是 $K$ 上的光滑真概形。

**定理** (Fontaine, Tsuji, Faltings, Niziol): 
存在自然的 $G_K$-等变同构：

$$H^i_{\text{ét}}(X_{\bar{K}}, \mathbb{Q}_p) \otimes_{\mathbb{Q}_p} \mathbb{B}_{\text{dR}} \cong H^i_{\text{dR}}(X/K) \otimes_K \mathbb{B}_{\text{dR}}$$

且此同构保持 filtration。

#### 1.2.2 晶体比较定理

设 $X$ 具有好约化，$\mathcal{X}$ 是其模型。

**定理**: 
存在自然的同构：

$$H^i_{\text{ét}}(X_{\bar{K}}, \mathbb{Q}_p) \otimes_{\mathbb{Q}_p} \mathbb{B}_{\text{cris}} \cong H^i_{\text{cris}}(\mathcal{X}_k/W(k)) \otimes_{W(k)} \mathbb{B}_{\text{cris}}$$

且此同构与Frobenius相容。

#### 1.2.3 半稳定比较定理

对于半稳定约化的情形：

**定理** (Tsuji, Faltings): 
存在自然的同构：

$$H^i_{\text{ét}}(X_{\bar{K}}, \mathbb{Q}_p) \otimes_{\mathbb{Q}_p} \mathbb{B}_{\text{st}} \cong H^i_{\text{log-cris}}(\mathcal{X}) \otimes_{K_0} \mathbb{B}_{\text{st}}$$

且此同构与 $\varphi$, $N$ 相容。

### 1.3 (phi, Gamma)-模

#### 1.3.1 定义与构造

**定义**: 一个 $(\varphi, \Gamma)$-模是有限自由的 $\mathbb{B}_K$-模 $D$，带有：

- **Frobenius**: $\varphi$-半线性自同态 $\varphi_D: D \to D$
- **Galois作用**: 连续的 $\Gamma$-作用，与 $\varphi_D$ 交换

其中 $\mathbb{B}_K$ 是Robba环或相关环。

#### 1.3.2 与p进表示的等价

**定理** (Fontaine, Cherbonnier-Colmez, Kedlaya): 
存在范畴等价：

$$\{\text{p进表示 of } G_K\} \longleftrightarrow \{\text{etale } (\varphi, \Gamma)\text{-模}\}$$

这是研究p进Galois表示的强有力工具。

#### 1.3.3 扩展与上同调

**Herr复形**: 计算 $(\varphi, \Gamma)$-模的上同调：

$$C^\bullet(D) = [D \xrightarrow{(\varphi-1, \gamma-1)} D \oplus D \xrightarrow{(\gamma-1, 1-\varphi)} D]$$

---

## 2. 现代观点 / Modern Perspectives

### 2.1 相对p进Hodge理论

#### 2.1.1 动机与背景

传统的p进Hodge理论处理单点情形。相对版本处理态射 $f: X \to Y$。

**挑战**: 纤维变化时的比较同构的相容性。

#### 2.1.2 Scholze的方法

**定理** (Scholze): 
对于光滑态射 $f: X \to Y$ 的适当刚性空间，存在相对比较同构。

**关键工具**: 
- 完美胚空间
- pro-etale拓扑
- 几乎数学

#### 2.1.3 应用

- 对族上同调的研究
- p进deformation理论
- 与p进Langlands的联系

### 2.2 完美胚空间与p进Hodge理论

#### 2.2.1 完美胚提升

**定理** (Scholze): 
设 $R$ 是完美胚环，则：

$$H^i_{\text{ét}}(\text{Spa}(R[1/p], R^+), \mathbb{F}_p) \otimes \mathbb{B}_{\text{dR}} \cong H^i_{\text{dR}}$$

#### 2.2.2 几乎纯性

**定理** (Almost Purity): 
对于完美胚空间的有限etale覆盖，在几乎意义下仍保持etale性。

这是p进Hodge理论革命性的进展。

### 2.3 无穷范畴视角

#### 2.3.1 导出p进Hodge理论

使用导出代数几何的语言：

$$\mathcal{D}(X_{\text{proét}}) \quad \text{vs} \quad \mathcal{D}(X_{\text{dR}})$$

#### 2.3.2 滤过与谱序列

Hodge-de Rham谱序列：

$$E_1^{p,q} = H^q(X, \Omega^p) \Rightarrow H^{p+q}_{\text{dR}}(X)$$

在p进情形下的类似结构。

---

## 3. 研究前沿 / Research Frontiers

### 3.1 p进Simpson对应

#### 3.1.1 经典Simpson对应回顾

对于紧Kaehler流形 $X$：

$$\{\text{向量丛 with flat connection}\} \longleftrightarrow \{\text{Higgs bundle with } \theta \wedge \theta = 0\}$$

#### 3.1.2 p进Simpson对应

**定理** (Faltings, Tsuji, Scholze, Liu-Zhu): 
对于p进域 $K$ 上的光滑簇 $X$：

$$\{\text{表示 of } \pi_1^{\text{ét}}(X_{\bar{K}})\} \longleftrightarrow \{\text{Higgs bundles on } X\}$$

**关键差异**: p进对应依赖于**高度**的选取。

### 3.2 黎曼-Hilbert对应

#### 3.2.1 经典黎曼-Hilbert

$$\{\text{正则全纯平坦联络}\} \cong \{\text{局部系统}\}$$

#### 3.2.2 p进黎曼-Hilbert

**构造** (Diao-Lan-Liu-Zhu): 
对于光滑刚性空间：

$$RH: \{\text{p进局部系统}\} \to \{\text{具有联络的向量丛}\}$$

**特征**: 涉及**对数联络**和**monodromy**。

### 3.3 与Langlands纲领的联系

#### 3.3.1 p进Langlands对应

p进Hodge理论提供了p进Langlands对应的工具：

$$\{\text{p进Galois表示}\} \longleftrightarrow \{\text{p进自守表示}\}$$

#### 3.3.2 完美胚空间的几何化

Scholze的局部Shimura簇理论使用完美胚空间：

$$\mathcal{M}_{(G,b,\mu)} \to \text{Spa}(\breve{E})$$

其中 $G$ 是p进群，$b$ 是 $\sigma$-共轭类，$\mu$ 是余权。

---

## 4. 参考文献 / References

### 经典文献

1. **Fontaine, J-M.** (1982). *Formes differentielles et modules de Tate des varietes abeliennes sur les corps locaux*. Inventiones Math.
   
2. **Faltings, G.** (1988). *p-adic Hodge Theory*. Journal AMS.
   
3. **Tsuji, T.** (1999). *p-adic etale cohomology and crystalline cohomology in the semi-stable reduction case*. Inventiones Math.

### 现代突破

4. **Scholze, P.** (2012). *Perfectoid Spaces*. Publ. Math. IHES.
   
5. **Scholze, P.** (2013). *p-adic Hodge theory for rigid-analytic varieties*. Forum Math. Pi.
   
6. **Kedlaya, K. & Liu, R.** (2015). *Relative p-adic Hodge theory: Foundations*. Astérisque.

### 前沿研究

7. **Liu, R. & Zhu, X.** (2017). *Rigidity and a Riemann-Hilbert correspondence for p-adic local systems*. Inventiones Math.
   
8. **Diao, H., Lan, K-W., Liu, R. & Zhu, X.** (2019). *Logarithmic Riemann-Hilbert correspondences for rigid varieties*. ArXiv.
   
9. **Anschütz, J. & Le Bras, A-C.** (2020). *Prismatic Dieudonne theory*. ArXiv.

### 综述文章

10. **Brinon, O. & Conrad, B.** (2009). *CMI Summer School notes on p-adic Hodge Theory*.
    
11. **Morrow, M.** (2019). *The Fargues-Fontaine curve and p-adic Hodge theory*. Proceedings ICM.
    
12. **Fargues, L. & Fontaine, J-M.** (2018). *Courbes et fibres vectoriels en theorie de Hodge p-adique*. Astérisque.

---

**相关文档**:

- [完美胚空间](./perfectoid-spaces.md)
- [算术几何深度版](./arithmetic-geometry.md)
- [Langlands纲领深度版](./langlands-program.md)
