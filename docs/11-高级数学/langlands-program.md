---
title: "Langlands纲领深度版 / Langlands Program (Advanced)"
msc_primary: "11R39"
msc_secondary: ["14D24", "22E50", "11F70"]
processed_at: '2026-04-05'
---
# Langlands纲领深度版 / Langlands Program (Advanced)

**主题编号**: B.11.ADV.01
**创建日期**: 2026年4月4日
**最后更新**: 2026年4月4日
**版本**: 深度版 (Advanced Version)

---

## 目录

- [Langlands纲领深度版 / Langlands Program (Advanced)](#langlands纲领深度版--langlands-program-advanced)
  - [目录](#目录)
  - [1. 深入概念 / Deep Concepts](#1-深入概念--deep-concepts)
    - [1.1 核心数学结构](#11-核心数学结构)
      - [1.1.1 自守表示的谱分解](#111-自守表示的谱分解)
      - [1.1.2 L群与对偶性](#112-l群与对偶性)
      - [1.1.3 局部-整体原理](#113-局部-整体原理)
    - [1.2 自守表示的精细理论](#12-自守表示的精细理论)
      - [1.2.1 Arthur-Selberg迹公式](#121-arthur-selberg迹公式)
      - [1.2.2 内窥理论 (Endoscopy)](#122-内窥理论-endoscopy)
    - [1.3 动机与L函数](#13-动机与l函数)
      - [1.3.1 标准L函数](#131-标准l函数)
      - [1.3.2 函子性原理](#132-函子性原理)
  - [2. 现代观点 / Modern Perspectives](#2-现代观点--modern-perspectives)
    - [2.1 范畴论视角](#21-范畴论视角)
      - [2.1.1 自守层的范畴](#211-自守层的范畴)
      - [2.1.2 Tannaka对偶性](#212-tannaka对偶性)
    - [2.2 几何Langlands对应](#22-几何langlands对应)
      - [2.2.1 几何对应陈述](#221-几何对应陈述)
      - [2.2.2 量子变形](#222-量子变形)
    - [2.3 p进Langlands纲领](#23-p进langlands纲领)
      - [2.3.1 p进局部对应](#231-p进局部对应)
      - [2.3.2 模p对应](#232-模p对应)
  - [3. 研究前沿 / Research Frontiers](#3-研究前沿--research-frontiers)
    - [3.1 几何Langlands的突破](#31-几何langlands的突破)
      - [3.1.1 Raskin等人的工作 (2024)](#311-raskin等人的工作-2024)
      - [3.1.2 导出/无穷范畴方法](#312-导出无穷范畴方法)
    - [3.2 函子性猜想进展](#32-函子性猜想进展)
      - [3.2.1 自守提升](#321-自守提升)
      - [3.2.2 基变换 (Base Change)](#322-基变换-base-change)
    - [3.3 与物理学的联系](#33-与物理学的联系)
      - [3.3.1 规范场论](#331-规范场论)
      - [3.3.2 共形场论](#332-共形场论)
  - [4. 参考文献 / References](#4-参考文献--references)
    - [经典文献](#经典文献)
    - [现代专著](#现代专著)
    - [关键论文](#关键论文)
    - [综述文章](#综述文章)

---

## 1. 深入概念 / Deep Concepts

### 1.1 核心数学结构

Langlands纲领是现代数学中最深远的统一理论之一，它建立了**数论**、**代数几何**、**表示论**和**调和分析**之间的深刻联系。

#### 1.1.1 自守表示的谱分解

设 $G$ 是定义在数域 $F$ 上的约化代数群，$\mathbb{A}_F$ 是 $F$ 的阿代尔环。自守形式空间可分解为：

$$L^2(G(F) \backslash G(\mathbb{A}_F)) = \bigoplus_{\pi} m(\pi) \cdot \pi$$

其中 $\pi$ 遍历 $G(\mathbb{A}_F)$ 的不可约酉表示，$m(\pi)$ 是重数。

**关键定理** (Langlands谱分解):

$$L^2(G(F) \backslash G(\mathbb{A}_F)) = L^2_{\text{disc}} \oplus \int_{\mathcal{X}} \pi_x d\mu(x)$$

这里 $L^2_{\text{disc}}$ 是离散谱，积分遍历连续谱。

#### 1.1.2 L群与对偶性

对于约化群 $G$，其**Langlands对偶群** $^L G$ 定义为半直积：

$$^L G = \hat{G} \rtimes \Gamma_F$$

其中：

- $\hat{G}$ 是 $G$ 的复对偶群
- $\Gamma_F = \text{Gal}(\bar{F}/F)$ 是绝对Galois群

**示例表**:

| 群 $G$ | 对偶群 $\hat{G}$ | 类型 |
|--------|------------------|------|
| $GL_n$ | $GL_n(\mathbb{C})$ | 一般线性 |
| $SL_n$ | $PGL_n(\mathbb{C})$ | 特殊线性 |
| $Sp_{2n}$ | $SO_{2n+1}(\mathbb{C})$ | 辛/正交 |
| $SO_{2n}$ | $SO_{2n}(\mathbb{C})$ | 正交 |
| $G_2$ | $G_2(\mathbb{C})$ | 例外 |

#### 1.1.3 局部-整体原理

**局部Langlands对应**: 对于局部域 $F_v$，存在对应：

$$\{\text{WD}_F \to {}^L G\}/\sim \quad \longleftrightarrow \quad \{\text{不可约光滑表示 of } G(F_v)\}$$

其中 $\text{WD}_F$ 是Weil-Deligne群。

**整体-局部相容性**: 对于整体表示 $\pi = \otimes_v' \pi_v$，局部成分 $\pi_v$ 与整体Galois表示的局部限制相容。

### 1.2 自守表示的精细理论

#### 1.2.1 Arthur-Selberg迹公式

迹公式是研究自守表示的强有力工具：

$$\sum_{\gamma \in G(F)/\sim} J_G(\gamma, f) = \sum_{\pi} m(\pi) \text{tr}(\pi(f))$$

**几何侧**: 轨道积分 $J_G(\gamma, f)$  。
**谱侧**: 自守表示的特征标和。

#### 1.2.2 内窥理论 (Endoscopy)

内窥理论处理Langlands函子性中的"非稳定"情形。

**基本引理** (Ngô Bảo Châu, 2008):
对于单位元的轨道积分，内窥群上的基本引理成立：

$$\mathbf{1}_{\mathfrak{g}(\mathcal{O})}^{\text{st}}(\gamma) = \sum_{\kappa} \Delta(\gamma, \gamma_\kappa) \mathbf{1}_{\mathfrak{h}_\kappa(\mathcal{O})}(\gamma_\kappa)$$

这一成果为Ngô Bảo Châu赢得了2010年Fields Medal。

### 1.3 动机与L函数

#### 1.3.1 标准L函数

对于自守表示 $\pi$ 和有限维表示 $r: {}^L G \to GL_N(\mathbb{C})$，定义L函数：

$$L(s, \pi, r) = \prod_v L_v(s, \pi_v, r_v)$$

**Euler乘积**: 在非Archimedean位 $v$，局部因子为：

$$L_v(s, \pi_v, r_v) = \frac{1}{\det(I - r_v(t_v) q_v^{-s})}$$

其中 $t_v \in {}^L G$ 是Satake参数。

#### 1.3.2 函子性原理

**Langlands函子性猜想**: 设 $G, H$ 为约化群，$\rho: {}^L H \to {}^L G$ 为L同态，则存在转移映射：

$$\mathcal{L}_\rho: \{\text{自守表示 of } H\} \to \{\text{自守表示 of } G\}$$

满足 $L(s, \pi, r \circ \rho) = L(s, \mathcal{L}_\rho(\pi), r)$。

---

## 2. 现代观点 / Modern Perspectives

### 2.1 范畴论视角

#### 2.1.1 自守层的范畴

在几何Langlands框架下，自守形式可理解为模空间上的层：

$$\mathcal{A}ut_G = \{\text{Hecke特征层 on } \text{Bun}_G\}$$

**Hecke对应**: 对于 $G$-主丛的模空间 $\text{Bun}_G$，Hecke对应定义为：

$$\text{Hecke}_\mu = \{(\mathcal{P}, \mathcal{P}', x) \mid \mathcal{P}' \subset \mathcal{P} \text{ with relative position } \mu\}$$

#### 2.1.2 Tannaka对偶性

Langlands对应可视为Tannaka对偶的算术类比：

$$\text{Rep}({}^L G) \quad \longleftrightarrow \quad \text{具有Hecke作用的层}$$

### 2.2 几何Langlands对应

#### 2.2.1 几何对应陈述

设 $X$ 是光滑射影曲线，$G$ 是约化群，$\hat{G}$ 是其Langlands对偶。

**几何Langlands对应**:

$$\mathcal{D}(\text{Bun}_G) \simeq \mathcal{D}(\text{LocSys}_{\hat{G}})$$

其中：

- $\text{Bun}_G$: $G$-主丛的模空间
- $\text{LocSys}_{\hat{G}}$: $\hat{G}$-局部系统的模空间
- $\mathcal{D}$: 导出范畴的D模

#### 2.2.2 量子变形

**量子几何Langlands** 引入参数 $k$（水平）：

$$\mathcal{D}_{k}(\text{Bun}_G) \simeq \mathcal{D}_{-\check{k}}(\text{Bun}_{\hat{G}})$$

其中 $\check{k}$ 是相对于Langlands对偶的水平。

### 2.3 p进Langlands纲领

#### 2.3.1 p进局部对应

对于p进域 $F$（$[F:\mathbb{Q}_p] < \infty$），p进Langlands研究连续表示：

$$\rho: G_F \to GL_n(\overline{\mathbb{Q}}_p)$$

**Breuil猜想**: 对于 $GL_2(\mathbb{Q}_p)$，存在对应：

$$\{\text{2维p进Galois表示}\} \longleftrightarrow \{\text{单位球上的p进Banach表示}\}$$

#### 2.3.2 模p对应

简化到模 $p$ 情形，考虑：

$$\bar{\rho}: G_F \to GL_n(\overline{\mathbb{F}}_p)$$

与光滑模 $p$ 表示的联系。

---

## 3. 研究前沿 / Research Frontiers

### 3.1 几何Langlands的突破

#### 3.1.1 Raskin等人的工作 (2024)

2024年末，Sam Raskin（耶鲁大学）与合作者发布了超过**900页**的手稿，证明了几何Langlands纲领的主要部分。

**核心结果**:

- 建立了Whittaker范畴与拟凝聚层范畴的等价
- 证明了全局范畴对应的兼容性
- 解决了多个长期存在的技术障碍

| 项目 | 详情 |
|------|------|
| 主要作者 | Sam Raskin (Yale), Dennis Gaitsgory, D. Arinkin 等 |
| 页数 | 900+ 页 |
| 核心方法 | 导出代数几何、无穷范畴论 |
| 影响 | 几何Langlands纲领的重大突破 |

#### 3.1.2 导出/无穷范畴方法

现代几何Langlands强烈依赖于：

- **导出代数几何**: 处理模空间的导出结构
- **无穷范畴论**: $(\infty,1)$-范畴提供正确的同伦论框架

$$\text{IndCoh}(\text{Bun}_G) \quad \text{vs} \quad \text{QCoh}(\text{Bun}_G)$$

### 3.2 函子性猜想进展

#### 3.2.1 自守提升

**Arthur分类** 对于经典群提供了自守表示的完整描述：

$$L^2_{\text{disc}}(G(F)\backslash G(\mathbb{A})) = \bigoplus_{\psi} \bigoplus_{\pi \in \Pi_\psi} m_\psi(\pi) \cdot \pi$$

其中 $\psi$ 是Arthur参数。

#### 3.2.2 基变换 (Base Change)

对于域扩张 $E/F$，基Change函子性建立了：

$$BC_{E/F}: \{\text{GL}_n(F)\text{的表示}\} \to \{\text{GL}_n(E)\text{的表示}\}$$

**应用**: 素数定理的逆定理、L函数的特殊值。

### 3.3 与物理学的联系

#### 3.3.1 规范场论

几何Langlands与**超对称规范场论**有深刻联系：

$$\mathcal{N}=4 \text{超Yang-Mills理论} \longleftrightarrow \text{几何Langlands对应}$$

**Kapustin-Witten (2006)**: 电磁对偶性与几何Langlands对应通过S-对偶联系。

#### 3.3.2 共形场论

顶点算子代数与自守表示的联系：

$$\text{WZW模型} \longleftrightarrow \text{Kac-Moody群的表示}$$

---

## 4. 参考文献 / References

### 经典文献

1. **Langlands, R.P.** (1970). *Problems in the Theory of Automorphic Forms*. Lecture Notes in Mathematics, Vol. 170, Springer.
   - Langlands纲领的奠基性论文

2. **Borel, A. & Wallach, N.** (1980). *Continuous Cohomology, Discrete Subgroups, and Representations of Reductive Groups*. Princeton University Press.
   - 连续上同调与自守形式的系统处理

3. **Arthur, J.** (1989). *Unipotent Automorphic Representations: Conjectures*. Astérisque 171-172.
   - Arthur猜想与内窥理论的框架

### 现代专著

1. **Frenkel, E.** (2007). *Langlands Correspondence for Loop Groups*. Cambridge University Press.
   - 环群Langlands对应的系统阐述

2. **Gaitsgory, D. & Lurie, J.** (2019). *Weil's Conjecture for Function Fields*. Annals of Mathematics Studies.
   - 函数域上的Weil猜想，使用无穷范畴方法

3. **Calegari, F. & Emerton, M.** (2022). *Completed Cohomology and p-adic Langlands*. In preparation.
   - p进Langlands的现代处理

### 关键论文

1. **Ngô, B.C.** (2010). *Le lemme fondamental pour les algèbres de Lie*. Publ. Math. IHES 111.
   - 基本引理的证明，Fields Medal工作

2. **Raskin, S. et al.** (2024). *Geometric Langlands Correspondence*. ArXiv preprint (900+ pages).
   - 几何Langlands纲领的最新突破

3. **Peter Scholze** (2018). *On the p-adic Langlands correspondence*. Proceedings ICM 2018.
   - p进Langlands的现代视角

### 综述文章

1. **Gelbart, S.** (1984). *An Elementary Introduction to the Langlands Program*. Bulletin AMS 10(2).
    - Langlands纲领的入门介绍

2. **Bernstein, J. & Gelbart, S.** (Eds.) (2003). *An Introduction to the Langlands Program*. Birkhäuser.
    - Langlands纲领各方向的综述文集

3. **Frenkel, E.** (2005). *Lectures on the Langlands Program and Conformal Field Theory*. Les Houches Lectures.
    - 共形场论与Langlands纲领的联系

---

**相关文档**:

- [朗兰兹纲领](./10-朗兰兹纲领.md) (标准版)
- [几何朗兰兹纲领](./12-几何朗兰兹纲领.md)
- [算术几何](./11-算术几何.md)
- [自守形式](./automorphic-forms.md)

**交叉引用**:

- [代数K理论](./08-代数K理论.md)
- [导出代数几何](./05-导出代数几何.md)
- [无穷范畴理论](./06-无穷范畴理论.md)
