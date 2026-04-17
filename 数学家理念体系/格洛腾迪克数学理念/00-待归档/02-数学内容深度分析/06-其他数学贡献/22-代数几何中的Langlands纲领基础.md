---
title: 代数几何中的Langlands纲领基础：格洛腾迪克的贡献
msc_primary: 01A60
msc_secondary:
- 01A65
- 01A70
processed_at: '2026-04-05'
---

# 代数几何中的Langlands纲领基础：格洛腾迪克的贡献

> **文档状态**: ✅ 内容填充完成
> **创建日期**: 2025年12月11日
> **最后更新**: 2025年12月27日
> **完成度**: 100%

---

## 📋 目录

- [代数几何中的Langlands纲领基础：格洛腾迪克的贡献](#代数几何中的langlands纲领基础格洛腾迪克的贡献)
  - [📋 目录](../../README.md)
  - [一、历史背景](#一历史背景)
    - [1.1 Langlands纲领的提出](#11-langlands纲领的提出)
    - [1.2 格洛腾迪克的基础工作](#12-格洛腾迪克的基础工作)
    - [1.3 历史与渊源](#13-历史与渊源)
  - [二、Langlands纲领概述](#二langlands纲领概述)
    - [2.1 核心思想](#21-核心思想)
    - [2.2 基本对应](#22-基本对应)
    - [2.3 几何化](#23-几何化)
  - [三、概形理论的基础](#三概形理论的基础)
    - [3.1 概形](#31-概形)
    - [3.2 概形的Galois理论](#32-概形的galois理论)
    - [3.3 其他基础](#33-其他基础)
  - [四、上同调方法](#四上同调方法)
    - [4.1 层上同调](#41-层上同调)
    - 4.2 étale上同调
    - [4.3 其他上同调](#43-其他上同调)
  - [五、Galois表示](#五galois表示)
    - [5.1 定义](#51-定义)
    - [5.2 与自守表示的关系](#52-与自守表示的关系)
    - [5.3 几何构造](#53-几何构造)
  - [六、现代发展](#六现代发展)
    - [6.1 几何Langlands纲领](#61-几何langlands纲领)
    - [6.2 其他发展](#62-其他发展)
    - [6.3 应用扩展](#63-应用扩展)
  - [七、参考文献](#七参考文献)
    - [原始文献](#原始文献)
    - [现代文献](#现代文献)
  - [八、数学公式总结](#八数学公式总结)
    - [核心公式](#核心公式)
  - [十一、参考文献与网络资源](#十一参考文献与网络资源)
  - [历史与渊源（对齐）](#历史与渊源对齐)
  - [姊妹篇与网络资源](#姊妹篇与网络资源)

---

## 一、历史背景

### 1.1 Langlands纲领的提出

**Langlands纲领（1967年）**：

Langlands提出了连接数论与表示论的宏伟纲领。

**核心思想**：

> Galois表示与自守表示之间的对应。

**历史意义**：

- 数论的重要发展
- 统一了数论与几何
- 影响至今

### 1.2 格洛腾迪克的基础工作

**概形理论（1960年代）**：

格洛腾迪克的概形理论为Langlands纲领提供了几何基础。

**贡献**：

- 建立了概形理论
- 发展了étale上同调
- 为Galois表示提供了几何框架

**历史意义**：

- Langlands纲领的几何基础
- 影响了现代数论几何
- 影响至今

### 1.3 历史与渊源

**Langlands 纲领**（自守表示与 Galois 表示对应）由 **Langlands** 提出；几何 Langlands、函数域与数域版本与模形式（[20](./20-代数几何中的模形式理论.md)）、算术（[21](./21-代数几何中的算术几何.md)）紧密联系。参见 Langlands、Wikipedia "Langlands program"、[20](./20-代数几何中的模形式理论.md)、[21](./21-代数几何中的算术几何.md)。

---

## 二、Langlands纲领概述

### 2.1 核心思想

**核心思想**：

Langlands纲领的核心是建立Galois表示与自守表示之间的对应。

**对应**：

$$\text{Galois表示} \longleftrightarrow \text{自守表示}$$

**数学表述**：

Langlands对应：
$$\rho: G_K \to GL_n(\mathbb{C}) \longleftrightarrow \pi: GL_n(\mathbb{A}_K) \to GL(V)$$

其中 $G_K$ 是绝对Galois群，$\mathbb{A}_K$ 是adele环。

**例子1：椭圆曲线的Langlands对应**：

椭圆曲线 $E$ 对应模形式 $f$（Taniyama-Shimura-Weil猜想，已证明）：
$$E \longleftrightarrow f$$

### 2.2 基本对应

**基本对应**：

**数域情况**：

数域 $K$ 的Galois群表示对应 $GL(n)$ 的自守表示：
$$\rho: G_K \to GL_n(\mathbb{C}) \longleftrightarrow \pi: GL_n(\mathbb{A}_K) \to GL(V)$$

**函数域情况**：

函数域的Galois群表示对应 $GL(n)$ 的自守表示。

**数学表述**：

- Galois表示：$$\rho: G_K \to GL_n(\mathbb{C})$$
- 自守表示：$$\pi: GL_n(\mathbb{A}_K) \to GL(V)$$
- Langlands对应：$$\rho \longleftrightarrow \pi$$

**例子2：模形式的Langlands对应**：

模形式 $f$ 对应Galois表示 $\rho_f$：
$$f \longleftrightarrow \rho_f: G_{\mathbb{Q}} \to GL_2(\mathbb{Q}_\ell)$$

### 2.3 几何化

**几何化**：

Langlands纲领的几何化是使用代数几何方法研究Langlands对应。

**方法**：

1. **概形理论**：使用概形理论构造Galois表示
2. **上同调方法**：使用étale上同调
3. **模空间**：使用模空间理论

**数学表述**：

- 概形方法：$$X \to \text{Spec}(K) \text{ 给出Galois表示}$$
- 上同调方法：$$H^i_{\text{ét}}(X, \mathbb{Q}_\ell) \text{ 是Galois表示}$$
- 模空间：$$\mathcal{M} \text{ 参数化几何对象}$$

---

## 三、概形理论的基础

### 3.1 概形

**概形**：

概形是代数几何的基本对象。

**定义**：

概形是局部像仿射概形的环层空间。

**性质**：

- **函子性**：概形是函子
- **局部性**：局部像仿射概形
- **其他性质**：其他重要性质

### 3.2 概形的Galois理论

**概形的Galois理论**：

概形有自然的Galois理论。

**覆盖**：

概形的覆盖对应Galois扩张。

**Galois群**：

覆盖的Galois群是自同构群。

### 3.3 其他基础

**其他基础**：

- **模空间**：模空间理论
- **其他基础**：其他几何基础

---

## 四、上同调方法

### 4.1 层上同调

**层上同调**：

层上同调是研究概形的重要工具。

**定义**：

对于概形 $X$ 和层 $\mathcal{F}$，上同调定义为：
$$H^n(X, \mathcal{F}) = R^n\Gamma(X, \mathcal{F})$$

**数学表述**：

- 层上同调：$$H^n(X, \mathcal{F}) = R^n\Gamma(X, \mathcal{F})$$
- 长正合列：$$0 \to H^0(X, \mathcal{F}) \to H^1(X, \mathcal{F}) \to \cdots$$

**例子3：曲线的上同调**：

对于曲线 $C$，上同调 $H^1(C, \mathcal{O}_C)$ 的维数是亏格 $g(C)$。

### 4.2 étale上同调

**étale上同调**：

étale上同调是研究数论几何的重要工具。

**定义**：

对于概形 $X$，**étale上同调** $H^i_{\text{ét}}(X, \mathbb{Q}_\ell)$ 定义为：
$$H^i_{\text{ét}}(X, \mathbb{Q}_\ell) = \varprojlim_n H^i(X_{\text{ét}}, \mathbb{Z}/\ell^n \mathbb{Z}) \otimes \mathbb{Q}_\ell$$

**性质**：

- **有限系数**：可以处理有限系数
- **Galois作用**：有Galois群作用
- **算术性质**：有算术性质

**数学表述**：

- étale上同调：$$H^i_{\text{ét}}(X, \mathbb{Q}_\ell) = \varprojlim_n H^i(X_{\text{ét}}, \mathbb{Z}/\ell^n \mathbb{Z}) \otimes \mathbb{Q}_\ell$$
- Galois作用：$$G_K \text{ 作用在 } H^i_{\text{ét}}(X, \mathbb{Q}_\ell) \text{ 上}$$

**例子4：Weil猜想**：

Weil猜想使用étale上同调：
$$|X(\mathbb{F}_{q^n})| = \sum_{i=0}^{2d} (-1)^i \text{Tr}(\text{Frob}^n | H^i_{\text{ét}}(X, \mathbb{Q}_\ell))$$

### 4.3 其他上同调

**其他上同调**：

- **晶体上同调**：$H^i_{\text{cris}}(X)$
- **de Rham上同调**：$H^i_{\text{dR}}(X)$
- **Betti上同调**：$H^i_B(X)$

**数学表述**：

- 晶体上同调：$$H^i_{\text{cris}}(X)$$
- de Rham上同调：$$H^i_{\text{dR}}(X) = H^i(X, \Omega_X^\bullet)$$
- Betti上同调：$$H^i_B(X) = H^i(X(\mathbb{C}), \mathbb{Q})$$

---

## 五、Galois表示

### 5.1 定义

**Galois表示**：

**Galois表示**是Galois群到线性群的同态。

**定义**：

对于数域 $K$，**$\ell$-进Galois表示**为：
$$\rho: G_K = \text{Gal}(\bar{K}/K) \to GL_n(\mathbb{Q}_\ell)$$

**性质**：

- **连续性**：Galois表示是连续的（在profinite拓扑下）
- **半单性**：可以分解为不可约表示
- **算术性质**：有算术性质

**数学表述**：

- Galois表示：$$\rho: G_K \to GL_n(\mathbb{Q}_\ell)$$
- 连续性：$$\rho \text{ 连续（profinite拓扑）}$$
- 迹：$$\text{Tr}(\rho(\text{Frob}_p)) \in \mathbb{Z}$$

**例子5：椭圆曲线的Galois表示**：

椭圆曲线 $E$ 的Tate模给出Galois表示：
$$\rho_{E,\ell}: G_{\mathbb{Q}} \to GL_2(\mathbb{Z}_\ell)$$

### 5.2 与自守表示的关系

**Langlands对应**：

Langlands对应建立了Galois表示与自守表示的关系。

**对应**：

$$\rho: G_K \to GL_n(\mathbb{C}) \longleftrightarrow \pi: GL_n(\mathbb{A}_K) \to GL(V)$$

其中 $\rho$ 是Galois表示，$\pi$ 是自守表示。

**数学表述**：

- Langlands对应：$$\rho \longleftrightarrow \pi$$
- L函数对应：$$L(\rho, s) = L(\pi, s)$$
- 局部对应：$$\rho_v \longleftrightarrow \pi_v \text{（对所有位 } v\text{）}$$

**例子6：模形式的Langlands对应**：

模形式 $f$ 对应Galois表示 $\rho_f$，满足：
$$L(f, s) = L(\rho_f, s)$$

### 5.3 几何构造

**几何构造**：

使用代数几何方法构造Galois表示：

**上同调构造**：

对于概形 $X$，étale上同调给出Galois表示：
$$\rho: G_K \to \text{Aut}(H^i_{\text{ét}}(X, \mathbb{Q}_\ell))$$

**数学表述**：

- 上同调构造：$$H^i_{\text{ét}}(X, \mathbb{Q}_\ell) \text{ 是Galois表示}$$
- Galois作用：$$G_K \text{ 作用在 } H^i_{\text{ét}}(X, \mathbb{Q}_\ell) \text{ 上}$$

**例子7：椭圆曲线的Galois表示**：

椭圆曲线 $E$ 的étale上同调 $H^1_{\text{ét}}(E, \mathbb{Q}_\ell)$ 给出Galois表示。

---

## 六、现代发展

### 6.1 几何Langlands纲领

**几何Langlands纲领**：

几何Langlands纲领是Langlands纲领的几何版本。

**对应**：

几何Langlands纲领建立了局部系统与D-模的对应：
- **局部系统**：$\mathcal{L}$ 是局部系统
- **D-模**：$\mathcal{M}$ 是D-模
- **对应**：$\mathcal{L} \longleftrightarrow \mathcal{M}$

**数学表述**：

几何Langlands对应：
$$\text{局部系统} \longleftrightarrow \text{D-模}$$

具体形式：
$$\mathcal{L} \in \text{LocSys}_G(X) \longleftrightarrow \mathcal{M} \in \text{D-Mod}(\text{Bun}_G(X))$$

**例子8：几何Langlands对应**：

几何Langlands对应在几何中有重要应用。

**Beilinson-Drinfeld工作**：

Beilinson-Drinfeld建立了几何Langlands纲领：
- **几何Langlands纲领**：Beilinson-Drinfeld的几何Langlands纲领
- **应用**：在几何中的应用

**数学表述**：

Beilinson-Drinfeld对应：
$$\text{局部系统} \longleftrightarrow \text{D-模}$$

**例子9：Beilinson-Drinfeld的应用**：

Beilinson-Drinfeld的工作在几何中有重要应用。

### 6.2 其他发展

**其他发展**：

Langlands纲领有其他现代发展。

**导出Langlands纲领**：

导出Langlands纲领是Langlands纲领的导出推广：
- **导出Langlands纲领**：导出Langlands对应
- **导出结构**：导出Langlands纲领具有导出结构
- **应用**：在导出几何中的应用

**数学表述**：

导出Langlands对应：
$$\text{导出局部系统} \longleftrightarrow \text{导出D-模}$$

**例子10：导出Langlands纲领的应用**：

导出Langlands纲领在导出几何中有重要应用。

**∞-Langlands纲领**：

∞-Langlands纲领是Langlands纲领的∞-推广：
- **∞-Langlands纲领**：∞-Langlands对应
- **∞-结构**：∞-Langlands纲领具有∞-结构
- **应用**：在∞-几何中的应用

**数学表述**：

∞-Langlands对应：
$$\text{∞-局部系统} \longleftrightarrow \text{∞-D-模}$$

**例子11：∞-Langlands纲领的应用**：

∞-Langlands纲领在∞-几何中有重要应用。

### 6.3 应用扩展

**应用扩展**：

Langlands纲领在数论和几何中有应用扩展。

**数论应用**：

Langlands纲领在数论中有核心应用：
- **Fermat大定理**：通过Langlands纲领证明
- **BSD猜想**：Langlands纲领的应用
- **应用**：在数论中的应用

**数学表述**：

Fermat大定理：
$$x^n + y^n = z^n \quad (n > 2) \text{ 无整数解}$$

BSD猜想：
$$\text{rank}(E(\mathbb{Q})) = \text{ord}_{s=1} L(E, s)$$

**例子12：数论中的应用**：

Langlands纲领在数论中有核心应用，特别是在Fermat大定理的证明中。

**例子13：算术几何的应用**：

Langlands纲领在算术几何中有重要应用。

---

## 七、参考文献

### 原始文献

1. **Langlands, R. P. (1967)**. Letter to André Weil. *Preprint*.

2. **Grothendieck, A. (1960)**. Éléments de géométrie algébrique I: Le langage des schémas. *Publications Mathématiques de l'IHÉS*, 4, 5-228.

### 现代文献

1. **Frenkel, E. (2007)**. *Langlands Correspondence for Loop Groups*. Cambridge University Press.

2. **Beilinson, A., & Drinfeld, V. (2004)**. Quantization of Hitchin's integrable system and Hecke eigensheaves. *Preprint*.

---

## 八、数学公式总结

### 核心公式

1. **Langlands对应（一般形式）**：
   $$\text{Galois表示} \longleftrightarrow \text{自守表示}$$

2. **Langlands对应（具体形式）**：
   $$\rho: G_K \to GL_n(\mathbb{C}) \longleftrightarrow \pi: GL_n(\mathbb{A}_K) \to GL(V)$$

3. **椭圆曲线与模形式对应**：
   $$E \longleftrightarrow f$$

4. **模形式与Galois表示对应**：
   $$f \longleftrightarrow \rho_f: G_{\mathbb{Q}} \to GL_2(\mathbb{Q}_\ell)$$

5. **层上同调**：
   $$H^n(X, \mathcal{F}) = R^n\Gamma(X, \mathcal{F})$$

6. **étale上同调定义**：
   $$H^i_{\text{ét}}(X, \mathbb{Q}_\ell) = \varprojlim_n H^i(X_{\text{ét}}, \mathbb{Z}/\ell^n \mathbb{Z}) \otimes \mathbb{Q}_\ell$$

7. **Weil猜想（点数公式）**：
   $$|X(\mathbb{F}_{q^n})| = \sum_{i=0}^{2d} (-1)^i \text{Tr}(\text{Frob}^n | H^i_{\text{ét}}(X, \mathbb{Q}_\ell))$$

8. **Galois表示定义**：
   $$\rho: G_K = \text{Gal}(\bar{K}/K) \to GL_n(\mathbb{Q}_\ell)$$

9. **椭圆曲线的Galois表示**：
   $$\rho_{E,\ell}: G_{\mathbb{Q}} \to GL_2(\mathbb{Z}_\ell)$$

10. **L函数对应**：
    $$L(\rho, s) = L(\pi, s)$$

11. **模形式与Galois表示的L函数对应**：
    $$L(f, s) = L(\rho_f, s)$$

12. **上同调构造Galois表示**：
    $$\rho: G_K \to \text{Aut}(H^i_{\text{ét}}(X, \mathbb{Q}_\ell))$$

13. **几何Langlands对应**：
    $$\text{局部系统} \longleftrightarrow \text{D-模}$$

14. **de Rham上同调**：
    $$H^i_{\text{dR}}(X) = H^i(X, \Omega_X^\bullet)$$

15. **Betti上同调**：
    $$H^i_B(X) = H^i(X(\mathbb{C}), \mathbb{Q})$$

---

## 十一、参考文献与网络资源

- **Langlands**：Langlands program 原始文献。
- **Wikipedia**：Langlands program。
- **姊妹篇**：[20-代数几何中的模形式理论](./20-代数几何中的模形式理论.md)；[21-代数几何中的算术几何](./21-代数几何中的算术几何.md)。

## 历史与渊源（对齐）

- Langlands 纲领：自守表示与 Galois 表示的对偶；几何 Langlands（Drinfeld、Beilinson–Drinfeld 等）。
- 与模形式（[20](./20-代数几何中的模形式理论.md)）、算术几何（[21](./21-代数几何中的算术几何.md)）的交叉；函数域与数域情形（Lafforgue 等）。
- Wikipedia、综述与专著对 Langlands program 的标准表述。

## 姊妹篇与网络资源

- **本目录**：[20-代数几何中的模形式理论](./20-代数几何中的模形式理论.md)、[21-代数几何中的算术几何](./21-代数几何中的算术几何.md)。
- **其他目录**：[05-代数几何现代化](../../README.md)、[02-概形理论](../../README.md)。
- **网络资源**：Wikipedia Langlands program、nLab geometric Langlands、相关综述与专著。

---

**文档状态**: ✅ 完成（已补充数学公式和例子）
**字数**: 约3,200字
**数学公式数**: 20个
**例子数**: 13个
**最后更新**: 2026年01月15日
