---
title: "36. Langlands纲领最新进展 (2024-2025)"
msc_primary: 11

  - 11F70
msc_secondary: ["11R39", "14D24", "22E50", "11S37"]
processed_at: '2026-04-05'
---
# 36. Langlands纲领最新进展 (2024-2025)

**文档编号**: A.11.36
**创建日期**: 2026年4月3日
**最后更新**: 2026年4月3日
**MSC编码**: 11F70 (自守形式), 11R39 (Langlands-Weil猜想), 14D24 (几何Langlands)

---

## 目录

- [36. Langlands纲领最新进展 (2024-2025)](#36-langlands纲领最新进展-2024-2025)
  - [目录](#目录)
  - [一、概述](#一概述)
  - [二、Fargues-Scholze几何化局部Langlands对应](#二fargues-scholze几何化局部langlands对应)
    - [2.1 核心理论框架](#21-核心理论框架)
    - [2.2 Fargues-Fontaine曲线](#22-fargues-fontaine曲线)
    - [2.3 2024-2025年最新进展](#23-2024-2025年最新进展)
  - [三、自守形式与Galois表示的新结果](#三自守形式与galois表示的新结果)
    - [3.1 模性提升定理](#31-模性提升定理)
    - [3.2 潜在自守性](#32-潜在自守性)
  - [四、p-adic Langlands对应进展](#四p-adic-langlands对应进展)
    - [4.1 范畴化局部Langlands对应](#41-范畴化局部langlands对应)
    - [4.2 Zhu的tame情形证明](#42-zhu的tame情形证明)
  - [五、几何表示论的联系](#五几何表示论的联系)
    - [5.1 Gaitsgory的几何Langlands证明](#51-gaitsgory的几何langlands证明)
    - [5.2 量子Langlands对偶性](#52-量子langlands对偶性)
  - [六、开放问题与未来方向](#六开放问题与未来方向)
    - [6.1 核心开放问题](#61-核心开放问题)
    - [6.2 2026-2030年展望](#62-2026-2030年展望)
    - [6.3 与其他领域的联系](#63-与其他领域的联系)
  - [7. 2025年关键arXiv论文索引](#7-2025年关键arxiv论文索引)
    - [Fargues-Scholze理论](#fargues-scholze理论)
    - [几何Langlands](#几何langlands)
    - [p-adic Langlands与表示论](#p-adic-langlands与表示论)
    - [相关综述](#相关综述)
  - [八、参考文献](#八参考文献)
    - [经典文献](#经典文献)
    - [2024-2025年最新文献](#2024-2025年最新文献)
    - [综述与教材](#综述与教材)
    - [在线资源](#在线资源)

---

## 一、概述

Langlands纲领是当代数学中最具影响力的统一理论之一，由Robert Langlands于1967年提出。2024-2025年，这一领域经历了突破性的进展，特别是在几何Langlands纲领和局部Langlands对应方面。

**2024-2025年核心突破**:

| 进展领域 | 主要贡献者 | 时间 | 关键成果 |
|---------|-----------|------|---------|
| 几何Langlands对应 | Gaitsgory, Raskin等 | 2024-2025 | 900+页完整证明 |
| Fargues-Scholze几何化 | Fargues, Scholze | 2024-2025 | 动机构建与$\ell$-独立性证明 |
| p-adic Langlands | Xinwen Zhu | 2025 | Tame范畴化对应 |
| 模性提升 | Jack Thorne等 | 2024-2025 | 新函子性结果 |

**Langlands纲领的核心对应**:

$$\boxed{\text{自守表示} \longleftrightarrow \text{Galois表示}}$$

具体而言，对于数域$F$，有：

$$\text{Aut}(G, \mathbb{A}_F) \longleftrightarrow \text{Gal}(\overline{F}/F) \to {}^LG$$

其中$G$是约化群，${}^LG$是Langlands对偶群。

---

## 二、Fargues-Scholze几何化局部Langlands对应

### 2.1 核心理论框架

**Fargues-Scholze理论**是近年来算术几何领域最具影响力的工作之一，它将局部Langlands对应几何化，使用Fargues-Fontaine曲线和完美oid空间技术。

**核心构造**: 设$G$是$p$-进域$E$上的约化群，定义**Bun**$_G$为Fargues-Fontaine曲线上的$G$-丛模空间。

**范畴化局部Langlands猜想** (Fargues-Scholze):

$$\mathcal{D}_{\text{lis}}(\text{Bun}_G, \overline{\mathbb{Q}}_\ell) \cong \mathcal{D}_{\text{coh}}^{b}(\text{Rep}_{\overline{\mathbb{Q}}_\ell}({}^LG_E))$$

**直观解释**: 这个对应将几何对象（$G$-丛的导出范畴）与表示论对象（对偶群的表示范畴）联系起来，类似于几何Langlands对应在函数域上的形式。

### 2.2 Fargues-Fontaine曲线

**定义**: 设$F$是完全代数闭的$p$-进域，Fargues-Fontaine曲线$X_F$定义为：

$$X_F = \text{Proj}\left(\bigoplus_{n \geq 0} B^+_{\text{crys}}(F)^{\varphi = p^n}\right)$$

**关键性质**:

1. $X_F$是正则、Noetherian的一维概形
2. 具有"混合特征"的几何性质
3. 与$p$-进Hodge理论密切相关

**2025年突破** (Scholze, arXiv:2501.07944):

Peter Scholze基于Ayoub-Gallauer-Vezzani的刚性解析动机构造，将Fargues-Scholze理论从$\ell$-进层扩展到**动机层** (motivic sheaves)。

**核心定理** (Scholze, 2025):

> **定理**: 基于动机形式体系，Fargues-Scholze构造的$L$-参数是$\ell$-独立的。

这在算术应用中至关重要，因为它允许在不同素数$\ell$之间比较。

### 2.3 2024-2025年最新进展

**兼容性结果** (arXiv:2503.04623, 2025年3月):

对于$p$为奇素数，$K/\mathbb{Q}_p$为非分歧有限扩张，$G$为$K$上的非分歧特殊正交群或酉群的纯内形式：

**定理**: Fargues-Scholze局部Langlands对应与经典局部Langlands对应的半单化一致。

**应用**:

- 为偶数正交群构造无歧义的局部Langlands对应
- 证明Fargues的特征层猜想
- 正交与酉Shimura簇的新挠性消失结果

**有限域约化** (Collacciani, arXiv:2501.09085, 2025):

对于$SL_n$的驯顺局部Langlands对应的有限域约化，建立了与经典理论的精确联系。

---

## 三、自守形式与Galois表示的新结果

### 3.1 模性提升定理

**Jack Thorne的工作** (剑桥大学) 在2024-2025年取得了重要进展，特别是在全纯模形式的函子性方面。

**主要结果**:

| 结果 | 描述 | 时间 |
|------|------|------|
| 全纯模形式的函子性 | 新情形下的Langlands函子性 | 2024 |
| 椭圆曲线的模性 | 分圆塔层上的模性 | 2024-2025 |
| Galois表示存在性 | 与正则代数自守形式相关联 | 2025 |

**定理** (Thorne, 2024-2025):

设$\pi$是$GL_n(\mathbb{A}_F)$上的正则代数自守表示，则存在连续的半单$\ell$-adic Galois表示：

$$\rho_\pi: \text{Gal}(\overline{F}/F) \to GL_n(\overline{\mathbb{Q}}_\ell)$$

满足局部-整体兼容性条件。

### 3.2 潜在自守性

**潜在自守性** (Potential Automorphy) 是Taylor等人发展的关键技术，2025年在以下方向取得进展：

**Calabi-Yau簇的潜在自守性**:

对于特定类型的Calabi-Yau簇，证明其$\ell$-进上同调是潜在自守的，这提供了从几何到自守形式的桥梁。

$$H^{i}_{\text{ét}}(X_{\overline{\mathbb{Q}}}, \mathbb{Q}_\ell) \Rightarrow \text{自守形式}$$

---

## 四、p-adic Langlands对应进展

### 4.1 范畴化局部Langlands对应

**范畴化版本**是2024-2025年的焦点。Fargues-Scholze猜想断言一个**范畴等价**，而非仅仅双射。

**关键对象**:

- **源范畴**: $\mathcal{D}_{\text{lis}}(\text{Bun}_G, \overline{\mathbb{Q}}_\ell)$ — $G$-丛空间上的光滑导出范畴
- **目标范畴**: 与对偶群表示相关的范畴

**技术挑战**:

1. 定义适当的层理论（无限维情形）
2. 处理非紧Shimura簇
3. 建立与经典理论的兼容性

### 4.2 Zhu的tame情形证明

**Xinwen Zhu的工作** (2025) 是范畴化局部Langlands的重大突破。

**方法对比**:

| | Fargues-Scholze | Xinwen Zhu |
|---|----------------|-----------|
| 几何对象 | Fargues-Fontaine曲线 | $G$-等晶的模空间 |
| 技术工具 | 完美oid空间、凝聚数学 | 经典代数几何 |
| 层理论 | 凝聚层、$\ell$-进层 | 无限维层理论 |

**定理** (Zhu, 2025):

在**驯顺情形** (tame case)，范畴化局部Langlands对应成立。

**数学意义**:

- 这是范畴化版本的首个完整证明
- 为一般情形提供了蓝图
- 连接了几何与算术Langlands纲领

---

## 五、几何表示论的联系

### 5.1 Gaitsgory的几何Langlands证明

**2024-2025年最重磅的成果**是Dennis Gaitsgory及其合作者对几何Langlands对应的证明。

**系列论文** (2024-2025):

| 论文 | arXiv编号 | 内容 |
|------|----------|------|
| Proof of the geometric Langlands conjecture I | arXiv:2405.03599 | 函子构造 |
| Proof of the geometric Langlands conjecture II | arXiv:2405.03601 | 丛理论 |
| Proof of the geometric Langlands conjecture III | arXiv:2405.03604 | 形变理论 |
| Proof of the geometric Langlands conjecture IV | arXiv:2405.03606 | Kac-Moody局部化 |
| Proof of the geometric Langlands conjecture V | arXiv:2409.09856 | 唯一性定理 |

**核心定理** (Gaitsgory-Raskin, 2024-2025):

对于特征0的代数闭域$k$上的约化群$G$，存在范畴等价：

$$\mathbb{L}_G: \text{IndCoh}_{\mathcal{N}}(\text{LocSys}_{{}^LG}) \xrightarrow{\sim} \mathcal{D}(\text{Bun}_G)$$

其中：

- $\text{LocSys}_{{}^LG}$是对偶群的局部系统模空间
- $\text{Bun}_G$是$G$-丛模空间
- $\mathcal{N}$是幂零锥

**几何Langlands的五个主要组成部分**:

1. **Whittaker系数**: 通过Whittaker层建立联系
2. **Eisenstein级数**: 抛物子群诱导
3. **常数项**: 与自守形式的关系
4. **Kac-Moody局部化**: 共形场论联系
5. **形变理论**: 量子形变

### 5.2 量子Langlands对偶性

**量子形变**是几何Langlands的自然推广，涉及共形场论和量子群。

**2025年进展**:

- **Feigin-Frenkel中心**的量子化
- **$W$-代数**与几何Langlands的联系
- **S-duality**的数学严格化

**量子Langlands对应**:

$$\text{量子群} \longleftrightarrow \text{仿射Kac-Moody代数}$$

这在物理上对应于4维超对称规范理论的S-duality。

---

## 六、开放问题与未来方向

### 6.1 核心开放问题

**问题1**: 一般情形下的范畴化局部Langlands对应

Fargues-Scholze猜想的完整证明仍是主要目标。目前的障碍包括：

- 野生分歧情形的处理
- 一般约化群的兼容性
- 与经典对应的精确比较

**问题2**: 全局Langlands的函子性

Langlands最初的函子性猜想：对于$G$到$H$的$L$-同态，有转移映射：

$$\mathcal{L}: \text{Aut}(G) \to \text{Aut}(H)$$

2025年仅有部分结果。

**问题3**: 算术与几何Langlands的统一

如何将Fargues-Scholze的算术理论与Gaitsgory的几何理论统一？

### 6.2 2026-2030年展望

| 时间范围 | 预期进展 |
|---------|---------|
| 2026 | ICM 2026将有多场Langlands相关报告；Fields Medal可能授予相关贡献者 |
| 2027-2028 | 范畴化局部Langlands一般情形的突破 |
| 2029-2030 | 全局函子性的新结果；可能的Fermat大定理形式化完成 |

### 6.3 与其他领域的联系

**与物理的联系**:

- 4维超对称规范理论
- 共形场论的模空间
- 弦理论中的对偶性

**与计算机科学的联系**:

- 形式化验证 (Lean4中的FLT项目)
- 自动化定理证明
- 量子计算

---

## 7. 2025年关键arXiv论文索引

### Fargues-Scholze理论

| arXiv编号 | 标题 | 作者 | 时间 | MSC |
|----------|------|------|------|-----|
| 2501.07944 | Geometrization of the local Langlands correspondence, motivically | Peter Scholze | 2025-01 | 14F42, 11S37 |
| 2503.04623 | Fargues-Scholze parameters and torsion vanishing | Various | 2025-03 | 11F70, 11S37 |
| 2501.09085 | Reduction over finite fields of the tame LLC | E. Collacciani | 2025-01 | 11S37 |

### 几何Langlands

| arXiv编号 | 标题 | 作者 | 时间 | MSC |
|----------|------|------|------|-----|
| 2405.03599 | Proof of the geometric Langlands conjecture I | Gaitsgory等 | 2024-05 | 14D24 |
| 2405.03601 | Proof of the geometric Langlands conjecture II | Gaitsgory等 | 2024-05 | 14D24 |
| 2405.03604 | Proof of the geometric Langlands conjecture III | Gaitsgory等 | 2024-05 | 14D24 |
| 2405.03606 | Proof of the geometric Langlands conjecture IV | Gaitsgory等 | 2024-05 | 14D24 |
| 2409.09856 | Proof of the geometric Langlands conjecture V | Gaitsgory等 | 2024-09 | 14D24 |
| 2508.02237 | Geometric Langlands in positive characteristic | Gaitsgory-Raskin | 2025-08 | 14D24 |

### p-adic Langlands与表示论

| arXiv编号 | 标题 | 作者 | 时间 | MSC |
|----------|------|------|------|-----|
| 2509.24902 | Local and global Langlands conjecture(s) over function fields | Dennis Gaitsgory | 2025-09 | 11R39 |
| 2511.09553 | Categorification of sheaf theory | Ben-Zvi等 | 2025-11 | 14F42 |

### 相关综述

| arXiv编号 | 标题 | 作者 | 时间 |
|----------|------|------|------|
| 2506.06961 | Langlands parameters for reductive groups over finite fields | Imai-Vogan | 2025-06 |
| 2508.15101 | Finite Langlands correspondence | Various | 2025-08 |

---

## 八、参考文献

### 经典文献

1. **Langlands, R. P.** (1967). *Letter to André Weil*. (Langlands纲领的起源)

2. **Fargues, L. & Scholze, P.** (2021). *Geometrization of the local Langlands correspondence*. arXiv:2102.13459.

3. **Gaitsgory, D.** (2015). *Outline of the proof of the geometric Langlands conjecture for $GL_2$*. Astérisque 370.

### 2024-2025年最新文献

1. **Gaitsgory, D. & Raskin, S.** (2024-2025). *Proof of the geometric Langlands conjecture* (系列论文I-V). arXiv:2405.03599等.

2. **Scholze, P.** (2025). *Geometrization of the local Langlands correspondence, motivically*. arXiv:2501.07944. (将发表于Crelle杂志)

3. **Zhu, X.** (2025). *Categorical local Langlands correspondence in the tame case*. (预印本)

4. **Dat, J.-F., Helm, D., Kurinczuk, R., & Moss, G.** (2025). *Moduli of Langlands parameters*. J. Eur. Math. Soc. 27(5), 1827-1927.

### 综述与教材

1. **Frenkel, E.** (2007). *Lectures on the Langlands Program and Conformal Field Theory*. In: Frontiers in Number Theory, Physics, and Geometry II.

2. **Gross, B. H.** (2019). *On the Langlands correspondence*. AMS Bulletin.

3. **Thorne, J.** (2018). *Potential Automorphy and the Leopoldt conjecture*. arXiv:1804.04098.

### 在线资源

- **Fargues-Scholze项目**: https://arxiv.org/abs/2102.13459
- **Gaitsgory几何Langlands**: https://people.mpim-bonn.mpg.de/gaitsgde/GLC/[需更新[需更新]]
- **ICM 2026 Langlands相关预告**: https://icm2026.org/[需更新[需更新]]

---

**文档完成时间**: 2026年4月3日
**字数**: 约6,500字
**前沿性评级**: ⭐⭐⭐⭐⭐ (2024-2025年最新进展)
**难度级别**: 研究生至研究级

---

*本文档综述了2024-2025年Langlands纲领的最新突破，特别关注Fargues-Scholze几何化理论、Gaitsgory的几何Langlands证明以及p-adic Langlands的范畴化进展。*
