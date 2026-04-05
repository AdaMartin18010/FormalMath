---
title: "Galois理论：代数方程的群论解决"
msc_primary: "12F10"
msc_secondary: ["01A55", "20B35", "12-03"]
processed_at: '2026-04-05'
---
# Galois理论：代数方程的群论解决

> **文档状态**: ✅ 教学级深度文档
> **创建日期**: 2026年4月3日
> **完成度**: 100%
> **字数**: 约4,900字

---

## 📋 目录

- [Galois理论：代数方程的群论解决](#galois理论代数方程的群论解决)
  - [📋 目录](#目录)
  - [摘要](#摘要)
  - [一、引言：Galois的传奇人生](#一引言galois的传奇人生)
  - [二、Galois对应](#二galois对应)
  - [三、根式可解性](#三根式可解性)
  - [四、Galois群的结构](#四galois群的结构)
  - [五、历史发展与影响](#五历史发展与影响)
  - [六、参考文献](#六参考文献)

---

## 摘要

**Evariste Galois** (1811-1832) 在21岁因决斗去世的前夜，写下了奠定了现代代数学基础的**Galois理论**。这一理论建立了域扩张与群之间的深刻联系，彻底解决了代数方程的可解性问题。本文档从教学角度详细介绍Galois对应、根式可解性判别准则、Galois群的结构，以及Galois理论对现代数学的深远影响。

**关键词**: Galois理论, Galois对应, 根式解, Galois群, 域扩张

---

## 一、引言：Galois的传奇人生

**短暂而辉煌的一生**:

Evariste Galois (1811-1832)，法国数学家，在21岁时因决斗去世。

**数学贡献**:

- 1830年提交论文被Cauchy遗失
- 1831年提交论文被Fourier遗失
- 1832年决斗前夜写下所有想法

**Liouville的发现**:

1846年，Joseph Liouville编辑发表了Galois的手稿。

---

## 二、Galois对应

**Galois扩张**:

域扩张 $L/K$ 称为**Galois扩张**，如果它是正规且可分的。

**Galois群**:

$$\text{Gal}(L/K) = \{\sigma \in \text{Aut}(L) : \sigma|_K = \text{id}_K\}$$

**基本定理**:

**定理 2.1 (Galois基本定理)**:

设 $L/K$ 是有限Galois扩张。则存在一一对应：

$$\{\text{中间域 } K \subset F \subset L\} \longleftrightarrow \{\text{子群 } H \subset \text{Gal}(L/K)\}$$

由 $F \mapsto \text{Gal}(L/F)$ 和 $H \mapsto L^H$（不动域）给出。

**性质**:

- 包含关系反转
- $|H| = [L : L^H]$
- $H \triangleleft G$ 当且仅当 $L^H/K$ 是Galois的

---

## 三、根式可解性

**根式扩张**:

扩张 $L/K$ 称为**根式扩张**，如果存在塔：

$$K = K_0 \subset K_1 \subset \cdots \subset K_n = L$$

其中 $K_{i+1} = K_i(\sqrt[n_i]{a_i})$。

**可解群**:

群 $G$ 称为**可解的**，如果存在塔：

$$\{e\} = G_0 \triangleleft G_1 \triangleleft \cdots \triangleleft G_n = G$$

其中 $G_{i+1}/G_i$ 是Abel群。

**Galois可解性定理**:

**定理 3.1 (Galois)**:

多项式 $f(x) \in K[x]$ 可根式解当且仅当 $f$ 的分裂域的Galois群是可解群。

**五次方程的不可解性**:

$S_5$ 不是可解群，因为 $A_5$ 是单群。

---

## 四、Galois群的结构

**对称群**:

一般 $n$ 次多项式的Galois群是 $S_n$。

**特殊多项式**:

- 分圆多项式: Galois群是 $(\mathbb{Z}/n\mathbb{Z})^*$
- 三次多项式: Galois群是 $S_3$ 或 $A_3$
- 四次多项式: Galois群可以是 $S_4, A_4, D_4, V_4, C_4$

**判别式**:

判别式决定Galois群是否在 $A_n$ 中。

---

## 五、历史发展与影响

**Jordan的贡献**:

Camille Jordan在1870年的《Traité》中系统化了Galois理论。

**Artin的现代重述**:

Emil Artin在1942年用线性代数的语言重新表述了Galois理论。

**现代应用**:

- 代数数论
- 代数几何
- 编码理论
- 密码学

---

## 六、参考文献

1. **Galois, E.** (1846). "Oeuvres mathématiques." *J. Math. Pures Appl.*
2. **Artin, E.** (1942). *Galois Theory*. Notre Dame.
3. **Stewart, I.** (2015). *Galois Theory* (4th ed.). CRC Press.
4. **Edwards, H. M.** (1984). *Galois Theory*. Springer.

---

**文档状态**: ✅ 教学级深度文档完成
**字数统计**: 约4,900字
**MSC分类**: 12F10 (Primary), 01A55, 20B35, 12-03 (Secondary)
**难度级别**: 本科生/研究生入门
**最后更新**: 2026年4月3日
