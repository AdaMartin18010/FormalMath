---
title: "Galois理论应用 - 深度版"
msc_primary: 12

  - 12F10
msc_secondary: ["12F12", "12G05", "11R32", "14G32"]
processed_at: '2026-04-05'
references:
  textbooks:
    - id: artin_algebra
      type: textbook
      title: Algebra
      authors:
      - Michael Artin
      publisher: Pearson
      edition: 2nd
      year: 2011
      isbn: 978-0132413770
      msc: 16-01
      chapters: 
      url: ~
    - id: strang_la
      type: textbook
      title: Introduction to Linear Algebra
      authors:
      - Gilbert Strang
      publisher: Wellesley-Cambridge Press
      edition: 5th
      year: 2016
      isbn: 978-0980232776
      msc: 15-01
      chapters: 
      url: ~
    - id: dummit_foote_aa
      type: textbook
      title: Abstract Algebra
      authors:
      - David S. Dummit
      - Richard M. Foote
      publisher: Wiley
      edition: 3rd
      year: 2003
      isbn: 978-0471433347
      msc: 13-01
      chapters: 
      url: ~
  databases:
    - id: nlab
      type: database
      name: nLab
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
      consulted_at: 2026-04-17
    - id: stacks_project
      type: database
      name: Stacks Project
      entry_url: "https://stacks.math.columbia.edu/tag/{tag}"
      consulted_at: 2026-04-17
    - id: zbmath
      type: database
      name: zbMATH Open
      entry_url: "https://zbmath.org/?q=an:{zb_id}"
      consulted_at: 2026-04-17
---

# Galois理论应用 - 深度版

> **"Galois理论是数学中最优美的理论之一，它将域扩张的层次结构与群的结构完美对应。"** —— 纪念Evariste Galois

---

## 📚 概述

Galois理论是代数学的皇冠明珠，它建立了域扩张与群之间的深刻对应。这一理论不仅解决了代数方程根式可解性的古典问题，还为现代代数学、代数数论和代数几何提供了基本工具。本文深入探讨Galois理论的核心定理及其重要应用。

---

## 🕰️ 历史发展与数学家理念

### 伽罗瓦的革命性遗产

**伽罗瓦数学理念**的核心贡献：

1. **群的概念**：首次认识到代数方程的对称群（伽罗瓦群）
2. **对应原理**：域子结构与群子结构的反序对应
3. **可解性判据**：将方程可解性问题转化为群的可解性问题

伽罗瓦在1830年左右写下这些思想时年仅18-19岁，其工作在他因决斗去世后才被Liouville理解和发表（1846年）。

### 格洛腾迪克的推广

**格洛腾迪克数学理念**将Galois理论纳入更一般的框架：

1. **étale基本群**：Galois群是空间基本群的代数类比
2. **Galois上同调**：研究Galois模的上同调理论
3. **Tannaka对偶**：通过表示范畴重构Galois群

### 现代发展

- **Artin的线性代数方法**：现代Galois理论的标准表述
- **Krull拓扑**：无限Galois扩张的拓扑群框架
- **Langlands纲领**：Galois表示与自守形式的深刻联系

---

## 🏗️ 核心概念与完整证明

### 1. Galois扩张的定义

**定义 10.1**（Galois扩张）
代数扩张$K/F$称为**Galois扩张**，如果满足以下等价条件之一：

1. $K$是$F$上某个可分多项式族的分裂域
2. $K/F$是正规且可分的扩张
3. $K^{Gal(K/F)} = F$（不动域等于基域）

**定义 10.2**（Galois群）
Galois扩张$K/F$的**Galois群**定义为：
$$Gal(K/F) = \{\sigma \in Aut(K) : \sigma|_F = id_F\}$$

### 2. Galois基本定理

**定理 10.1**（Galois基本定理）
设$K/F$是有限Galois扩张，$G = Gal(K/F)$。则：

1. 存在包含关系的反序一一对应：
$$\{\text{中间域 } E : F \subseteq E \subseteq K\} \longleftrightarrow \{\text{子群 } H \leq G\}$$

对应方式为$E \mapsto Gal(K/E)$，$H \mapsto K^H$。

1. **维数公式**：$[E : F] = [G : Gal(K/E)]$

2. **正规性对应**：$E/F$是正规扩张当且仅当$Gal(K/E) \trianglelefteq G$，此时：
$$Gal(E/F) \cong G / Gal(K/E)$$

**完整证明**：

**步骤1**：证明$E = K^{Gal(K/E)}$。

由定义，$E \subseteq K^{Gal(K/E)}$。

设$H = Gal(K/E)$。因$K/E$是Galois扩张（$K$是可分多项式在$F$上的分裂域，也是在$E$上的分裂域），由条件3：
$$K^{Gal(K/E)} = E$$

**步骤2**：证明$H = Gal(K/K^H)$对$H \leq G$。

显然$H \subseteq Gal(K/K^H)$。

由Artin定理：若$H$是$K$的有限自同构群，则$[K : K^H] = |H|$。

因此：
$$|Gal(K/K^H)| = [K : K^H] = |H|$$

故$H = Gal(K/K^H)$。

**步骤3**：证明对应是双射。

由步骤1和2，两个映射互为逆映射。

**步骤4**：证明反序性。

若$E_1 \subseteq E_2$，则$Gal(K/E_2) \subseteq Gal(K/E_1)$（固定$E_2$的自同构必然固定$E_1$）。

反之亦然。

**步骤5**：证明维数公式。

$$[K : E] = |Gal(K/E)|$$
（Galois扩张的基本性质）

因此：
$$[E : F] = \frac{[K : F]}{[K : E]} = \frac{|G|}{|Gal(K/E)|} = [G : Gal(K/E)]$$

**步骤6**：证明正规性对应。

($\Rightarrow$)：设$E/F$正规，$\sigma \in G$。对$\alpha \in E$，$\sigma(\alpha)$是$\min_F(\alpha)$的根。

因$E/F$正规，$\min_F(\alpha)$在$E$中分裂，故$\sigma(\alpha) \in E$。

因此$\sigma(E) = E$，即$\sigma Gal(K/E) \sigma^{-1} = Gal(K/E)$。

($\Leftarrow$)：设$Gal(K/E) \trianglelefteq G$。对$\alpha \in E$，$\sigma \in G$，$\sigma(\alpha)$被$\sigma Gal(K/E) \sigma^{-1} = Gal(K/E)$固定。

因此$\sigma(\alpha) \in K^{Gal(K/E)} = E$，即$E/F$正规。

**步骤7**：证明同构$Gal(E/F) \cong G/Gal(K/E)$。

限制映射$\rho: G \to Gal(E/F)$，$\sigma \mapsto \sigma|_E$。

- 满射：由$E/F$正规，任何$E$的$F$-嵌入可延拓到$K$
- 核：$\ker(\rho) = \{\sigma \in G : \sigma|_E = id\} = Gal(K/E)$

由同态基本定理：$G/Gal(K/E) \cong Gal(E/F)$。

**证毕**。

### 3. 根式可解性判据

**定义 10.3**（根式扩张）
扩张$K/F$称为**根式扩张**，如果存在塔：
$$F = F_0 \subseteq F_1 \subseteq \cdots \subseteq F_m = K$$
其中$F_{i+1} = F_i(\alpha_i)$，$\alpha_i^{n_i} \in F_i$对某个$n_i$。

**定理 10.2**（Galois可解性判据）
设$f(x) \in F[x]$是可分多项式，$K$是$f$在$F$上的分裂域。则$f(x) = 0$根式可解当且仅当$Gal(K/F)$是可解群。

**证明概要**：

**($\Rightarrow$)**：设$f$根式可解，$F = F_0 \subseteq \cdots \subseteq F_m = E$是根式塔，$K \subseteq E$。

通过添加单位根，可假设塔中仅含素数根扩张。

对每个素数$p$扩张$F_{i+1}/F_i$，Galois群是$p$阶循环群（Kummer理论）。

因此$Gal(E/F)$有循环因子的次正规列，是可解群。

$Gal(K/F)$是其商群，故可解。

**($\Leftarrow$)**：设$G = Gal(K/F)$可解，$|G| = n$。

设$\zeta$是本原$n$次单位根，$F' = F(\zeta)$，$K' = K(\zeta)$。

$Gal(K'/F')$是$G$的子群，可解。

利用可解群的导出列和Kummer理论，构造根式塔从$F'$到$K'$。

因此$f$根式可解。

**证毕**。

**推论**：一般五次方程不能用根式求解。

**证明**：$S_5$是不可解群（$[S_5, S_5] = A_5$非阿贝尔）。

一般五次多项式的Galois群是$S_5$，故不可根式求解。

---

## 🧮 应用示例

### 分圆扩张

**定理 10.3**：$Gal(\mathbb{Q}(\zeta_n)/\mathbb{Q}) \cong (\mathbb{Z}/n\mathbb{Z})^\times$

**证明**：$\sigma \in Gal(\mathbb{Q}(\zeta_n)/\mathbb{Q})$由$\sigma(\zeta_n) = \zeta_n^a$确定，其中$\gcd(a, n) = 1$。

---

## 📚 参考文献

1. **Artin, E.** (1942). *Galois Theory*. Notre Dame.
2. **Edwards, H. M.** (1984). *Galois Theory*. Springer.
3. **Lang, S.** (2002). *Algebra* (Revised 3rd ed.). Springer.
4. **Cox, D. A.** (2012). *Galois Theory* (2nd ed.). Wiley.

---

*文档版本: 1.0*
*创建日期: 2026年4月*
*最后更新: 2026年4月*
