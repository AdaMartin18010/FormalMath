---
title: "集合论 (Set Theory)"
msc_primary: 03

  - 03E30
msc_secondary: ['03E25', '03E35', '03E55', '03E60']
processed_at: '2026-04-05'
references:
  textbooks:
    - id: enderton_logic
      type: textbook
      title: A Mathematical Introduction to Logic
      authors:
      - Herbert B. Enderton
      publisher: Academic Press
      edition: 2nd
      year: 2001
      isbn: 978-0122384523
      msc: 03-01
      chapters: 
      url: ~
    - id: mendelson_logic
      type: textbook
      title: Introduction to Mathematical Logic
      authors:
      - Elliott Mendelson
      publisher: Chapman and Hall/CRC
      edition: 6th
      year: 2015
      isbn: 978-1482237725
      msc: 03-01
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

# 集合论 (Set Theory)

**最后更新**: 2026年4月5日  
**MSC分类**: 03E-XX (集合论), 涵盖基础公理、大基数、强制法等核心主题

---

## 1. 引言

集合论是现代数学的基础语言，由Georg Cantor在19世纪末创立。ZFC公理系统（Zermelo-Fraenkel with Choice）为几乎所有数学分支提供了严格的形式化框架。本模块从基础公理出发，深入探讨序数、基数、大基数层级以及哥德尔和Cohen的独立性证明。

---

## 2. ZFC公理系统

### 2.1 基础公理

**定义 2.1** (ZFC公理): ZFC包含以下九条公理：

**公理 1** (外延公理): 
$$\forall x \forall y (\forall z (z \in x \leftrightarrow z \in y) \rightarrow x = y)$$
两个集合相等当且仅当它们有相同的元素。

**公理 2** (空集公理): 
$$\exists x \forall y (y \notin x)$$
存在空集 $\emptyset$。

**公理 3** (配对公理): 
$$\forall x \forall y \exists z \forall w (w \in z \leftrightarrow w = x \lor w = y)$$
对任意两个集合，存在包含它们的双元集合 $\{x, y\}$。

**公理 4** (并集公理): 
$$\forall x \exists y \forall z (z \in y \leftrightarrow \exists w (w \in x \land z \in w))$$
对任意集合的集合，存在其并集。

**公理 5** (幂集公理): 
$$\forall x \exists y \forall z (z \in y \leftrightarrow z \subseteq x)$$
对任意集合，存在其所有子集构成的幂集 $\mathcal{P}(x)$。

**公理 6** (无穷公理): 
$$\exists x (\emptyset \in x \land \forall y (y \in x \rightarrow y \cup \{y\} \in x))$$
存在归纳集，由此构造自然数 $\mathbb{N}$。

**公理 7** (替换公理模式): 
对任意公式 $\varphi(x, y)$ 定义的函数关系，集合在函数下的像仍是集合。

**公理 8** (正则公理/基础公理): 
$$\forall x (x \neq \emptyset \rightarrow \exists y (y \in x \land y \cap x = \emptyset))$$
每个非空集合有 $\in$-极小元，防止集合属于自身。

**公理 9** (选择公理/AC): 
$$\forall x (\forall y, z \in x (y \cap z = \emptyset \land y \neq \emptyset) \rightarrow \exists c \forall y \in x, \exists! z \in y, z \in c)$$
或等价地：每个集合存在选择函数。

---

### 2.2 等价形式

**定理 2.1** (选择公理等价形式): 以下命题等价：
1. **选择公理** (AC)
2. **良序定理** (Zermelo): 每个集合可良序化
3. **Zorn引理**: 归纳偏序集有极大元
4. **Hausdorff极大原理**: 每个链含于某个极大链
5. **Tukey引理**: 有限特征的集族有极大元

---

## 3. 序数与基数

### 3.1 序数理论

**定义 3.1** (传递集): 集合 $x$ 是传递的，若 $y \in x \Rightarrow y \subseteq x$。

**定义 3.2** (序数): 序数是 $\in$-良序的传递集。

**定义 3.3** (后继与极限): 
- 后继序数: $\alpha + 1 = \alpha \cup \{\alpha\}$
- 极限序数: 非零且非后继的序数

**定理 3.1** (序数性质): 
1. 每个良序集序同构于唯一序数
2. 所有序数构成真类 $\mathbf{Ord}$
3. 序数类是良序的：$\alpha < \beta \Leftrightarrow \alpha \in \beta$

**定义 3.4** (超限递归): 定义在序数上的函数可通过递归定义：
- $F(0) = a$
- $F(\alpha + 1) = G(F(\alpha))$
- $F(\lambda) = \sup_{\alpha < \lambda} F(\alpha)$（$\lambda$ 极限序数）

---

### 3.2 基数理论

**定义 3.5** (等势): 集合 $A, B$ 等势，记 $|A| = |B|$，若存在双射 $f: A \to B$。

**定义 3.6** (基数): 基数是初始序数（不与更小的序数等势）。记 $\aleph_\alpha$ 为第 $\alpha$ 个无穷基数。

**定理 3.2** (Cantor-Bernstein-Schröder): 若 $|A| \leq |B|$ 且 $|B| \leq |A|$，则 $|A| = |B|$。

**定理 3.3** (Cantor定理): 对任意集合 $A$，有 $|A| < |\mathcal{P}(A)|$。

**定义 3.7** (共尾性与正则基数): 
- $cf(\kappa) = \min\{|X| : X \subseteq \kappa, \sup X = \kappa\}$
- 若 $cf(\kappa) = \kappa$，则称 $\kappa$ 为正则基数

**定理 3.4** (König定理): 对无穷基数 $\kappa$，有 $\kappa^{cf(\kappa)} > \kappa$。

---

## 4. 大基数层级

### 4.1 不可达基数

**定义 4.1** (不可达基数): 不可数正则极限基数 $\kappa$ 称为弱不可达基数；若还满足 $2^\lambda < \kappa$（$\lambda < \kappa$），则称为强不可达基数。

**定理 4.1**: ZFC不能证明不可达基数的存在性。

---

### 4.2 可测基数与更强假设

**定义 4.2** (可测基数): 不可数基数 $\kappa$ 是可测的，若其上存在非主 $\kappa$-完备超滤子。

**定义 4.3** (超紧基数): 基数 $\kappa$ 是 $\lambda$-超紧的，若存在初等嵌入 $j: V \to M$ 满足：
- $crit(j) = \kappa$
- $j(\kappa) > \lambda$
- $M^\lambda \subseteq M$

**大基数层级**:
```
ZFC + 不可达 ⊂ ZFC + 可测 ⊂ ZFC + 超紧 ⊂ ... ⊂ ZFC + 决定性公理
```

---

## 5. 独立性与强制法

### 5.1 哥德尔不完备性

**定理 5.1** (Gödel第一不完备定理): 任何包含皮亚诺算术的一致形式系统都存在不可判定的命题。

**定理 5.2** (Gödel第二不完备定理): 一致的形式系统不能证明自身的一致性。

---

### 5.2 连续统假设

**定义 5.1** (连续统假设/CH): $2^{\aleph_0} = \aleph_1$

**广义连续统假设 (GCH)**: 对所有无穷基数 $\kappa$，$2^\kappa = \kappa^+$。

**定理 5.3** (Gödel, 1938): 若ZFC一致，则ZFC + GCH一致（即GCH不能被ZFC否证）。

**定理 5.4** (Cohen, 1963): 若ZFC一致，则ZFC + $\neg$CH一致（即CH不能被ZFC证明）。

---

### 5.3 强制法基础

**定义 5.2** (偏序与稠密集): 强制偏序 $(P, \leq)$ 满足：
- $D \subseteq P$ 是稠密的，若 $\forall p \in P, \exists q \in D, q \leq p$
- 滤子 $G \subseteq P$ 是脱殊的，若与所有稠密集相交

**定理 5.5** (强制法基本定理): 设 $M$ 是ZFC的可数传递模型，$P \in M$ 是强制偏序，$G$ 是 $M$-脱殊滤子，则：
1. $M[G]$ 是ZFC的可数传递模型
2. $M \subseteq M[G]$ 且 $G \in M[G]$
3. 若 $N$ 是ZFC传递模型，$M \subseteq N$，$G \in N$，则 $M[G] \subseteq N$

---

## 6. 目录结构

```
docs/07-数理逻辑/01-集合论/
├── 00-README.md                    # 本文件
├── 01-基础概念.md                   # ZFC公理系统
├── 02-核心定理.md                   # 良序定理、选择公理
├── 03-序数理论.md                   # 超限归纳、序数运算
├── 04-基数理论.md                   # 基数运算、共尾性
├── 05-大基数.md                     # 不可达、可测、超紧基数
├── 06-实战问题.md                   # 独立性证明、强制法
└── 07-选择公理应用.md               # AC在数学中的应用
```

---

## 7. 学习路径

### 7.1 基础路径
**朴素集合论** → **ZFC公理** → **序数基数** → **选择公理** → **大基数**

### 7.2 高级路径
- **描述集合论**:  Polish空间上的可定义集合
- **内模型理论**:  可构成宇宙L
- **强迫法深入**:  迭代强迫、适当强迫

---

## 8. 核心定理索引

| 定理 | 领域 | 重要性 | 状态 |
|------|------|--------|------|
| Cantor定理 | 基数 | ⭐⭐⭐⭐⭐ | ZFC证明 |
| 良序定理 | 选择公理 | ⭐⭐⭐⭐⭐ | ZFC证明 |
| Gödel不完备定理 | 元数学 | ⭐⭐⭐⭐⭐ | 元定理 |
| Cohen独立性定理 | CH | ⭐⭐⭐⭐⭐ | 强制法 |
| König定理 | 基数运算 | ⭐⭐⭐⭐ | ZFC证明 |
| 大基数存在性 | 大基数 | ⭐⭐⭐⭐ | 不可证 |

---

**最后更新**: 2026年4月5日  
**维护者**: FormalMath项目组  
**质量等级**: ⭐⭐⭐⭐⭐ (研究级)
