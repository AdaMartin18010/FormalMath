---
msc_primary: 00

  - 00A99
title: 23 Tannaka对偶
processed_at: '2026-04-05'
---
# 23 Tannaka对偶

﻿# 23-Tannaka对偶

---

**文档编号**: FM.L3.ALG.23  
**理论名称**: Tannaka对偶  
**MSC分类**: 18D10, 20G05  
**创建日期**: 2026年4月3日  
**版本**: 2.0

---

## 一、理论概述

### 1.1 理论定位

Tannaka对偶理论是代数学中一座连接群（或更一般的Hopf代数）与其表示范畴的桥梁。它起源于1939年Tadao Tannaka对紧致群表示的工作，后经Chevalley、Grothendieck、Saavedra Rivano、Deligne和Milne等人发展为现代形式。其核心思想是：一个代数群（或更一般的对称张量范畴）可以完全由其有限维表示范畴（配备遗忘纤维函子）所重构。这一理论是 motives 理论、Langlands纲领以及量子群理论的深层基础。

### 1.2 核心思想

经典Pontryagin对偶处理的是交换局部紧致群的对偶群。Tannaka对偶将其推广到非交换情形：不再是群到其对偶群的映射，而是**群到其表示范畴的等价**。更精确地说，对代数群 \(G\)，其表示范畴 \(\text{Rep}(G)\) 配备忘却函子 \(\omega: \text{Rep}(G) \to \text{Vec}\)（向量空间范畴），可以完全重构 \(G\)。用现代语言，这是**对称张量范畴的纤维函子分类定理**。

---

## 二、核心定义(L1)清单

### 定义 2.1（张量范畴）

**张量范畴**（或幺半范畴）是带有双函子 \(\otimes: \mathcal{C} \times \mathcal{C} \to \mathcal{C}\)（张量积）、单位对象 \(\mathbf{1}\)、结合约束 \(a_{X,Y,Z}: (X \otimes Y) \otimes Z \xrightarrow{\sim} X \otimes (Y \otimes Z)\) 和单位约束 \(l_X: \mathbf{1} \otimes X \xrightarrow{\sim} X\)、\(r_X: X \otimes \mathbf{1} \xrightarrow{\sim} X\) 的范畴，满足MacLane的pentagon公理和triangle公理。

### 定义 2.2（对称张量范畴）

张量范畴 \(\mathcal{C}\) 称为**对称的**，若配备自然同构 \(c_{X,Y}: X \otimes Y \xrightarrow{\sim} Y \otimes X\)（辫结构），满足 \(c_{Y,X} \circ c_{X,Y} = \text{id}_{X \otimes Y}\)（对称性）以及Hexagon公理。

### 定义 2.3（纤维函子）

设 \(\mathcal{C}\) 为域 \(k\) 上的张量范畴。**纤维函子**是指一个正合 \(k\)-线性张量函子 \(\omega: \mathcal{C} \to \text{Vec}_k\)，保持张量积、单位对象和对称约束。

### 定义 2.4（Tannaka对偶群/双代数）

设 \((\mathcal{C}, \omega)\) 为带有纤维函子的张量范畴。其**Tannaka对偶**定义为纤维函子的自同构群概形：

$$
\underline{\text{Aut}}^\otimes(\omega) = \text{Spec}(\text{End}(\omega)^{\text{cop}})
$$

或等价地，由 \(\omega\) 的"可表示性"所给出的仿射群概形。

---

## 三、支撑定理(L2)清单

### 定理 3.1（Tannaka重构定理，经典形式）

设 \(G\) 为代数闭域上的仿射群概形，\(\omega: \text{Rep}(G) \to \text{Vec}_k\) 为忘却纤维函子。则存在典范同构：

$$
G \xrightarrow{\sim} \underline{\text{Aut}}^\otimes(\omega)
$$

即 \(G\) 完全由其表示范畴（带纤维函子）所重构。

### 定理 3.2（Deligne-Milne定理，抽象形式）

设 \(\mathcal{C}\) 为域 \(k\) 上的**刚性的**对称张量范畴，且存在纤维函子 \(\omega: \mathcal{C} \to \text{Vec}_k\)。则 \(\mathcal{C}\) 等价于某个仿射群概形 \(G\) 的有限维表示范畴：

$$
\mathcal{C} \simeq \text{Rep}(G)
$$

其中 \(G = \underline{\text{Aut}}^\otimes(\omega)\)。

### 定理 3.3（Deligne定理，特征零情形）

设 \(k\) 为特征零的代数闭域，\(\mathcal{C}\) 为 \(k\) 上的对称张量范畴。若 \(\mathcal{C}\) 中每个对象的自同态代数的维数均为有限（即满足"有限增长条件"或"super-Tannakian"），则 \(\mathcal{C}\) 必等价于某个超群概形（super-group scheme）的表示范畴。

这一结果是 motives 理论与张量范畴 Galois 理论的基石。

### 定理 3.4（Nori's Tannaka定理）

Madhav Nori证明了：从代数簇的上同调理论出发，可以纯范畴地构造出一个 pro-代数群（即 motivic Galois 群），使得该群的上同调表示范畴精确捕捉原上同调理论的所有信息。这是 motives 理论中最强的Tannaka型结果之一。

---

## 四、理论结构图

```
Tannaka对偶理论
├── 经典Tannaka对偶（代数群 ↔ 表示范畴+纤维函子）
│   ├── 紧致群情形（Tannaka, 1939）
│   ├── 代数群情形（Chevalley, Hochschild-Mostow）
│   └── 超Tannakian范畴（Deligne, 2002）
├── 推广与变体
│   ├── Doplicher-Roberts定理（C*-代数与对称张量范畴）
│   ├── 量子群Tannaka对偶（RTF代数, Majid）
│   └── 非交换Tannaka对偶（weak Hopf代数, Hayashi）
└── 核心应用
    ├── Motivic Galois理论（Nori, Ayoub）
    ├── Langlands纲领中的Satake同构
    └── 共形场论中的模张量范畴
```

---

## 五、向L4前沿的开放问题

1. ** motives 的Tannaka实现**：是否存在一个"终极" motivic Galois 群，其表示范畴精确对应于所有Weil上同调理论的交？
2. **特征 \(p\) 的障碍**：在正特征情形，Tannaka重构面临 \(p\)-挠问题。是否存在统一的修正框架？
3. **高阶范畴化**：将Tannaka对偶推广到 \((\infty, 1)\)-范畴或导出范畴层面，与derived algebraic geometry的联系。
4. **物理中的Tannaka对偶**：量子场论中的对称性与缺陷范畴（category of defects）之间是否存在Tannaka型对偶？

---

**文档信息**
- **创建日期**: 2026年4月3日
- **状态**: 已完成扩充
