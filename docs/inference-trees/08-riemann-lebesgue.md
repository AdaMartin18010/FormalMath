---
msc_primary: 00A99
msc_secondary:
- 00A99
title: 黎曼积分 → 勒贝格积分推理树
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# 黎曼积分 → 勒贝格积分推理树

## 概述
本推理树展示从黎曼积分出发，通过可测集和可测函数的概念，最终建立勒贝格积分理论的完整推理链。

```mermaid
graph TD
    subgraph 黎曼积分
        A1[分割定义] --> A2[Darb上和/下和]
        A2 --> A3[黎曼可积条件]
        A3 --> A4[上积分=下积分]
        A4 --> A5[不连续点为零测集]
    end
    
    subgraph 测度论基础
        B1[外测度定义] --> B2[Caratheodory条件]
        B2 --> B3[Lebesgue可测集]
        B3 --> B4[σ-代数结构]
        B4 --> B5[测度性质]
    end
    
    subgraph 可测函数
        B3 --> C1[可测函数定义]
        C1 --> C2[简单函数逼近]
        C2 --> C3[简单函数积分]
    end
    
    subgraph 勒贝格积分
        C3 --> D1[非负可测函数积分]
        D1 --> D2[单调收敛定理]
        D2 --> D3[一般可测函数积分]
        D3 --> D4[控制收敛定理]
    end
    
    subgraph 两种积分关系
        A5 --> E1[黎曼可积⇒勒贝格可积]
        E1 --> E2[积分值相等]
        A3 --> E3[勒贝格可积不一定黎曼可积]
    end
    
    subgraph 勒贝格积分优势
        D4 --> F1[极限与积分交换]
        D4 --> F2[L^p空间完备]
        D4 --> F3[逐项积分]
    end
    
    style D3 fill:#e1f5ff,stroke:#01579b,stroke-width:3px
    style E1 fill:#fff8e1,stroke:#ff6f00,stroke-width:2px

```

## 推理步骤详解

### 第一步：黎曼积分回顾

**定义**：$f$ 在 $[a,b]$ 黎曼可积，若：

$$\overline{\int_a^b} f = \underline{\int_a^b} f$$

**Lebesgue判别法**：$f$ 黎曼可积当且仅当 $f$ 有界且不连续点为零测集。

### 第二步：Lebesgue测度

**外测度**：$m^*(E) = \inf\{\sum |I_n|: E \subset \bigcup I_n\}$

**可测集**：$E$ 可测当且仅当对任意 $A$：
$$m^*(A) = m^*(A \cap E) + m^*(A \cap E^c)$$

### 第三步：可测函数

**定义**：$f$ 可测当且仅当对任意开集 $O$，$f^{-1}(O)$ 可测。

**简单函数逼近**：任何非负可测函数可由简单函数单调逼近。

### 第四步：勒贝格积分

**非负简单函数**：$\int \sum a_i \chi_{E_i} = \sum a_i m(E_i)$

**非负可测函数**：$\int f = \sup\{\int \varphi: 0 \leq \varphi \leq f, \varphi \text{简单}\}$

**一般可测函数**：$f = f^+ - f^-$，$\int f = \int f^+ - \int f^-$

### 第五步：积分关系

**定理**：若 $f$ 黎曼可积，则 $f$ 勒贝格可积且积分值相等。

**依赖关系**：

```

黎曼可积 ⇒ 有界+不连续点零测
    ↓
可测函数
    ↓
勒贝格可积

```
