---
title: 代数群作用
msc_primary: 14
  - 14L24
  - 14L30
course: Stanford FOAG
course_code: Math 216A/B
instructor: Ravi Vakil
foag_chapter: Ch 21
topic: 群概形与表示理论
exercise_type: REP (表示型)
difficulty: ⭐⭐⭐⭐
importance: ★
references:
  textbooks:
    - id: hartshorne_ag
      type: textbook
      title: Algebraic Geometry
      authors:
      - Robin Hartshorne
      publisher: Springer
      edition: 1st
      year: 1977
      isbn: 978-0387902449
      msc: 14-01
      chapters: 
      url: ~
    - id: vakil_foag
      type: textbook
      title: Foundations of Algebraic Geometry
      authors:
      - Ravi Vakil
      publisher: self-published
      edition: draft
      year: 2024
      isbn: ~
      msc: 14-01
      chapters: 
      url: "https://math.stanford.edu/~vakil/216blog/"
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

# AG-VK-014: 代数群作用

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | Stanford FOAG (Math 216A/B) |
| **教材章节** | Ch 21: 群概形 |
| **对应FOAG习题** | 21.4.G |
| **类型** | REP (表示型) |
| **难度** | ⭐⭐⭐⭐ |
| **重要性** | ★ |

---

## 问题陈述

### 主问题

设 $k$ 是代数闭域，$G$ 是代数群（群概形）。

**(a)** **群概形的定义与例子**：

给出群概形的严格定义，并证明以下都是群概形：
1. $\mathbb{G}_a = \operatorname{Spec} k[x]$（加法群）
2. $\mathbb{G}_m = \operatorname{Spec} k[x, x^{-1}]$（乘法群）
3. $\operatorname{GL}_n = \operatorname{Spec} k[x_{ij}, \det^{-1}]$（一般线性群）

**(b)** **群作用与商**：

设 $G$ 作用在概形 $X$ 上。定义：
1. 作用是有限的（properly discontinuous）
2. 自由作用
3. 几何商 $X/G$ 的存在条件

**(c)** **GIT商**：

设 $G$ 是约化群，$X \subset \mathbb{P}^n$ 是射影概形，$L$ 是 $G$-线性化丰沛线丛。

解释稳定点集 $X^s$ 和半稳定点集 $X^{ss}$ 的构造，以及商概形 $X^s/G$ 和 $X^{ss}/\!/G$ 的存在性。

---

## 解题思路

### 思路概述

本题涉及**代数群与代数几何的交叉**：
- **群概形** - 代数群的几何化
- **群作用** - 对称性的代数几何
- **GIT** - 几何不变量理论

### 群概形图景

```
代数群（群概形）
    │
    ├─ 交换：G_a, G_m, 环面, Abel簇
    │
    └─ 非交换：GL_n, SL_n, SO_n, Sp_n, ...
    
作用与商：
    G × X → X
    │
    ├─ 自由作用 → 好商（概形）
    ├─ 一般作用 → 叠
    └─ 线性化 → GIT商（射影）
```

---

## 详细解答

### (a) 群概形的定义与例子

**定义**：$k$-群概形是 $k$-概形 $G$ 带有态射：
- 乘法 $m: G \times G \to G$
- 单位元 $e: \operatorname{Spec} k \to G$
- 逆元 $i: G \to G$

满足群公理（用交换图表表示）。

**例子证明**：

**1. $\mathbb{G}_a = \operatorname{Spec} k[x]$**

- 乘法：$k[x] \to k[x] \otimes k[x] = k[x_1, x_2]$，$x \mapsto x_1 + x_2$
- 单位：$k[x] \to k$，$x \mapsto 0$
- 逆元：$k[x] \to k[x]$，$x \mapsto -x$

**Hopf代数结构**：$k[x]$ 有余乘法 $\Delta(x) = x \otimes 1 + 1 \otimes x$。

**2. $\mathbb{G}_m = \operatorname{Spec} k[x, x^{-1}]$**

- 乘法：$x \mapsto x_1 \cdot x_2$
- 单位：$x \mapsto 1$
- 逆元：$x \mapsto x^{-1}$

**Hopf代数**：$\Delta(x) = x \otimes x$（群样元）。

**3. $\operatorname{GL}_n = \operatorname{Spec} k[x_{ij}, \det^{-1}]$**

- 乘法：矩阵乘法 $(AB)_{ij} = \sum_k a_{ik}b_{kj}$
- 单位：单位矩阵
- 逆元：逆矩阵（Cramer法则，分母是行列式）

∎

### (b) 群作用与商

**群作用的定义**：

态射 $\sigma: G \times X \to X$ 满足：
1. $\sigma \circ (e \times \text{id}_X) = \text{id}_X$
2. $\sigma \circ (m \times \text{id}_X) = \sigma \circ (\text{id}_G \times \sigma)$

**作用类型**：

**1. 有限作用（properly discontinuous）**：

映射 $G \times X \to X \times X$，$(g, x) \mapsto (gx, x)$ 是固有且拟有限的。

**2. 自由作用**：

上述映射是闭浸入（无不动点，无稳定子群）。

**3. 几何商**：

概形态射 $\pi: X \to Y$ 是几何商，如果：
1. $\pi$ 是满射，纤维是 $G$-轨道
2. $\mathcal{O}_Y = \pi_*^G(\mathcal{O}_X)$（$G$-不变函数层）
3. 万有性质

**存在性**：自由作用 $\Rightarrow$ 几何商存在（作为概形）。

一般情形需要叠。∎

### (c) GIT商

**线性化**：$G$-线性化线丛 $L$ 是带 $G$-作用的线丛，作用提升 $X$ 上的作用。

**稳定点**（$X^s$）：$x \in X$ 稳定，如果：
1. $G$-轨道 $G \cdot x \subset X$ 是闭的
2. 稳定子 $G_x$ 是有限的

**半稳定点**（$X^{ss}$）：$x \in X$ 半稳定，如果存在 $G$-不变截面 $s \in H^0(X, L^n)^G$ 使得 $s(x) \neq 0$。

**GIT商的存在性**（Mumford）：

1. **稳定商**：$X^s/G$ 存在，是拟射影概形
2. **半稳定商**：$X^{ss}/\!/G = \operatorname{Proj} \bigoplus_{n \geq 0} H^0(X, L^n)^G$ 是射影概形

映射 $X^{ss} \to X^{ss}/\!/G$ 是范畴商（满足万有性质）。

∎

---

## 关键概念

### Hopf代数

群概形 $G$ 对应 Hopf代数 $H = \Gamma(G, \mathcal{O}_G)$：
- 乘法 $\mu: H \otimes H \to H$
- 余乘法 $\Delta: H \to H \otimes H$
- 对极映射 $S: H \to H$

### GIT的核心思想

"坏"商的问题：
- 轨道不闭 $\Rightarrow$ 需要抛弃或合并
- 稳定子非有限 $\Rightarrow$ 维数跳跃

GIT解决方案：
- 用线性化选择"好"的点
- 半稳定点有射影商
- 稳定点有好几何

---

## 重要例子

### 环面的商

$\mathbb{G}_m$ 作用在 $\mathbb{A}^n$ 上：
$$t \cdot (x_1, \ldots, x_n) = (t^{a_1}x_1, \ldots, t^{a_n}x_n)$$

GIT商依赖于权 $(a_1, \ldots, a_n)$。

### 射影空间的商

$\mathbb{G}_m$ 作用在 $\mathbb{P}^n$ 上，权 $(1, 1, \ldots, 1)$：

所有点稳定，$\mathbb{P}^n / \mathbb{G}_m = \mathbb{P}^{n-1}$（自变量商）。

---

## 变式练习

### 变式 1: 模空间的GIT构造

解释如何用GIT构造曲线模空间 $M_g$（通过Hilbert概形）。

### 变式 2: 辛约化

对比GIT商与Marsden-Weinstein辛约化（在复几何中）。

### 变式 3: 不稳定锥

描述Hilbert-Mumford判据中的不稳定锥。

---

## 常见错误

| 错误 | 纠正 |
|------|------|
| 认为所有作用有概形商 | 一般需要用叠 |
| 混淆稳定和半稳定 | 稳定更强（闭轨道+有限稳定子） |
| 忽略线性化的选择 | 不同的线性化给出不同的商 |

---

## 学习建议

1. **理解Hopf代数**：群概形的代数对应
2. **练习GIT例子**：射影空间、Grassmannian的商
3. **学习稳定性条件**：Hilbert-Mumford判据

---

**文档位置**: `docs/13-代数几何/习题/AG-VK-014-代数群作用.md`  
**创建日期**: 2026-04-10  
**最后更新**: 2026-04-10
