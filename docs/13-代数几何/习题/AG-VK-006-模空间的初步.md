---
title: 模空间的初步
msc_primary: 14
  - 14D20
  - 14D22
course: Stanford FOAG
course_code: Math 216A/B
instructor: Ravi Vakil
foag_chapter: Ch 12, 14
topic: 模空间理论入门
exercise_type: FRO (前沿型)
difficulty: ⭐⭐⭐⭐
importance: ★★
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

# AG-VK-006: 模空间的初步

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | Stanford FOAG (Math 216A/B) |
| **教材章节** | Ch 12, 14: 模问题 |
| **对应FOAG习题** | 12.2.C, 14.2.G |
| **类型** | FRO (前沿型) |
| **难度** | ⭐⭐⭐⭐ |
| **重要性** | ★★ |

---

## 问题陈述

### 主问题

设 $k$ 是代数闭域，考虑以下模问题。

**(a)** **Hilbert概形的函子定义**：

固定射影空间 $\mathbb{P}^n_k$ 和Hilbert多项式 $P(t) \in \mathbb{Q}[t]$。定义函子：
$$\mathcal{H}ilb_{P}(T) = \left\{ \begin{array}{c} \text{闭子概形 } Z \subset \mathbb{P}^n_T \\ \text{平坦于 } T \\ \text{纤维有Hilbert多项式 } P \end{array} \right\}$$

证明：这是一个可表函子，代表概形 $\operatorname{Hilb}_P(\mathbb{P}^n)$（Hilbert概形）。

**(b)** **Grassmannian作为特例**：

证明：当 $P(t) = d$（常数多项式）时，$\operatorname{Hilb}_d(\mathbb{P}^n) = \mathbb{G}(n-d, n)$（Grassmannian）。

**(c)** **模空间的存在性问题**：

解释为什么以下模问题的可表性不同：
1. 射影直线上秩2、度0的向量丛（可表）
2. 射影平面上秩2、$c_1=0$、$c_2=n$ 的向量丛（需要稳定性条件）
3. 亏格 $g$ 的光滑射影曲线（粗模空间存在，精细模空间不存在）

---

## 解题思路

### 思路概述

本题涉及**现代代数几何的前沿领域**：
- **Hilbert概形** - 参数化子概形
- **Grassmannian** - 最简单的模空间
- **存在性条件** - 稳定性、有界性

### 概念层级

```
模空间的层次结构

Hilbert概形 ─────→ 最一般的参数空间
    │                  │
    ▼                  ▼
Quot概形 ────────→ 参数化商层
    │                  │
    ▼                  ▼
Grassmannian ────→ 参数化线性子空间
    │                  │
    ▼                  ▼
射影空间 ────────→ 参数化超平面/点
```

---

## 详细解答

### (a) Hilbert概形的可表性

**定理**（Grothendieck）：对固定射影空间 $\mathbb{P}^n$ 和Hilbert多项式 $P$，函子 $\mathcal{H}ilb_P$ 是可表的。

**证明概要**：

**步骤1: 有界性 (Boundedness)**

关键引理（Gotzmann）：存在仅依赖于 $P$ 的整数 $m$，使得任何具有Hilbert多项式 $P$ 的子概形 $Z \subset \mathbb{P}^n$ 被其在 $H^0(\mathbb{P}^n, \mathcal{O}(m))$ 中的像决定。

这意味着：所有这样的 $Z$ 属于有限个平坦族。

**步骤2: 构造 Quot 概形**

更一般地，对凝聚层 $\mathcal{E}$ 和多项式 $P$，构造 Quot 概形 $\operatorname{Quot}(\mathcal{E}, P)$ 参数化 $\mathcal{E}$ 的商（具有Hilbert多项式 $P$）。

**步骤3: Hilbert概形 = Quot 的特殊情形**

$$\operatorname{Hilb}_P(\mathbb{P}^n) = \operatorname{Quot}(\mathcal{O}_{\mathbb{P}^n}, P)$$

**步骤4: 泛族的构造**

在 $\operatorname{Hilb}_P(\mathbb{P}^n) \times \mathbb{P}^n$ 中存在泛闭子概形 $\mathcal{Z}$（泛族），使得对任意 $T$ 和 $Z \subset \mathbb{P}^n_T$，存在唯一的 $g: T \to \operatorname{Hilb}_P(\mathbb{P}^n)$ 使得 $Z = g^*\mathcal{Z}$。

∎（完整证明较长，见FGA或Vakil的笔记）

### (b) Grassmannian作为特例

**情形**：$P(t) = d$（常数）。

这意味着子概形 $Z \subset \mathbb{P}^n$ 的维数是0，长度是 $d$。

等等，这与Grassmannian不同...

**修正理解**：应该是考虑 $P(t) = \binom{t+k}{k}$（线性子空间的Hilbert多项式）。

实际上，$\mathbb{G}(r, n)$ 参数化 $\mathbb{P}^n$ 中的 $r$-维线性子空间。

$\mathbb{P}^r \subset \mathbb{P}^n$ 的Hilbert多项式是：
$$P(t) = \binom{t+r}{r}$$

所以：
$$\operatorname{Hilb}_{\binom{t+r}{r}}(\mathbb{P}^n) \supset \mathbb{G}(r, n)$$

实际上，对于线性多项式，Hilbert概形的连通分支就是 Grassmannian。

**正确陈述**：

$$\operatorname{Hilb}_{\binom{t+m}{m}}(\mathbb{P}^n) \cong \mathbb{G}(m, n)$$

当 $m = 0$，$P(t) = 1$，$\operatorname{Hilb}_1(\mathbb{P}^n) = \mathbb{P}^n$（参数化点）。

当 $m = n-1$，$P(t) = t + 1$，$\operatorname{Hilb}_{t+1}(\mathbb{P}^n) = (\mathbb{P}^n)^\vee$（参数化超平面）。∎

### (c) 模空间存在性的对比

**情形1: $\mathbb{P}^1$ 上秩2、度0的向量丛**

由Grothendieck分解定理：
$$\mathcal{E} \cong \mathcal{O}(a) \oplus \mathcal{O}(b), \quad a + b = 0, \quad a \leq b$$

所以 $a \leq 0$，$b = -a \geq 0$。

可能的分解：$\mathcal{O} \oplus \mathcal{O}$ 或 $\mathcal{O}(-n) \oplus \mathcal{O}(n)$（$n > 0$）。

这些不形成连续族，模空间是离散的点集。

**注**：如果固定 $a, b$，则只有唯一同构类。

**情形2: $\mathbb{P}^2$ 上秩2、$c_1=0$、$c_2=n$**

这是更复杂的情形。Maruyama证明了：若固定Chern类和稳定性条件，则模空间是拟射影概形。

**稳定性条件**（Gieseker-Maruyama）：
- 向量丛 $\mathcal{E}$ 是稳定的，如果对任意真子层 $\mathcal{F} \subset \mathcal{E}$：
$$\frac{\chi(\mathcal{F}(m))}{\operatorname{rank}(\mathcal{F})} < \frac{\chi(\mathcal{E}(m))}{\operatorname{rank}(\mathcal{E})}, \quad m \gg 0$$

**不稳定性**：
- 没有稳定性条件时，模空间不紧（需要紧化）
- 存在从半稳定到稳定的跳跃现象

**情形3: 亏格 $g$ 的光滑曲线**

**$M_g$ 的存在性**：
- Deligne-Mumford证明了 $M_g$（$g \geq 2$）是Deligne-Mumford叠
- 作为粗模空间，$M_g$ 是拟射影概形（由Mumford）

**精细模空间不存在**：
- 一般曲线有平凡自同构群，但某些特殊曲线（如超椭圆曲线）有额外自同构
- 自同构的存在阻碍泛族的存在
- 因此只有粗模空间，没有精细模空间

**对比总结**：

| 模问题 | 可表性 | 关键条件 |
|--------|--------|----------|
| Hilbert概形 | ✅ 精细 | 固定Hilbert多项式 |
| 稳定向量丛 | ✅ 精细 | 稳定性条件 |
| 不稳定向量丛 | ❌ | 需要紧化 |
| 光滑曲线 | ⚠️ 粗模 | 自同构阻碍精细 |

---

## 关键概念

### Hilbert多项式

对凝聚层 $\mathcal{F}$ 在 $\mathbb{P}^n$ 上，定义：
$$P_{\mathcal{F}}(m) = \chi(\mathcal{F}(m)) = \sum (-1)^i h^i(\mathbb{P}^n, \mathcal{F}(m))$$

这是多项式（由Serre消失和有限性）。

**几何意义**：
- $\deg P = \dim \operatorname{supp}(\mathcal{F})$
- 首项系数与次数相关
- 其他系数与Chern类相关

### 稳定性条件

**向量丛的稳定性**（Mumford）：

$\mathcal{E}$ 是稳定的，如果对任意真子层 $\mathcal{F}$：
$$\mu(\mathcal{F}) < \mu(\mathcal{E})$$

其中斜率 $\mu(\mathcal{F}) = \deg(\mathcal{F}) / \operatorname{rank}(\mathcal{F})$。

**意义**：
- 稳定性保证模空间的好性质（紧、射影）
- 与物理中的孤子稳定性、规范场论联系

---

## 相关结果

### 重要的模空间

| 模空间 | 参数化对象 | 维度 | 性质 |
|--------|-----------|------|------|
| $M_{g,n}$ | 带 $n$ 个点的亏格 $g$ 曲线 | $3g-3+n$ | Deligne-Mumford叠 |
| $A_g$ | 主极化Abel簇 | $g(g+1)/2$ | 叠 |
| $M(r, c_1, c_2)$ | 稳定向量丛 | 计算 | 拟射影 |
| $Q_{d,n}$ | 度 $d$ 的映射 $f: \mathbb{P}^1 \to \mathbb{P}^n$ | $(n+1)(d+1)-1$ | 射影 |

---

## 变式练习

### 变式 1: Hilbert概形的维度

计算 $\operatorname{Hilb}_3(\mathbb{P}^2)$（平面上的3点）的维度。

### 变式 2: Quot概形的存在

陈述并理解Quot概形的存在定理。

### 变式 3: 稳定性与几何不变量理论

解释稳定性条件如何与GIT（Geometric Invariant Theory）的稳定性联系。

---

## 前沿联系

### 镜像对称

Calabi-Yau流形的模空间与镜像对称深刻联系：
$$\text{复结构模空间} \leftrightarrow \text{Kähler结构模空间}$$

### 枚举几何

通过模空间（特别是稳定映射模空间）计算Gromov-Witten不变量。

---

## 学习建议

1. **理解Hilbert概形的构造**：这是代数几何技术的巅峰
2. **研究具体例子**：Grassmannian、曲线模空间等
3. **关注稳定性条件**：现代模空间理论的核心

---

**文档位置**: `docs/13-代数几何/习题/AG-VK-006-模空间的初步.md`  
**创建日期**: 2026-04-10  
**最后更新**: 2026-04-10
