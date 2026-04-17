---
title: 对偶理论应用
msc_primary: 14-01
msc_secondary:
- 14F17
- 14B15
course: Stanford FOAG
course_code: Math 216A/B
instructor: Ravi Vakil
foag_chapter: Ch 30
topic: Serre对偶与Grothendieck对偶
exercise_type: SYN (综合型)
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
      chapters: []
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
      chapters: []
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

# AG-VK-010: 对偶理论应用

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | Stanford FOAG (Math 216A/B) |
| **教材章节** | Ch 30: 对偶理论 |
| **对应FOAG习题** | 30.1.A, 30.2.D |
| **类型** | SYN (综合型) |
| **难度** | ⭐⭐⭐⭐ |
| **重要性** | ★★ |

---

## 问题陈述

### 主问题

设 $X$ 是域 $k$ 上的光滑射影簇，维数 $n$，$\mathcal{F}$ 是 $X$ 上的局部自由层。

**(a)** **Serre对偶**：

证明存在自然的（函子性的）完美配对：
$$H^i(X, \mathcal{F}) \times H^{n-i}(X, \mathcal{F}^\vee \otimes \omega_X) \to k$$

其中 $\omega_X = \Omega_{X/k}^n$ 是典范丛。

等价地，给出同构：
$$H^i(X, \mathcal{F})^\vee \cong H^{n-i}(X, \mathcal{F}^\vee \otimes \omega_X)$$

**(b)** **曲线上的特殊形式**：

设 $C$ 是光滑射影曲线，亏格 $g$。证明：
- $\dim H^0(C, \omega_C) = g$
- $\dim H^1(C, \mathcal{O}_C) = g$
- 对任意除子 $D$，$\ell(D) - \ell(K - D) = \deg(D) + 1 - g$

（即经典Riemann-Roch定理）

**(c)** **Grothendieck对偶的形式**：

设 $f: X \to Y$ 是固有态射，维数 $n$。陈述并解释对偶复形 $\omega_f^\bullet$ 的存在性以及迹映射的构造。

---

## 解题思路

### 思路概述

本题涉及**代数几何最深层的定理之一**：
- **Serre对偶** - 光滑射影簇上的上同调对偶
- **Riemann-Roch** - 曲线上的经典应用
- **Grothendieck对偶** - 最一般的对偶理论

### 对偶性全景

```
Serre对偶（光滑射影簇）
    │
    ▼
Grothendieck对偶（固有态射）
    │
    ├─ 奇异概形
    ├─ 非紧情形
    └─ 相对情形
    
应用：
├─ Riemann-Roch
├─ Hodge理论
├─ 形变理论
└─ 枚举几何
```

---

## 详细解答

### (a) Serre对偶

**定理**（Serre Duality）：设 $X$ 是 $n$ 维光滑射影簇，$\mathcal{F}$ 是局部自由层。

则有函子同构：
$$\operatorname{Ext}^i(\mathcal{F}, \omega_X) \cong H^{n-i}(X, \mathcal{F})^*$$

若 $\mathcal{F}$ 局部自由，$\operatorname{Ext}^i(\mathcal{F}, \omega_X) = H^i(X, \mathcal{F}^\vee \otimes \omega_X)$。

**证明概要**：

**步骤1**: Yoneda配对。

对任意 $", \mathcal{G}$，有配对：
$$\operatorname{Ext}^i(\mathcal{F}, \mathcal{G}) \times \operatorname{Ext}^{n-i}(\mathcal{G}, \omega_X) \to \operatorname{Ext}^n(\mathcal{F}, \omega_X)$$

**步骤2**: 迹映射。

构造 $\operatorname{Tr}: H^n(X, \omega_X) \to k$。

在Čech上同调中，由留数理论给出。

**步骤3**: 完美配对。

组合上述，得到：
$$H^i(X, \mathcal{F}^\vee \otimes \omega_X) \times H^{n-i}(X, \mathcal{F}) \to H^n(X, \omega_X) \xrightarrow{\operatorname{Tr}} k$$

验证这是完美配对（即诱导同构）。

**步骤4**: 归纳法。

对 $n$ 归纳。$n = 0$ 显然。

对一般 $n$，用超平面截断和归纳假设。

∎

### (b) 曲线上的Riemann-Roch

**Serre对偶在曲线上**：设 $C$ 是光滑射影曲线，亏格 $g$。

对除子 $D$，令 $\mathcal{F} = \mathcal{O}(D)$，$\mathcal{F}^\vee = \mathcal{O}(-D)$。

$$H^0(C, \mathcal{O}(D)) \times H^1(C, \mathcal{O}(K-D)) \to k$$

由Serre对偶：
$$h^0(D) = h^1(K-D)$$

**Riemann-Roch定理**：

$$\chi(\mathcal{O}(D)) = h^0(D) - h^1(D) = \deg(D) + 1 - g$$

**证明**：

**步骤1**: $\chi(\mathcal{O}) = 1 - g$。

$h^0(\mathcal{O}) = 1$（常值函数），$h^1(\mathcal{O}) = g$（由Serre对偶，等于 $h^0(K) = g$）。

**步骤2**: 对除子加点的归纳。

若 $D' = D + p$，有正合列：
$$0 \to \mathcal{O}(D) \to \mathcal{O}(D') \to k(p) \to 0$$

取Euler示性数：
$$\chi(\mathcal{O}(D')) = \chi(\mathcal{O}(D)) + 1$$

**步骤3**: 一般情形。

由归纳，$\chi(\mathcal{O}(D)) = \deg(D) + \chi(\mathcal{O}) = \deg(D) + 1 - g$。

由Serre对偶：
$$h^0(D) - h^0(K-D) = \deg(D) + 1 - g$$

∎

### (c) Grothendieck对偶

**定理**（Grothendieck Duality）：设 $f: X \to Y$ 是维数 $n$ 的固有态射。

存在**对偶复形** $\omega_f^\bullet \in D^b(X)$ 和**迹映射** $\operatorname{Tr}_f: Rf_*\omega_f^\bullet \to \mathcal{O}_Y$ 使得：

对任意 $\mathcal{F}^\bullet \in D^b(X)$，诱导映射：
$$Rf_*R\mathcal{H}om_X(\mathcal{F}^\bullet, \omega_f^\bullet) \to R\mathcal{H}om_Y(Rf_*\mathcal{F}^\bullet, \mathcal{O}_Y)$$

是同构。

**特殊情形**：

1. **$Y = \operatorname{Spec} k$，$X$ 光滑**：$\omega_f^\bullet = \omega_X[n]$，恢复Serre对偶。

2. **$f$ 有限**：$\omega_f^\bullet = \bar{f}^!\mathcal{O}_Y$，其中 $\bar{f}^!$ 是例外逆像。

3. **$f$ Cohen-Macaulay**：$\omega_f^\bullet$ 是层（移位）。

**应用**：

- 相对Serre对偶
- 奇异簇的对偶
- 对偶层的计算

---

## 关键概念

### Serre对偶的形式

**光滑射影簇**（$n$ 维）：
$$H^i(X, \mathcal{F})^\vee \cong H^{n-i}(X, \mathcal{F}^\vee \otimes \omega_X)$$

**曲线**（$n = 1$）：
$$H^0(C, L) \times H^1(C, L^{-1} \otimes K) \to k$$

**射影空间**（计算）：
$$h^i(\mathbb{P}^n, \mathcal{O}(k)) = \begin{cases} \binom{k+n}{n} & i = 0, k \geq 0 \\ \binom{-k-1}{n} & i = n, k \leq -n-1 \\ 0 & \text{其他} \end{cases}$$

### 典范丛

**定义**：$\omega_X = \det \Omega_{X/k}^1 = \Omega_{X/k}^n$（最高外幂）。

**曲线**：$\omega_C = \Omega_C^1$（微分形式层）。

**性质**：
- 光滑簇：$\omega_X$ 是线丛
- 奇异簇：可能不是线丛，需要处理（对偶化层）

---

## 重要应用

### Hodge理论

Serre对偶是Hodge理论的代数版本：
$$H^{p,q}(X)^\vee \cong H^{n-p, n-q}(X)$$

### Euler示性数公式

对 $n$ 维光滑射影簇：
$$\chi(\mathcal{F}) = (-1)^n \chi(\mathcal{F}^\vee \otimes \omega_X)$$

---

## 变式练习

### 变式 1: 曲面的Noether公式

对光滑射影曲面 $S$，证明Noether公式：
$$\chi(\mathcal{O}_S) = \frac{1}{12}(K_S^2 + c_2(S))$$

### 变式 2: Kodaira维数

定义并计算 $\mathbb{P}^n$、曲线、曲面的Kodaira维数。

### 变式 3: 残余复形

设 $X$ 是 $n$ 维Noether概形，$f: X \to \operatorname{Spec} k$。解释残余复形 $\mathcal{K}_X^\bullet$ 与对偶复形的关系。

---

## 常见错误

| 错误 | 纠正 |
|------|------|
| Serre对偶对所有层成立 | 需要Cohen-Macaulay或局部自由条件 |
| 混淆典范层和对偶化层 | 光滑时相同，奇异时不同 |
| 忽略迹映射的存在性 | 对偶需要明确的迹映射 |

---

## 学习建议

1. **理解对偶的层次**：Serre → Grothendieck → 最一般形式
2. **掌握曲线情形**：Riemann-Roch是Serre对偶的经典应用
3. **学习残余复形**：理解对偶的几何实现

---

**文档位置**: `docs/13-代数几何/习题/AG-VK-010-对偶理论应用.md`  
**创建日期**: 2026-04-10  
**最后更新**: 2026-04-10
