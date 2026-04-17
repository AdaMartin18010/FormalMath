---
title: 相交理论的计算
msc_primary: 14-01
msc_secondary:
- 14C17
- 14C40
course: Stanford FOAG
course_code: Math 216A/B
instructor: Ravi Vakil
foag_chapter: Ch 29
topic: 相交理论计算技术
exercise_type: TEC (技术型)
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

# AG-VK-013: 相交理论的计算

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | Stanford FOAG (Math 216A/B) |
| **教材章节** | Ch 29: 相交理论 |
| **对应FOAG习题** | 29.4.E |
| **类型** | TEC (技术型) |
| **难度** | ⭐⭐⭐⭐ |
| **重要性** | ★★ |

---

## 问题陈述

### 主问题

设 $X$ 是光滑射影簇，维数 $n$。

**(a)** **Chow环的基本性质**：

设 $A^*(X) = \bigoplus_{i=0}^n A^i(X)$ 是Chow环（有理等价类环）。

证明：
1. 次数映射 $\deg: A^n(X) \to \mathbb{Z}$ 是良定义的
2. 对射影空间 $\mathbb{P}^n$，$A^*(\mathbb{P}^n) \cong \mathbb{Z}[h]/(h^{n+1})$，其中 $h = [H]$ 是超平面类
3. 相交乘积满足交换律和结合律

**(b)** **具体计算**：

在 $\mathbb{P}^3$ 中，设 $C$ 是 $d$ 次曲线，$S$ 是 $e$ 次曲面。计算：
1. $C \cdot H$，其中 $H$ 是平面
2. $S \cdot H^2$
3. 若 $C \subset S$，计算自相交 $C^2$（在 $S$ 上）

**(c)** **Bézout定理**：

证明一般形式：设 $Z_1, \ldots, Z_k$ 是 $\mathbb{P}^n$ 中的子簇，余维数分别为 $c_1, \ldots, c_k$，且 $\sum c_i = n$。

若它们正常相交（横截），则：
$$\deg(Z_1 \cap \cdots \cap Z_k) = \prod_{i=1}^k \deg(Z_i)$$

---

## 解题思路

### 思路概述

本题涉及**相交代数的核心技术**：
- **Chow环** - 代数闭链的有理等价
- **具体计算** - 射影空间中的相交数
- **Bézout定理** - 古典代数几何的巅峰

### 计算策略

```
相交理论计算框架

给定子簇 Z_1, Z_2 ⊂ X
    │
    ▼
求 [Z_1] · [Z_2] ∈ A^*(X)
    │
    ├─ 横截相交：几何交点计数
    ├─ 自相交：需要法丛信息
    └─ 非正常相交：需要扰动或 excess 公式
    
射影空间：
    A^*(P^n) = Z[h]/(h^{n+1})
    计算化为多项式乘法
```

---

## 详细解答

### (a) Chow环的基本性质

**1. 次数映射**

**定义**：对 $[Z] \in A^n(X)$（零维闭链），$\deg([Z]) = \sum n_i$ 若 $[Z] = \sum n_i [p_i]$。

**良定义性**：

需证有理等价保持次数。

若 $Z \sim_{\text{rat}} 0$，则存在 $W \subset X \times \mathbb{P}^1$ 使得 $W_0 - W_\infty = Z$。

投射到点，$\deg$ 是固有推进映射 $\pi_*: A^n(X) \to A^0(\text{pt}) = \mathbb{Z}$。

固有推进保持有理等价，所以良定义。∎

**2. $A^*(\mathbb{P}^n)$ 的结构**

**定理**：$A^*(\mathbb{P}^n) = \mathbb{Z}[h]/(h^{n+1})$。

**证明**：

**生成**：超平面 $H$ 生成 $A^1(\mathbb{P}^n)$。

由相交乘积，$h^i$ 对应余维数 $i$ 的线性子空间 $[L^i]$。

**关系**：$h^{n+1} = 0$ 因为 $\dim \mathbb{P}^n = n$。

**无其他关系**：$A^i(\mathbb{P}^n) \cong \mathbb{Z}$ 由 $h^i$ 生成（通过次数映射是同构）。∎

**3. 交换律和结合律**

**交换律**：$[Z] \cdot [W] = [W] \cdot [Z]$。

若正常相交，由几何对称性。

一般情形用Chow移动引理。

**结合律**：$([Z] \cdot [W]) \cdot [V] = [Z] \cdot ([W] \cdot [V])$。

由相交乘积的定义（纤维化积或形变到法锥）。∎

### (b) 具体计算

**在 $\mathbb{P}^3$ 中**：$A^*(\mathbb{P}^3) = \mathbb{Z}[h]/(h^4)$。

**1. $C \cdot H$**

$[C] = d \cdot h^2$（$d$ 次曲线，余维数2）。

$[H] = h$。

$$[C] \cdot [H] = d \cdot h^3$$

$\deg(h^3) = 1$（点类的次数）。

所以 $C \cdot H = d$。

**几何解释**：平面与 $d$ 次曲线相交于 $d$ 个点。

**2. $S \cdot H^2$**

$[S] = e \cdot h$（$e$ 次曲面，余维数1）。

$$[S] \cdot h^2 = e \cdot h^3$$

所以 $S \cdot H^2 = e$。

**几何解释**：曲面与两条一般平面的交（即一般直线）相交于 $e$ 个点。

**3. $C^2$ 在 $S$ 上**

设 $C \subset S$，$S$ 是 $e$ 次曲面。

**伴随公式**：$K_C = (K_S + C)|_C$。

**自交计算**：$C^2$ 在 $S$ 上由 $C \sim eH$ 在 $\mathbb{P}^3$ 中的关系决定。

具体地，$C$ 作为 $S$ 上的除子，$C \sim H|_S$ 当 $C$ 是平面截线。

一般 $d$ 次曲线：用 $C \sim d \cdot L$，其中 $L$ 是直线。

对直线 $L \subset S$，$L^2 = 2 - e - 2g(L) = 2 - e$（由伴随公式）。

所以 $C^2 = d^2(2-e)$（假设 $C \sim d \cdot L$）。

**一般公式**：对 $S$ 上的光滑曲线 $C$，
$$C^2 = 2g(C) - 2 - K_S \cdot C$$

由伴随公式和Riemann-Roch。∎

### (c) Bézout定理

**定理**：$Z_i \subset \mathbb{P}^n$，$\operatorname{codim}(Z_i) = c_i$，$\sum c_i = n$。

正常相交时：
$$\deg(\bigcap Z_i) = \prod \deg(Z_i)$$

**证明**：

设 $[Z_i] = d_i \cdot h^{c_i} \in A^{c_i}(\mathbb{P}^n)$，其中 $d_i = \deg(Z_i)$。

**相交乘积**：
$$\prod [Z_i] = \prod (d_i h^{c_i}) = (\prod d_i) \cdot h^{\sum c_i} = (\prod d_i) \cdot h^n$$

**正常相交**：正常相交意味着交是纯零维的，且重数为1。

$$[\bigcap Z_i] = \prod [Z_i] = (\prod d_i) \cdot [\text{pt}]$$

取次数：
$$\deg(\bigcap Z_i) = \prod d_i = \prod \deg(Z_i)$$∎

---

## 关键概念

### Chow群

$$A_k(X) = \{\text{k维闭链}\} / \{\text{有理等价}\}$$

**有理等价**：两个闭链有理等价，如果它们的差是某个闭链在 $\mathbb{P}^1$ 上的纤维差。

### 相交乘积的构造

**正常相交**：$Z, W \subset X$ 正常相交，如果 $\operatorname{codim}(Z \cap W) = \operatorname{codim}(Z) + \operatorname{codim}(W)$。

**一般情形**：用Chow移动引理或形变到法锥。

---

## 计算示例

### 三次扭曲线

$C \subset \mathbb{P}^3$ 是三次扭曲线（$d=3$）。

$[C] = 3h^2$。

与二次曲面的交：$[Q] = 2h$，$[C] \cdot [Q] = 6h^3$。

所以 $C \cap Q = 6$ 个点（计重数）。

---

## 变式练习

### 变式 1: Grassmannian的Chow环

陈述并计算 $\mathbb{G}(k, n)$ 的Chow环结构（Schubert演算）。

### 变式 2: 自相交的计算

设 $E \subset X$ 是例外除子（吹上）。计算 $E^k$ 对 $k = 1, 2, \ldots, n-1$。

### 变式 3: 陈类的计算

证明陈类的Whitney和公式：对短正合列 $0 \to E \to F \to G \to 0$，
$$c(F) = c(E) \cdot c(G)$$

---

## 常见错误

| 错误 | 纠正 |
|------|------|
| 忽略正常相交条件 | 非正常相交需要 excess 公式 |
| 混淆不同簇的自交 | 自交依赖于周围空间 |
| 次数计算错误 | $h^n$ 是点类，次数为1 |

---

## 学习建议

1. **熟练掌握 $A^*(\mathbb{P}^n)$**：射影空间是最基本的例子
2. **练习具体计算**：曲线、曲面的相交数
3. **学习Schubert演算**：Grassmannian的相交理论

---

**文档位置**: `docs/13-代数几何/习题/AG-VK-013-相交理论的计算.md`  
**创建日期**: 2026-04-10  
**最后更新**: 2026-04-10
