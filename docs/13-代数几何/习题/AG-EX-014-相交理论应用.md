---
习题编号: AG-EX-014
标题: 相交理论应用
类型: 综合型
难度: ⭐⭐⭐⭐
章节: Hartshorne Ch V
对应课程: Harvard Math 232br
预计用时: 120-150分钟
msc: 14C17, 14C40
references:
  textbooks:
    - id: hartshorne_ag
      type: textbook
      title: Algebraic Geometry
msc_primary: 14A99
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

# AG-EX-014: 相交理论应用

## 题目

### 原题 (Hartshorne V.1.1-3)

设 $X$ 是光滑射影曲面，$D, E$ 是除子。

**(a)** 证明相交配对 $(D, E) \mapsto D \cdot E$ 是对称双线性型，且仅依赖于线性等价类。

**(b)** (Hodge指标定理) 设 $H$ 是丰沛除子，$D$ 满足 $D \cdot H = 0$ 且 $D \not\sim 0$。证明 $D^2 < 0$。

**(c)** 对曲面 $X = \mathbb{P}^2$，计算 $\text{Pic}(X)$ 上的相交形式。

### 计算题目

设 $X = \mathbb{P}^1 \times \mathbb{P}^1$（二次曲面）。

**(a)** 描述 $\text{Pic}(X)$ 并计算相交矩阵。

**(b)** 设 $C_1 = \{pt\} \times \mathbb{P}^1$，$C_2 = \mathbb{P}^1 \times \{pt\}$，$\Delta$ 是对角线。计算 $\Delta^2$。

**(c)** 验证Hodge指标定理。

---

## 解答

### 主题目解答

#### (a) 相交配对的基本性质

**定义**: 对曲面上的曲线（除子）$C, D$，定义:
$$C \cdot D = \chi(\mathcal{O}_X) - \chi(\mathcal{O}(-C)) - \chi(\mathcal{O}(-D)) + \chi(\mathcal{O}(-C-D))$$

或用相交重数定义。

**证明对称双线性**:

**对称性**: $C \cdot D = D \cdot C$（由定义）。

**双线性性**: 

对 $(C_1 + C_2) \cdot D$:

由正合列:
$$0 \to \mathcal{O}(-C_1-D) \to \mathcal{O}(-D) \oplus \mathcal{O}(-C_1) \to \mathcal{O} \to \mathcal{O}_{C_1 \cap D} \to 0$$

计算Euler示性数，得:
$$(C_1 + C_2) \cdot D = C_1 \cdot D + C_2 \cdot D$$

**线性等价不变性**:

若 $C \sim C'$，则 $\mathcal{O}(C) \cong \mathcal{O}(C')$。

相交数仅依赖于线丛，故不变。

---

#### (b) Hodge指标定理

**定理**: 设 $H$ 丰沛，$D \cdot H = 0$，$D \not\sim 0$。则 $D^2 < 0$。

**证明**:

**Step 1**: 由Riemann-Roch:

$$\chi(\mathcal{O}(nD)) = \frac{n^2 D^2 - n D \cdot K}{2} + \chi(\mathcal{O}_X)$$

**Step 2**: 若 $D^2 > 0$，则对 $n \gg 0$:

- $h^0(nD)$ 或 $h^0(-nD)$ 增长如 $n^2$

**Step 3**: 但 $D \cdot H = 0$，$H$ 丰沛，故 $D$ 不能是丰沛或反丰沛。

实际上，$h^0(nD)$ 有界（因 $nD \cdot H = 0$）。

**Step 4**: 故 $D^2 \leq 0$。

若 $D^2 = 0$ 且 $D \not\sim 0$，由Riemann-Roch分析得矛盾。

**结论**: $D^2 < 0$。

---

#### (c) $\mathbb{P}^2$ 的相交形式

**Picard群**:

$$\text{Pic}(\mathbb{P}^2) = \mathbb{Z} \cdot H$$

其中 $H$ 是直线类。

**相交**:

$$H^2 = H \cdot H = 1$$

（两一般直线交于一点）

**矩阵**:

$$(1)$$

**一般曲线**: 对 $C \sim dH$，$C' \sim d'H$:

$$C \cdot C' = dd'$$

（Bezout定理）

---

### 计算题目解答

#### (a) $\mathbb{P}^1 \times \mathbb{P}^1$ 的相交形式

**Picard群**:

$$\text{Pic}(X) = \mathbb{Z} \cdot C_1 \oplus \mathbb{Z} \cdot C_2$$

其中:
- $C_1 = \{pt\} \times \mathbb{P}^1$（纤维）
- $C_2 = \mathbb{P}^1 \times \{pt\}$（纤维）

**相交计算**:

- $C_1 \cdot C_1 = 0$（平行纤维不相交）
- $C_2 \cdot C_2 = 0$（同上）
- $C_1 \cdot C_2 = 1$（一点相交）

**矩阵**:

$$\begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$$

**类型**: 双曲平面（signature $(1,1)$）。

---

#### (b) 对角线的自交

**对角线**:

$$\Delta = \{(P, P) : P \in \mathbb{P}^1\} \subseteq \mathbb{P}^1 \times \mathbb{P}^1$$

**计算 $[\Delta]$ 在Picard群中的类**:

投影 $\pi_1: \Delta \to \mathbb{P}^1$ 是同构，故 $\Delta$ 是截面。

一般截面类: $C_1 + C_2$（一条水平+一条垂直纤维）。

实际上，用坐标 $(x_0:x_1), (y_0:y_1)$:

$$\Delta = V(x_0y_1 - x_1y_0)$$

这是 $(1,1)$-型，即 $\Delta \sim C_1 + C_2$。

**自交**:

$$\Delta^2 = (C_1 + C_2)^2 = C_1^2 + 2C_1 \cdot C_2 + C_2^2 = 0 + 2 + 0 = 2$$

**几何**: 对角线在自身上"移动"（由自同构），交于两点。

---

#### (c) Hodge指标定理验证

**丰沛类**: $H = C_1 + C_2$ 是丰沛的。

验证: $H^2 = 2 > 0$，且对任意曲线 $C$，$C \cdot H > 0$。

**正交子空间**:

设 $D = aC_1 + bC_2$，$D \cdot H = 0$:

$$D \cdot (C_1 + C_2) = a + b = 0$$

故 $b = -a$，$D = a(C_1 - C_2)$。

**自交**:

$$D^2 = a^2(C_1 - C_2)^2 = a^2(0 - 2 + 0) = -2a^2 < 0$$

对 $a \neq 0$。

**结论**: Hodge指标定理验证成立。

---

## 解题技巧

### 技巧1: 相交理论速查

```
┌─────────────────────────────────────────┐
│  曲面相交对偶 (rank ρ = dim Pic):       │
│  - 对称双线性型                          │
│  - signature (1, ρ-1)（Hodge理论）      │
│  - 一个正方向（丰沛除子）                │
└─────────────────────────────────────────┘
```

### 技巧2: 自交数计算

| 曲线 | 条件 | 自交 |
|:---|:---|:---:|
| 例外曲线 | 爆破产生 | $-1$ |
| 纤维 | 纤维化 | $0$ |
| 典范除子 | $K^2$ | 数值不变量 |
| 丰沛除子 | $H^2 > 0$ | 正 |

### 技巧3: Hodge指标定理应用

**典型应用**:
- 证明除子的负定性
- 研究曲线的几何
- 模空间的构造

---

## 变式与推广

### 变式1: K3曲面

设 $X$ 是K3曲面（$K_X = 0$，$h^1(\mathcal{O}) = 0$）。

**问题**: 证明 $\text{Pic}(X)$ 是偶格，signature $(1, \rho - 1)$。

---

### 变式2: 算术曲面

设 $X \to \text{Spec}(\mathbb{Z})$ 是算术曲面。

**问题**: 推广相交理论到算术情形（Arakelov理论）。

---

### 变式3: 高维相交

在 $n$ 维流形上，相交理论涉及余维 $r$ 和 $s$ 的类的乘积，余维 $r + s$。

**问题**: 陈述Chow环的基本性质。

---

## 相关概念

| 概念 | 定义 | 符号 |
|:---|:---|:---:|
| 相交配对 | 双线性型 | $D \cdot E$ |
| Picard群 | 线丛类群 | $\text{Pic}(X)$ |
| Hodge指标 | 签名性质 | $(1, \rho-1)$ |
| 自交数 | 曲线与自己的交 | $C^2$ |

## 参考文献

1. Hartshorne, R. *Algebraic Geometry*, Ch V, §1
2. Beauville, A. *Complex Algebraic Surfaces*, Ch I
3. Fulton, W. *Intersection Theory*

---

**创建日期**: 2026-04-10  
**难度**: ⭐⭐⭐⭐  
**预计用时**: 120-150分钟
