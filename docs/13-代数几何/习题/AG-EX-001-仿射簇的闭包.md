---
习题编号: AG-EX-001
标题: 仿射簇的闭包
类型: 经典习题
难度: ⭐⭐
章节: Hartshorne Ch I
对应课程: Harvard Math 232br
预计用时: 45-60分钟
msc: 14A10, 14A25
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

# AG-EX-001: 仿射簇的闭包

## 题目

### 原题 (Hartshorne I.1.6)

设 $Y \subseteq \mathbb{A}^n$ 是仿射空间的一个子集，$\overline{Y}$ 表示 $Y$ 在Zariski拓扑下的闭包。

**(a)** 证明 $I(\overline{Y}) = I(Y)$，其中 $I(Y)$ 是 $Y$ 的理想。

**(b)** 证明若 $Y$ 是拟仿射簇，则 $\overline{Y}$ 是仿射簇。

### 变式题目

设 $Y = \{(t, t^2, t^3) \in \mathbb{A}^3 : t \in k\}$ 是 $\mathbb{A}^3$ 中的扭曲三次曲线。

**(a)** 求 $I(Y)$ 的生成元。

**(b)** 证明 $\overline{Y} = Y$，即 $Y$ 是闭集。

---

## 解答

### 主题目解答

#### (a) 证明 $I(\overline{Y}) = I(Y)$

**证明**:

**Step 1: 证明 $I(Y) \subseteq I(\overline{Y})$**

设 $f \in I(Y)$，即对所有 $P \in Y$，有 $f(P) = 0$。

由于 $f$ 是多项式函数（连续函数），且 $f$ 在 $Y$ 上恒为零，
因此 $f$ 在 $Y$ 的闭包 $\overline{Y}$ 上也恒为零。

故 $f \in I(\overline{Y})$。

**Step 2: 证明 $I(\overline{Y}) \subseteq I(Y)$**

设 $f \in I(\overline{Y})$，即对所有 $P \in \overline{Y}$，有 $f(P) = 0$。

由于 $Y \subseteq \overline{Y}$，所以对所有 $P \in Y$，也有 $f(P) = 0$。

故 $f \in I(Y)$。

**结论**: $I(\overline{Y}) = I(Y)$。

---

#### (b) 拟仿射簇的闭包是仿射簇

**定义回顾**:
- **拟仿射簇**: 仿射簇的开子集
- **仿射簇**: 不可约的闭代数集

**证明**:

设 $Y$ 是拟仿射簇，则存在仿射簇 $X$ 和开集 $U \subseteq X$，使得 $Y = U$。

**Step 1**: $\overline{Y} \subseteq X$ 是闭集，故 $\overline{Y}$ 是仿射代数集。

**Step 2**: 证明 $\overline{Y}$ 不可约。

假设 $\overline{Y} = Z_1 \cup Z_2$，其中 $Z_1, Z_2$ 是闭集。

则 $Y = (Y \cap Z_1) \cup (Y \cap Z_2)$。

由于 $Y$ 不可约（作为仿射簇的开子集），不妨设 $Y = Y \cap Z_1$，即 $Y \subseteq Z_1$。

由于 $Z_1$ 闭且包含 $Y$，故 $\overline{Y} \subseteq Z_1$。

因此 $\overline{Y} = Z_1$，证明 $\overline{Y}$ 不可约。

**结论**: $\overline{Y}$ 是仿射簇。

---

### 变式题目解答

#### (a) 求 $I(Y)$ 的生成元

$Y = \{(t, t^2, t^3) : t \in k\}$ 的参数方程为:
$$x = t, \quad y = t^2, \quad z = t^3$$

消去参数 $t$:
- 从 $x = t$ 得 $t = x$
- 代入 $y = t^2$ 得 $y = x^2$，即 $y - x^2 = 0$
- 代入 $z = t^3$ 得 $z = x^3$，即 $z - x^3 = 0$

还需第三个关系:
$$z^2 = x^6 = y^3 \Rightarrow z^2 - y^3 = 0$$

验证: $z^2 - y^3 = x^6 - (x^2)^3 = x^6 - x^6 = 0$ ✓

**结论**: 
$$I(Y) = (y - x^2, z - x^3) = (y - x^2, z - xy)$$

---

#### (b) 证明 $\overline{Y} = Y$

**证明**:

**Step 1**: 显然 $Y \subseteq \overline{Y}$。

**Step 2**: 证明 $V(I(Y)) \subseteq Y$。

设 $P = (a, b, c) \in V(I(Y))$，则:
- $b - a^2 = 0 \Rightarrow b = a^2$
- $c - a^3 = 0 \Rightarrow c = a^3$

故 $P = (a, a^2, a^3) \in Y$。

**Step 3**: 由零点定理，$\overline{Y} = V(I(Y)) = Y$。

**结论**: $Y$ 是仿射簇（闭集）。

---

## 解题技巧

### 技巧1: 闭包与理想的对应

```
闭包计算的核心关系:
┌─────────────────────────────────────┐
│  $\overline{Y} = V(I(Y))$           │
│  $I(\overline{Y}) = I(Y)$           │
└─────────────────────────────────────┘
```

**应用场景**: 
- 已知子集求闭包
- 验证子集是否闭
- 计算理想的根

### 技巧2: 参数曲线理想生成元

对于参数曲线 $(f_1(t), \ldots, f_n(t))$:

1. **消去参数**: 寻找多项式关系
2. **Gröbner基**: 系统计算方法
3. **几何直观**: 观察代数依赖

### 技巧3: 不可约性检验

检验代数集 $X$ 是否不可约:
- 等价于 $I(X)$ 是否为素理想
- 或证明 $X$ 不是两个真闭子集的并

---

## 变式与推广

### 变式1: 高维扭曲曲线

设 $Y = \{(t, t^2, t^3, \ldots, t^n) \in \mathbb{A}^n : t \in k\}$。

**问题**: 求 $I(Y)$ 的生成元集合。

**提示**: 考虑关系 $x_i x_j = x_{i+j}$（适当指标）。

---

### 变式2: 乘积簇的闭包

设 $X \subseteq \mathbb{A}^n$, $Y \subseteq \mathbb{A}^m$ 是代数集。

**问题**: 证明 $\overline{X \times Y} = \overline{X} \times \overline{Y}$（在 $\mathbb{A}^{n+m}$ 中）。

---

### 变式3: 有理函数的零点集

设 $f/g$ 是 $\mathbb{A}^n$ 上的有理函数，$Y = \{P : f(P) = 0, g(P) \neq 0\}$。

**问题**: 求 $\overline{Y}$ 的方程。

---

## 相关概念

| 概念 | 定义 | 符号 |
|:---|:---|:---:|
| Zariski闭包 | 包含集合的最小闭集 | $\overline{Y}$ |
| 消失理想 | 在集合上为零的多项式理想 | $I(Y)$ |
| 零点集 | 理想的所有公共零点 | $V(I)$ |
| 拟仿射簇 | 仿射簇的开子集 | - |

## 参考文献

1. Hartshorne, R. *Algebraic Geometry*, Ch I, §1, Exercise 1.6
2. Shafarevich, I. *Basic Algebraic Geometry*, Ch I, §2
3. Reid, M. *Undergraduate Algebraic Geometry*, Chapter 3

---

**创建日期**: 2026-04-10  
**难度**: ⭐⭐  
**预计用时**: 45-60分钟
