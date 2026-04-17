---
习题编号: AG-EX-008
标题: 切空间与光滑性
类型: 分析型
难度: ⭐⭐⭐
章节: Hartshorne Ch I/II
对应课程: Harvard Math 232br
预计用时: 60-90分钟
msc: 14B05, 14B10
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

# AG-EX-008: 切空间与光滑性

## 题目

### 原题 (Hartshorne I.6.1 + II.2.8)

设 $X$ 是代数簇/概形，$P \in X$ 是点。

**(a)** 对仿射簇 $X \subseteq \mathbb{A}^n$，定义Zariski切空间:
$$T_P(X) = \left\{(a_1, \ldots, a_n) \in k^n : \sum_{i=1}^n \frac{\partial f}{\partial x_i}(P) \cdot a_i = 0, \forall f \in I(X)\right\}$$

证明这是内蕴定义的（不依赖于嵌入）。

**(b)** 定义 $X$ 在 $P$ 的维数 $\dim_P(X)$ 和切空间维数。证明 $X$ 在 $P$ 光滑当且仅当 $\dim T_P(X) = \dim_P(X)$。

**(c)** 对概形，用局部环的极大理想定义切空间:
$$T_P(X) = (\mathfrak{m}_P / \mathfrak{m}_P^2)^*$$

证明这与簇情形的定义一致。

### 计算题目

设 $X = V(y^2 - x^3) \subseteq \mathbb{A}^2$（尖点三次曲线）。

**(a)** 计算所有点 $P \in X$ 的切空间维数。

**(b)** 找出 $X$ 的奇点集。

**(c)** 描述奇点处的切锥。

---

## 解答

### 主题目解答

#### (a) 切空间的内蕴性

**代数定义**:

设 $A = k[X] = k[x_1, \ldots, x_n]/I(X)$，$\mathfrak{m}_P$ 是 $P$ 对应的极大理想。

**定义**:
$$T_P(X) = \text{Der}_k(A, k)$$

其中 $k$ 是 $A$-模通过 $A/\mathfrak{m}_P \cong k$。

**证明等价性**:

**Step 1**: 导子到切向量的对应。

给定导子 $D: A \to k$，设 $a_i = D(x_i)$。

对 $f \in I(X)$:
$$0 = D(f) = \sum_{i=1}^n \frac{\partial f}{\partial x_i}(P) \cdot D(x_i) = \sum_{i=1}^n \frac{\partial f}{\partial x_i}(P) \cdot a_i$$

**Step 2**: 切向量到导子的对应。

给定 $(a_1, \ldots, a_n)$ 满足条件，定义:
$$D(g) = \sum_{i=1}^n \frac{\partial g}{\partial x_i}(P) \cdot a_i$$

由条件，$D$ 在 $I(X)$ 上为零，故下降为 $A \to k$ 的导子。

**结论**: 两种定义等价，$\text{Der}_k(A, k)$ 不依赖于嵌入。

---

#### (b) 光滑性判据

**定义**:
- $\dim_P(X)$: $X$ 在 $P$ 的局部维数
- $X$ 在 $P$ 光滑: $\dim_k T_P(X) = \dim_P(X)$

**证明等价性**:

**Step 1**: 正则局部环刻画。

$\mathcal{O}_{X,P}$ 是正则局部环当且仅当:
$$\dim_k(\mathfrak{m}_P / \mathfrak{m}_P^2) = \dim(\mathcal{O}_{X,P})$$

**Step 2**: 切空间维数。

$$\dim_k T_P(X) = \dim_k(\mathfrak{m}_P / \mathfrak{m}_P^2)^* = \dim_k(\mathfrak{m}_P / \mathfrak{m}_P^2)$$

**Step 3**: 维数关系。

$$\dim_P(X) = \dim(\mathcal{O}_{X,P})$$

**结论**: $\dim T_P(X) = \dim_P(X) \Leftrightarrow \mathcal{O}_{X,P}$ 正则 $\Leftrightarrow X$ 在 $P$ 光滑。

---

#### (c) 概形切空间

**定义**: 对概形 $X$，点 $P$，定义:
$$T_P(X) = \text{Hom}_k(\mathfrak{m}_P / \mathfrak{m}_P^2, k) = (\mathfrak{m}_P / \mathfrak{m}_P^2)^*$$

**与簇情形一致**:

对仿射簇，我们已证:
$$\text{Der}_k(A, k) \cong (\mathfrak{m}_P / \mathfrak{m}_P^2)^*$$

**证明**:

设 $D: A \to k$ 是导子，$D(1) = 0$，故 $D|_{k + \mathfrak{m}_P}$ 由 $D|_{\mathfrak{m}_P}$ 决定。

对 $a, b \in \mathfrak{m}_P$:
$$D(ab) = a(P)D(b) + b(P)D(a) = 0$$

故 $D$ 在 $\mathfrak{m}_P^2$ 上为零，下降为 $\mathfrak{m}_P / \mathfrak{m}_P^2 \to k$ 的线性映射。

反之，给定 $\phi: \mathfrak{m}_P / \mathfrak{m}_P^2 \to k$，定义:
$$D(a) = \phi(a - a(P))$$

验证导子条件成立。

**结论**: 两定义一致。

---

### 计算题目解答

#### (a) 切空间维数

曲线 $X: y^2 = x^3$。

**一般点 $P = (a, b)$ 且 $b \neq 0$ 或 $a \neq 0$**:

Jacobi矩阵:
$$J = \left(\frac{\partial f}{\partial x}, \frac{\partial f}{\partial y}\right) = (-3x^2, 2y)$$

在 $P = (a, b)$:
- 若 $b \neq 0$：$J(P) = (-3a^2, 2b) \neq 0$（因 $2b \neq 0$）
- 若 $a \neq 0$：若 $-3a^2 = 0$ 则 $a = 0$，矛盾

故在一般点，rank$(J) = 1$，切空间维数 = $2 - 1 = 1$。

**原点 $P = (0, 0)$**:

$J(0, 0) = (0, 0)$，rank = 0。

切空间维数 = $2 - 0 = 2$。

**结论**:
- 一般点: $\dim T_P = 1$（曲线维数）
- 原点: $\dim T_P = 2 > 1$

---

#### (b) 奇点集

**奇点**: $\dim T_P > \dim_P(X) = 1$。

由 (a)，只有原点是奇点。

---

#### (c) 切锥

**定义**: 切锥是 $I(X)$ 的最低次齐次部分生成的理想定义的锥。

对 $f = y^2 - x^3$，最低次部分是 $y^2$（次数2）。

切锥: $V(y^2) = V(y)$（二重直线）。

**几何解释**: 在原点附近，$y^2 = x^3 \approx y^2 = 0$，即两重 $x$-轴。

---

## 解题技巧

### 技巧1: 光滑性检验流程

```
检验 X 在 P 的光滑性:
1. 计算 Jacobi 矩阵 J(P)
2. 秩 r = rank(J(P))
3. dim T_P(X) = n - r
4. 比较 dim T_P 与 dim X
相等 → 光滑；不等 → 奇点
```

### 技巧2: 切空间计算要点

| 情形 | 计算方法 |
|:---|:---|
| 仿射簇 | Jacobi矩阵核 |
| 射影簇 | 仿射锥切空间模去径向 |
| 概形 | $(\mathfrak{m}/\mathfrak{m}^2)^*$ |

### 技巧3: 奇点类型速查

| 奇点 | 方程 | 切锥 |
|:---|:---|:---|
| 结点 | $y^2 = x^2(x+1)$ | 两不同直线 |
| 尖点 | $y^2 = x^3$ | 二重直线 |

---

## 变式与推广

### 变式1: 超曲面奇点

设 $X = V(f) \subseteq \mathbb{A}^n$ 是超曲面。

**问题**: 证明 $X$ 在 $P$ 光滑当且仅当存在偏导数在 $P$ 非零。

---

### 变式2: 完全交奇点

设 $X = V(f_1, \ldots, f_r) \subseteq \mathbb{A}^n$，$r < n$。

**问题**: 证明 $X$ 光滑当且仅当Jacobi矩阵满秩。

---

### 变式3: 正规性与光滑性

**问题**: 证明光滑 $\Rightarrow$ 正规，但逆不成立。

**反例**: 曲面 $V(z^2 = xy)$ 在原点是锥点，正规但不光滑。

---

## 相关概念

| 概念 | 定义 | 符号 |
|:---|:---|:---:|
| Zariski切空间 | 导子空间/对偶 | $T_P(X)$ |
| 光滑点 | $\dim T_P = \dim_P X$ | - |
| 奇点 | 非光滑点 | $\text{Sing}(X)$ |
| 切锥 | 最低次部分定义的锥 | $C_P(X)$ |

## 参考文献

1. Hartshorne, R. *Algebraic Geometry*, Ch I, §6
2. Shafarevich, I. *Basic Algebraic Geometry*, Ch II, §1
3. Eisenbud, D. *Commutative Algebra*, Ch 16

---

**创建日期**: 2026-04-10  
**难度**: ⭐⭐⭐  
**预计用时**: 60-90分钟
