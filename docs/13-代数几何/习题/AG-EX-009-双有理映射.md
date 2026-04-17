---
习题编号: AG-EX-009
标题: 双有理映射
类型: 综合型
难度: ⭐⭐⭐⭐
章节: Hartshorne Ch I/IV
对应课程: Harvard Math 232br
预计用时: 90-120分钟
msc: 14E05, 14E07
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

# AG-EX-009: 双有理映射

## 题目

### 原题 (Hartshorne I.4.3 + IV.5.1)

设 $X, Y$ 是簇，$\phi: X \dashrightarrow Y$ 是有理映射。

**(a)** 证明 $\phi$ 是双有理的当且仅当存在非空开集 $U \subseteq X$, $V \subseteq Y$ 使得 $\phi|_U: U \to V$ 是同构。

**(b)** 证明曲线 $X$ 双有理等价于光滑射影曲线 $Y$ 当且仅当 $k(X) \cong k(Y)$（函数域同构）。

**(c)** 证明任何曲线都双有理等价于唯一的（同构意义下）光滑射影曲线（非奇异模型）。

### 应用题目

设 $C$ 是平面曲线 $y^2 = x^3$（尖点三次曲线）。

**(a)** 证明 $C$ 双有理等价于 $\mathbb{P}^1$。

**(b)** 找出具体的有理映射 $C \dashrightarrow \mathbb{P}^1$ 和逆。

**(c)** 说明为什么这不是同构。

---

## 解答

### 主题目解答

#### (a) 双有理的等价刻画

**定义**: $\phi: X \dashrightarrow Y$ 双有理是指存在 $\psi: Y \dashrightarrow X$ 使得 $\psi \circ \phi = \text{id}_X$，$\phi \circ \psi = \text{id}_Y$（作为有理映射）。

**证明**:

**($\Rightarrow$)** 设 $\phi$ 双有理，逆为 $\psi$。

$\phi$ 和 $\psi$ 在开集 $U_0 \subseteq X$，$V_0 \subseteq Y$ 是态射。

设 $U_1 = \phi^{-1}(V_0) \cap U_0$，$V_1 = \psi^{-1}(U_0) \cap V_0$。

在 $U = U_1 \cap \psi(V_1)$ 上:
$$\psi \circ \phi = \text{id}_U$$

类似定义 $V$，则 $\phi: U \to V$ 是同构。

**($\Leftarrow$)** 设 $\phi: U \to V$ 是同构，逆为 $\psi: V \to U$。

$\psi$ 作为有理映射 $Y \dashrightarrow X$，与 $\phi$ 互为逆。

---

#### (b) 曲线的函数域刻画

**定理**: 曲线 $X, Y$ 双有理等价 $\Leftrightarrow k(X) \cong k(Y)$。

**证明**:

**($\Rightarrow$)** 双有理映射诱导函数域同构。

设 $\phi: X \dashrightarrow Y$ 双有理，则在开集上 $\phi^*: k(Y) \to k(X)$ 是域同态。

逆有理映射给出逆同态。

**($\Leftarrow$)** 函数域同构诱导双有理映射。

设 $\sigma: k(Y) \to k(X)$ 是同构。

$k(Y) = k(y_1, \ldots, y_n)$，$\sigma(y_i) \in k(X)$ 是有理函数。

定义 $\phi: X \dashrightarrow Y$ 为 $\phi^*(y_i) = \sigma(y_i)$。

这是有理映射，且 $(\phi^{-1})^* = \sigma^{-1}$ 给出逆。

---

#### (c) 非奇异模型的存在唯一性

**存在性**:

对曲线 $C$，$k(C)$ 是1维函数域。

由代数函数域理论，存在光滑射影曲线 $C'$ 使得 $k(C') = k(C)$。

由 (b)，$C$ 与 $C'$ 双有理等价。

**唯一性**:

设 $C_1, C_2$ 都是光滑射影曲线，双有理等价。

双有理映射 $\phi: C_1 \dashrightarrow C_2$ 在光滑射影曲线间是有理函数。

由曲线上的有理函数延拓定理，$\phi$ 可延拓为态射 $\tilde{\phi}: C_1 \to C_2$。

同理有逆态射，故 $C_1 \cong C_2$。

**结论**: 非奇异模型在同构意义下唯一。

---

### 应用题目解答

#### (a) $C$ 双有理等价于 $\mathbb{P}^1$

曲线 $C: y^2 = x^3$。

**函数域**:
$$k(C) = k(x, y) / (y^2 - x^3) = k(x)[y] / (y^2 - x^3)$$

**参数化**:

令 $t = y/x$，则:
$$t^2 = y^2/x^2 = x^3/x^2 = x$$

故 $x = t^2$，$y = t^3$。

$$k(C) = k(t^2, t^3) = k(t)$$

因为 $t = y/x \in k(C)$，且 $x, y \in k(t)$。

**结论**: $k(C) \cong k(t) = k(\mathbb{P}^1)$，故双有理等价。

---

#### (b) 具体有理映射

**映射 $\phi: C \dashrightarrow \mathbb{P}^1$**:

$$\phi(x, y) = [x : y] = [1 : y/x] = [1 : t]$$

或齐次形式:
$$\phi([X:Y:Z]) = [XZ : YZ]$$

（在仿射开集 $Z = 1$ 上是 $(x, y) \mapsto [x : y]$）

**逆映射 $\psi: \mathbb{P}^1 \dashrightarrow C$**:

$$\psi([s:t]) = (t^2/s^2, t^3/s^3) = [s^3 : t^3 : s^2t]$$

（在仿射开集 $s = 1$ 上是 $t \mapsto (t^2, t^3)$）

**验证**:
- $\psi \circ \phi(x, y) = \psi([x:y]) = (y^2/x^2, y^3/x^3) = (x, y)$（因 $y^2 = x^3$）
- $\phi \circ \psi(t) = \phi(t^2, t^3) = [t^2 : t^3] = [1 : t]$

---

#### (c) 非同构的原因

**$C$ 不光滑**: 在原点 $(0, 0)$，Jacobi矩阵:
$$J = (-3x^2, 2y)|_{(0,0)} = (0, 0)$$

故 $(0, 0)$ 是奇点（尖点）。

**$\mathbb{P}^1$ 光滑**: 处处光滑。

**双有理等价但不同构**: 

- 光滑射影曲线双有理等价则同构
- $C$ 不光滑，故不能与 $\mathbb{P}^1$ 同构
- 双有理等价通过"解开"奇点实现

---

## 解题技巧

### 技巧1: 双有理判据

```
┌─────────────────────────────────────────┐
│  双有理等价的等价条件:                  │
│  1. 存在开集同构                        │
│  2. 函数域同构                          │
│  3. 有理映射互逆                        │
│                                         │
│  曲线情形: 双有理 ⇔ 函数域同构          │
└─────────────────────────────────────────┘
```

### 技巧2: 有理参数化方法

对曲线 $C$，找参数化的步骤:
1. 找曲线上的点 $P$
2. 考虑过 $P$ 的直线束
3. 另一交点给出参数化

**尖点三次**: 过原点直线 $y = tx$，代入 $t^2x^2 = x^3$，得 $x = t^2$，$y = t^3$。

### 技巧3: 奇点消解与双有理等价

```
奇点曲线 C --(爆破)--> 光滑曲线 C'
     ↓                    ↓
  双有理等价            同构
     ↓                    ↓
   k(C) = k(C') ≅ k(P^1)（有理曲线情形）
```

---

## 变式与推广

### 变式1: 结三次曲线

设 $C: y^2 = x^2(x+1)$（结点三次）。

**问题**: 证明 $C$ 双有理等价于 $\mathbb{P}^1$，找出参数化。

**提示**: 类似方法，参数化 $t = y/x$，得 $x = t^2 - 1$，$y = t(t^2 - 1)$。

---

### 变式2: 椭圆曲线非有理

设 $E: y^2 = x(x-1)(x-\lambda)$，$\lambda \neq 0, 1$。

**问题**: 证明 $E$ 不双有理等价于 $\mathbb{P}^1$。

**提示**: 证明 $k(E)$ 不是纯超越扩张，或证明 $g(E) = 1 \neq 0 = g(\mathbb{P}^1)$。

---

### 变式3: 高维双有理几何

**问题**: 证明 $\mathbb{P}^2$ 双有理等价于 $\mathbb{P}^1 \times \mathbb{P}^1$。

**构造**: 
- $\mathbb{P}^2$ 爆破一点 $\cong$ $\mathbb{P}^1$-丛 over $\mathbb{P}^1$
- 同构于 $\mathbb{P}^1 \times \mathbb{P}^1$ 爆破一点

---

## 相关概念

| 概念 | 定义 | 符号 |
|:---|:---|:---:|
| 有理映射 | 开集上的态射 | $\phi: X \dashrightarrow Y$ |
| 双有理等价 | 存在互逆有理映射 | $X \sim Y$ |
| 函数域 | 有理函数域 | $k(X)$ |
| 非奇异模型 | 光滑代表元 | - |

## 参考文献

1. Hartshorne, R. *Algebraic Geometry*, Ch I, §4
2. Shafarevich, I. *Basic Algebraic Geometry*, Ch II, §4
3. Beauville, A. *Complex Algebraic Surfaces*, Ch V

---

**创建日期**: 2026-04-10  
**难度**: ⭐⭐⭐⭐  
**预计用时**: 90-120分钟
