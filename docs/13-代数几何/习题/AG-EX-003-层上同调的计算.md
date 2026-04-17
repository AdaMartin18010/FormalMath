---
习题编号: AG-EX-003
标题: 层上同调的计算
类型: 技术型
难度: ⭐⭐⭐
章节: Hartshorne Ch III
对应课程: Harvard Math 232br
预计用时: 90-120分钟
msc: 14F25, 14F40
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

# AG-EX-003: 层上同调的计算

## 题目

### 原题 (Hartshorne III.4.1)

设 $X = \mathbb{P}^1_k$，$\mathcal{F} = \mathcal{O}_X \oplus \mathcal{O}_X(-2)$。计算 $H^i(X, \mathcal{F})$ 对所有 $i \geq 0$。

### 扩展题目

设 $X = \mathbb{P}^n_k$，计算:

**(a)** $H^i(X, \mathcal{O}_X(m))$ 对所有 $i, m$（已知结果）。

**(b)** $H^i(X, \Omega_X^p)$，其中 $\Omega_X^p$ 是 $p$-形式层。

**(c)** 用Čech上同调直接计算 $H^1(\mathbb{P}^1, \mathcal{O}(-2))$。

---

## 解答

### 主题目解答

#### 计算 $H^i(X, \mathcal{F})$

**已知**: $\mathcal{F} = \mathcal{O}_X \oplus \mathcal{O}_X(-2)$

**Step 1: 利用上同调的可加性**

$$H^i(X, \mathcal{F}) = H^i(X, \mathcal{O}_X) \oplus H^i(X, \mathcal{O}_X(-2))$$

**Step 2: 计算 $H^i(X, \mathcal{O}_X)$**

由射影空间的基本定理:

| $i$ | $H^i(\mathbb{P}^1, \mathcal{O}_X)$ | 维数 |
|:---:|:---|:---:|
| 0 | $k$ | 1 |
| 1 | $0$ | 0 |
| $\geq 2$ | $0$ | 0 |

**Step 3: 计算 $H^i(X, \mathcal{O}_X(-2))$**

用Čech上同调。设 $U_0 = \{x_0 \neq 0\}$, $U_1 = \{x_1 \neq 0\}$。

在开集 $U_0 \cong \mathbb{A}^1$，坐标 $t = x_1/x_0$:
$$\mathcal{O}(-2)|_{U_0} = t^{-2} \cdot k[t]$$

在开集 $U_1 \cong \mathbb{A}^1$，坐标 $s = x_0/x_1 = t^{-1}$:
$$\mathcal{O}(-2)|_{U_1} = k[s]$$

**Čech复形**:
$$C^0 = \mathcal{O}(-2)(U_0) \oplus \mathcal{O}(-2)(U_1) = t^{-2}k[t] \oplus k[t^{-1}]$$

$$C^1 = \mathcal{O}(-2)(U_0 \cap U_1) = t^{-2}k[t, t^{-1}]$$

**微分** $d: C^0 \to C^1$:
$$d(f(t), g(t^{-1})) = f(t) - g(t^{-1})$$

（在 $U_0 \cap U_1$ 上 $g(t^{-1}) = g(s)$ 视为 $t$ 的函数）

**计算 $H^0$**: $\ker(d)$

$d(f, g) = 0$ 意味着 $f(t) = g(t^{-1})$ 在 $U_0 \cap U_1$。

$f \in t^{-2}k[t]$ 仅有负幂次到 $-2$。
$g \in k[t^{-1}]$ 仅有非负幂次（在 $t$ 坐标下是 $t$ 的非正幂）。

交集为空，故 $H^0 = 0$。

**计算 $H^1$**: $\text{coker}(d) = C^1 / \text{im}(d)$

$\text{im}(d)$ 包含所有形如 $f(t) - g(t^{-1})$ 的元素。

$t^{-2}k[t, t^{-1}]$ 的基为 $\{t^n : n \geq -2\}$。

$f(t) \in t^{-2}k[t]$ 提供 $\{t^n : n \geq -2\}$（有限个正幂）
$g(t^{-1}) \in k[t^{-1}]$ 提供 $\{t^n : n \leq 0\}$

并集覆盖 $\{t^n : n \geq -2\} \cup \{t^n : n \leq 0\} = \{t^n : n \in \mathbb{Z}\}$ 除了 $t^{-1}$。

**结论**: $H^1 = k \cdot t^{-1} \cong k$，维数为1。

**Step 4: 汇总**

| $i$ | $H^i(\mathbb{P}^1, \mathcal{O}(-2))$ | 维数 |
|:---:|:---|:---:|
| 0 | $0$ | 0 |
| 1 | $k$ | 1 |
| $\geq 2$ | $0$ | 0 |

**Step 5: 最终答案**

| $i$ | $H^i(X, \mathcal{F})$ | 维数 |
|:---:|:---|:---:|
| 0 | $k$ | 1 |
| 1 | $k$ | 1 |
| $\geq 2$ | $0$ | 0 |

---

### 扩展题目解答

#### (a) $H^i(\mathbb{P}^n, \mathcal{O}(m))$

**定理** (Hartshorne III.5.1):

$$h^i(\mathbb{P}^n, \mathcal{O}(m)) = \begin{cases} \binom{m+n}{n} & i = 0, m \geq 0 \\ \binom{-m-1}{n} & i = n, m \leq -(n+1) \\ 0 & \text{其他情况} \end{cases}$$

**记忆口诀**: 
- $H^0$: 只有非负扭转有截面
- $H^n$: Serre对偶，$H^n(\mathcal{O}(m)) \cong H^0(\mathcal{O}(-m-n-1))^*$

---

#### (b) $H^i(\mathbb{P}^n, \Omega^p)$

**Bott消失定理**:

$$H^i(\mathbb{P}^n, \Omega^p(m)) = 0$$

除非:
- $i = 0$ 且 $m > p$
- $i = n$ 且 $m < p - n$
- $i = p$ 且 $m = 0$

**特例**:
- $H^i(\mathbb{P}^n, \Omega^p) = \begin{cases} k & i = p \\ 0 & i \neq p \end{cases}$

几何意义: $\Omega^p$ 的拓扑上同调。

---

#### (c) Čech直接计算 $H^1(\mathbb{P}^1, \mathcal{O}(-2))$

已在主题目中完成，答案是 $k$（1维）。

**关键观察**: $t^{-1}$ 是唯一的"间隙"，不能由 $C^0$ 的像覆盖。

---

## 解题技巧

### 技巧1: 射影直线上同调速查

```
┌────────────────────────────────────────────────┐
│  h^i(P^1, O(m))                                │
├────────────────────────────────────────────────┤
│  m ≥ 0:  h^0 = m+1,  h^1 = 0                   │
│  m = -1: h^0 = 0,    h^1 = 0                   │
│  m ≤ -2: h^0 = 0,    h^1 = -m-1                │
└────────────────────────────────────────────────┘
```

### 技巧2: Čech计算要点

1. **选覆盖**: 仿射开覆盖 $U_i = \{x_i \neq 0\}$
2. **写复形**: $C^p = \bigoplus \mathcal{F}(U_{i_0} \cap \cdots \cap U_{i_p})$
3. **算微分**: 交错和限制映射
4. **求上同调**: $\ker/\text{im}$

### 技巧3: Serre对偶应用

对 $\mathbb{P}^1$:
$$H^1(\mathcal{O}(m)) \cong H^0(\mathcal{O}(-2-m))^*$$

验证:
- $m = -2$: $H^1(\mathcal{O}(-2)) \cong H^0(\mathcal{O})^* = k^* = k$ ✓

---

## 变式与推广

### 变式1: 一般线丛

设 $L = \mathcal{O}(d_1) \oplus \cdots \oplus \mathcal{O}(d_r)$ 是 $\mathbb{P}^1$ 上的分裂线丛。

**问题**: 计算 $h^i(L)$ 用 $d_j$ 表示。

---

### 变式2: 乘积空间

计算 $H^i(\mathbb{P}^1 \times \mathbb{P}^1, \mathcal{O}(a,b))$。

**提示**: Künneth公式。

---

### 变式3: 椭圆曲线

设 $E$ 是椭圆曲线，$L$ 是 $d$ 次线丛。

**问题**: 用Riemann-Roch计算 $h^0(L)$。

---

## 相关概念

| 概念 | 定义 | 符号 |
|:---|:---|:---:|
| 层上同调 | 整体截面函子的导出函子 | $H^i(X, \mathcal{F})$ |
| Čech上同调 | 用开覆盖计算的同调 | $\check{H}^i(\mathcal{U}, \mathcal{F})$ |
| Serre对偶 | $H^i(\mathcal{F}) \cong H^{n-i}(\omega \otimes \mathcal{F}^\vee)^*$ | - |
| Bott消失 | 正合序列的消没 | - |

## 参考文献

1. Hartshorne, R. *Algebraic Geometry*, Ch III, §4-5
2. Bott, R. *Homogeneous Vector Bundles*
3. Voisin, C. *Hodge Theory and Complex Algebraic Geometry*, Ch 4

---

**创建日期**: 2026-04-10  
**难度**: ⭐⭐⭐  
**预计用时**: 90-120分钟
