---
习题编号: AG-EX-002
标题: 投影空间中的曲线
类型: 计算型
难度: ⭐⭐⭐
章节: Hartshorne Ch I
对应课程: Harvard Math 232br
预计用时: 60-90分钟
msc: 14H50, 14N05
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

# AG-EX-002: 投影空间中的曲线

## 题目

### 原题 (Hartshorne I.3.4)

设 $C \subseteq \mathbb{P}^3$ 是扭曲三次曲线，定义为映射:
$$\phi: \mathbb{P}^1 \to \mathbb{P}^3, \quad [s:t] \mapsto [s^3 : s^2t : st^2 : t^3]$$

**(a)** 证明 $C$ 的理想 $I(C)$ 由以下三个二次型生成:
$$Q_0 = x_0x_2 - x_1^2, \quad Q_1 = x_0x_3 - x_1x_2, \quad Q_2 = x_1x_3 - x_2^2$$

**(b)** 证明 $C$ 不能由两个二次超曲面交定义（即不是完全交）。

### 变式题目

设 $C_d \subseteq \mathbb{P}^d$ 是 $d$-次有理正规曲线:
$$[s:t] \mapsto [s^d : s^{d-1}t : \cdots : st^{d-1} : t^d]$$

**(a)** 求 $C_d$ 的Hilbert函数。

**(b)** 计算 $C_d$ 的次数和亏格。

---

## 解答

### 主题目解答

#### (a) 理想生成元

**Step 1: 验证生成元在 $C$ 上为零**

对 $[s:t] \in \mathbb{P}^1$，像点为 $[x_0:x_1:x_2:x_3] = [s^3:s^2t:st^2:t^3]$。

验证:
- $Q_0 = s^3 \cdot st^2 - (s^2t)^2 = s^4t^2 - s^4t^2 = 0$ ✓
- $Q_1 = s^3 \cdot t^3 - s^2t \cdot st^2 = s^3t^3 - s^3t^3 = 0$ ✓
- $Q_2 = s^2t \cdot t^3 - (st^2)^2 = s^2t^4 - s^2t^4 = 0$ ✓

**Step 2: 证明 $I(C) = (Q_0, Q_1, Q_2)$**

设 $V = V(Q_0, Q_1, Q_2)$。需证 $V = C$。

**证明 $C \subseteq V$**: 已验证。

**证明 $V \subseteq C$**: 设 $[x_0:x_1:x_2:x_3] \in V$。

**情形1**: $x_0 \neq 0$。不妨设 $x_0 = 1$。

由 $Q_0 = 0$: $x_2 = x_1^2$

由 $Q_1 = 0$: $x_3 = x_1x_2 = x_1^3$

令 $t = x_1$，则点为 $[1:t:t^2:t^3] = [s^3:s^2t:st^2:t^3]$（取 $s=1$）。

**情形2**: $x_0 = 0$。

由 $Q_0 = 0$: $x_1 = 0$
由 $Q_1 = 0$: 自动满足
由 $Q_2 = 0$: $x_2 = 0$（若 $x_3 \neq 0$）

点为 $[0:0:0:1]$，对应 $[s:t] = [0:1]$。

**结论**: $V = C$，故 $I(C) = (Q_0, Q_1, Q_2)$。

---

#### (b) $C$ 不是完全交

**定义**: 完全交是指可由 $	ext{codim}(C) = 2$ 个方程定义的曲线。

**证明**: 假设 $C = H_1 \cap H_2$，其中 $H_1, H_2$ 是二次超曲面。

**Step 1**: 若 $C = H_1 \cap H_2$，则 $I(C) = (F_1, F_2)$（由两个二次型生成）。

**Step 2**: 计算Hilbert函数。

$I(C)$ 的Hilbert函数:
- $h(0) = 1$（常数）
- $h(1) = 4$（所有一次型模去零）
- $h(2) = \binom{5}{2} - 3 = 7$（$\binom{5}{2}=10$ 个二次型，3个关系）

若由两个二次型生成，则Hilbert级数为:
$$\frac{(1-t^2)^2}{(1-t)^4} = \frac{(1+t)^2}{(1-t)^2}$$

展开得 $h(2) = 8$，矛盾！（实际为7）

**结论**: $C$ 不是完全交。

---

### 变式题目解答

#### (a) Hilbert函数

$C_d$ 由齐次坐标环 $k[x_0, \ldots, x_d]/I(C_d)$ 描述。

$I(C_d)$ 由所有 $2 \times 2$ 子式生成:
$$\det\begin{pmatrix} x_i & x_j \\ x_k & x_l \end{pmatrix} = 0, \quad i+j = k+l$$

Hilbert函数 $h(n) = \dim_k (S/I)_n$:

对有理正规曲线，曲线参数化为 $[s^d : s^{d-1}t : \cdots : t^d]$。

齐次坐标环同构于 $k[s^d, s^{d-1}t, \ldots, t^d] \subseteq k[s,t]$。

**关键观察**: $n$ 次齐次元对应 $k[s,t]$ 中 $nd$ 次齐次元。

$$h(n) = nd + 1$$

**Hilbert多项式**: $P(n) = nd + 1$

---

#### (b) 次数和亏格

**次数**: Hilbert多项式的首项系数乘以 $(\deg P)!$。

$P(n) = dn + 1$，故 $\deg(C_d) = d$。

**亏格**: 对有理曲线，同构于 $\mathbb{P}^1$，故亏格 $g = 0$。

也可用Riemann-Roch验证:
$$\chi(\mathcal{O}_{C_d}) = 1 - g = 1$$

**结论**: 
- 次数: $\deg(C_d) = d$
- 亏格: $g(C_d) = 0$

---

## 解题技巧

### 技巧1: 参数曲线的理想计算

```
参数曲线 [f_0(s,t) : ... : f_n(s,t)] 的理想求法:

1. 找出所有多项式关系（消元）
2. 验证生成元完备性
3. 用Hilbert函数检验
```

### 技巧2: 完全交的判别

**必要条件**: 若 $X$ 是余维 $r$ 的完全交，则:
- $I(X)$ 可由 $r$ 个元素生成
- Hilbert级数为 $(1-t^{d_1})\cdots(1-t^{d_r})/(1-t)^{n+1}$

**扭曲三次反例**: 余维2，但需3个生成元。

### 技巧3: Hilbert函数计算

```
Hilbert函数 h(n) = dim (S/I)_n

计算方法:
- 直接: 找商空间的基
- 级数: Hilbert级数展开
- 几何: 与线丛的截面联系
```

---

## 变式与推广

### 变式1: Veronese嵌入

考虑Veronese映射 $v_d: \mathbb{P}^1 \to \mathbb{P}^d$。

**问题**: 证明像的Hilbert函数为 $h(n) = dn + 1$。

---

### 变式2: 一般有理曲线

设 $C \subseteq \mathbb{P}^3$ 是一般三次曲线。

**问题**: 证明它是完全交（由二次和三次曲面定义）。

---

### 变式3: 曲线在 $\mathbb{P}^2$ 中的嵌入

**问题**: 证明 $\mathbb{P}^1$ 到 $\mathbb{P}^2$ 的 $d$ 次嵌入像是光滑平面曲线当且仅当 $d \leq 2$。

---

## 相关概念

| 概念 | 说明 | 公式 |
|:---|:---|:---:|
| 有理正规曲线 | $\mathbb{P}^1$ 的 $d$-次嵌入 | $[s^d:...:t^d]$ |
| 扭曲三次 | $d=3$ 情形 | 不是完全交 |
| Hilbert函数 | 分次分量的维数 | $h(n) = \dim (S/I)_n$ |
| 完全交 | 由余维数个方程定义 | $I = (f_1, ..., f_r)$ |

## 参考文献

1. Hartshorne, R. *Algebraic Geometry*, Ch I, §3, Exercise 3.4
2. Harris, J. *Algebraic Geometry*, Lecture 14
3. Eisenbud, D. *Commutative Algebra*, Ch 15

---

**创建日期**: 2026-04-10  
**难度**: ⭐⭐⭐  
**预计用时**: 60-90分钟
