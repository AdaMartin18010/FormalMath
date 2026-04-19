---
习题编号: AG-EX-012
标题: 平坦态射判别
类型: 技术型
难度: ⭐⭐⭐⭐
章节: Hartshorne Ch III
对应课程: Harvard Math 232br
预计用时: 120-150分钟
msc: 14D20, 14B12
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

# AG-EX-012: 平坦态射判别

## 题目

### 原题 (Hartshorne III.9.1-3)

设 $f: X \to Y$ 是概形态射，$\mathcal{F}$ 是 $X$ 上凝聚层。

**(a)** 证明若 $f$ 是有限型的，$Y$ 是Noether的，则平坦性可在纤维上检验。

**(b)** 设 $Y = \text{Spec}(k[t])$，$X = V(xy - t) \subseteq \mathbb{A}^2 \times \mathbb{A}^1$。证明投射 $f: X \to Y$ 是平坦的。

**(c)** 设 $Y = \text{Spec}(k[t])$，$X = V(xy, t) \subseteq \mathbb{A}^2 \times \mathbb{A}^1$。证明 $f: X \to Y$ 不是平坦的。

### 应用题目

设 $f: X \to Y$ 是族曲线。

**(a)** 证明若 $f$ 是平坦的，则几何纤维的算术亏格恒定。

**(b)** 验证 (b) 中的族 $xy = t$ 的纤维亏格。

**(c)** 用平坦性解释为什么 $xy = t$ 比 $xy = 0$ "更好"。

---

## 解答

### 主题目解答

#### (a) 平坦性的纤维判别

**定理**: 设 $f: X \to Y$ 有限型，$Y$ Noether，$\mathcal{F}$ 凝聚。则以下条件等价:

1. $\mathcal{F}$ 在 $Y$ 上平坦
2. 对所有 $y \in Y$，$\mathcal{F}_y$ 在 $\mathcal{O}_{Y,y}$ 上平坦
3. 对所有 $y \in Y$，$H^0(X_y, \mathcal{F}_y)$ 在 $k(y)$ 上维数局部恒定

**证明概要**:

**Step 1**: (1) $\Rightarrow$ (2) 是平坦性的基变换。

**Step 2**: (2) $\Rightarrow$ (3) 用平坦基变换。

**Step 3**: (3) $\Rightarrow$ (1) 用局部判别法（Hilbert多项式恒定）。

---

#### (b) $xy = t$ 族是平坦的

**设定**:

- $Y = \text{Spec}(k[t]) = \mathbb{A}^1$
- $X = \text{Spec}(k[x,y,t]/(xy - t))$
- $f: X \to Y$ 是投射

**证明平坦性**:

**Step 1**: 计算纤维。

对 $t_0 \in k$，纤维:
$$X_{t_0} = \text{Spec}(k[x,y]/(xy - t_0))$$

- $t_0 \neq 0$: $xy = t_0$ 是光滑双曲线（亏格0，1个点无穷远）
- $t_0 = 0$: $xy = 0$ 是两直线并（结点曲线）

**Step 2**: 验证Hilbert多项式恒定。

$X$ 在 $\mathbb{A}^2 \times \mathbb{A}^1$ 中由1个方程定义，是余维1。

作为 $t$ 的函数，Hilbert多项式不变。

**Step 3**: 用代数判别。

$k[x,y,t]/(xy - t) \cong k[x,y]$（消去 $t = xy$）。

这是自由 $k[t]$-模？不是，但:

局部看，在 $(x, y, t)$ 附近，$xy = t$ 给出正则局部环。

$k[x,y,t]/(xy-t)$ 在 $k[t]$ 上平坦因为:

- 作为 $k[t]$-模，它是整的
- $t$ 不是零因子

**结论**: $f$ 平坦。

---

#### (c) $xy = t = 0$ 族非平坦

**设定**:

- $X = \text{Spec}(k[x,y,t]/(xy, t)) = \text{Spec}(k[x,y]/(xy))$
- $f: X \to Y = \text{Spec}(k[t])$

**证明非平坦**:

**Step 1**: 纤维分析。

- $t \neq 0$: 纤维为空（因 $t = 0$ 在 $X$ 上）
- $t = 0$: 纤维为 $xy = 0$（两直线）

**Step 2**: Hilbert多项式跳跃。

纤维维数从 $-\infty$（空）跳到1。

**Step 3**: 代数判别。

$k[x,y]/(xy)$ 作为 $k[t]$-模，$t$ 作用为0。

$t$ 是零因子（零乘），故不平坦。

**结论**: $f$ 不平坦。

---

### 应用题目解答

#### (a) 平坦族的亏格恒定

**定理**: 设 $f: X \to Y$ 是平坦固有族曲线，则算术亏格 $p_a(X_y)$ 在 $Y$ 上局部恒定。

**证明**:

由平坦基变换:
$$R^i f_* \mathcal{O}_X \otimes k(y) \cong H^i(X_y, \mathcal{O}_{X_y})$$

$R^i f_* \mathcal{O}_X$ 是局部自由层（因 $Y$ 上平坦）。

故 $\dim H^i(X_y, \mathcal{O}_{X_y})$ 局部恒定。

算术亏格:
$$p_a(X_y) = 1 - \chi(\mathcal{O}_{X_y}) = 1 - h^0 + h^1$$

是局部恒定的。

---

#### (b) $xy = t$ 族的亏格

对 $t \neq 0$:

$xy = t$ 是双曲线，同构于 $\mathbb{P}^1 \setminus \{2\text{点}\}$。

光滑完备化为 $\mathbb{P}^1$，亏格0。

对 $t = 0$:

$xy = 0$ 是两直线，奇异。

算术亏格: $p_a = 1 - \chi = 1 - (1 - 0) = 0$。

**结论**: 亏格恒为0，平坦性一致。

---

#### (c) 平坦性的几何意义

**$xy = t$（平坦）**:
- 纤维几何连续变化
- $t \to 0$ 是光滑双曲线 $\to$ 结点曲线（极限良好）
- 保持拓扑性质

**$xy = 0$（非平坦）**:
- 所有纤维信息集中在 $t = 0$
- 没有"附近"纤维
- 无法讨论形变

**结论**: 平坦性保证族的良好连续性。

---

## 解题技巧

### 技巧1: 平坦性判别速查

```
┌─────────────────────────────────────────┐
│  平坦性判别:                            │
│  1. 自由模 ⇒ 平坦                       │
│  2. 局部自由层 ⇒ 平坦                   │
│  3. Hilbert多项式恒定 ⇒ 平坦            │
│  4. 纤维维数跳跃 ⇒ 非平坦               │
│  5. 零因子 ⇒ 非平坦                     │
└─────────────────────────────────────────┘
```

### 技巧2: 平坦族的性质

平坦族保持:
- Hilbert多项式
- 算术亏格
-  Euler示性数
- 某些数值不变量

### 技巧3: 非平坦的典型例子

```
非平坦族的典型:
├─ 锥的闭点: 所有纤维塌缩到一点
├─ 方程含参数不可消去
└─ 维数跳跃的族
```

---

## 变式与推广

### 变式1: 一般超曲面族

设 $f: X \to Y$ 是超曲面族，由 $F(x, t) = 0$ 定义。

**问题**: 证明 $f$ 平坦当且仅当 $F$ 对所有 $t$ 非零。

---

### 变式2: Hilbert概形与平坦性

Hilbert概形 $H$ 上的万有族 $Z \subseteq \mathbb{P}^n \times H$。

**问题**: 证明投射 $Z \to H$ 是平坦的。

---

### 变式3: 形变理论

平坦族是代数几何中形变理论的框架。

**问题**: 用平坦性定义一阶形变空间 $T^1$。

---

## 相关概念

| 概念 | 定义 | 符号 |
|:---|:---|:---:|
| 平坦模 | 张量积正合 | - |
| 平坦态射 | 局部平坦 | - |
| 纤维 | 点的原像 | $X_y$ |
| 算术亏格 | $1 - \chi(\mathcal{O})$ | $p_a$ |

## 参考文献

1. Hartshorne, R. *Algebraic Geometry*, Ch III, §9
2. Matsumura, H. *Commutative Ring Theory*, Ch 8
3. Vakil, R. *The Rising Sea*, Ch 24

---

**创建日期**: 2026-04-10  
**难度**: ⭐⭐⭐⭐  
**预计用时**: 120-150分钟
