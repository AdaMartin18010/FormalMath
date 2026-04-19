---
习题编号: AG-EX-015
标题: 代数几何与数论
类型: 跨学科
难度: ⭐⭐⭐⭐
章节: Hartshorne Ch I/IV
对应课程: Harvard Math 232br
预计用时: 120-150分钟
msc: 14G10, 11G30
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
review_status: draft
---

# AG-EX-015: 代数几何与数论

## 题目

### 原题 (基于Diophantine几何主题)

设 $k$ 是数域（如 $\mathbb{Q}$），$X$ 是 $k$ 上的代数簇。

**(a)** (Mordell猜想/Faltings定理) 设 $C$ 是定义在数域 $k$ 上的亏格 $g \geq 2$ 的曲线。证明 $C(k)$（$k$-有理点集）是有限的。

**(b)** 对椭圆曲线 $E/\mathbb{Q}$，描述Mordell-Weil群 $E(\mathbb{Q})$ 的结构。

**(c)** 设 $C: y^2 = x^3 - x$ 定义在 $\mathbb{F}_p$ 上。计算 $|C(\mathbb{F}_p)|$ 对 $p = 3, 5, 7$。

### 应用题目

设 $E$ 是定义在 $\mathbb{Q}$ 上的椭圆曲线。

**(a)** 解释Hasse原理对二次型的有效性，以及对椭圆曲线的失效。

**(b)** 对 $E: y^2 = x^3 - x$，计算实点 $E(\mathbb{R})$ 的连通分支数。

**(c)** 描述BSD猜想（Birch and Swinnerton-Dyer）对 $L(E, s)$ 在 $s = 1$ 的行为。

---

## 解答

### 主题目解答

#### (a) Mordell猜想/Faltings定理

**定理** (Faltings, 1983): 设 $C$ 是数域 $k$ 上亏格 $g \geq 2$ 的光滑曲线，则 $C(k)$ 有限。

**证明概要**:

**Step 1**: 约化到Jacobian。

设 $J = \text{Jac}(C)$ 是 $C$ 的Jacobian，是 $g$ 维Abel簇。

嵌入 $C \hookrightarrow J$（Abel-Jacobi映射）。

**Step 2**: Mordell-Weil定理。

$J(k)$ 是有限生成Abel群（秩有限，挠有限）。

**Step 3**: Faltings关键结果。

子簇的交性质: 若 $X \subseteq J$ 是子簇，则 $X(k)$ 的Zariski闭包有良好控制。

特别，对曲线 $C \subseteq J$，若 $C(k)$ 无限，则 $C$ 是Abel子簇的平移，不可能（因 $g \geq 2$）。

**结论**: $C(k)$ 有限。

---

#### (b) Mordell-Weil群结构

**定理** (Mordell-Weil): 设 $E/k$ 是椭圆曲线，则:
$$E(k) \cong \mathbb{Z}^r \oplus E(k)_{\text{tors}}$$

其中:
- $r = \text{rank}(E(k))$ 是非负整数（秩）
- $E(k)_{\text{tors}}$ 是有限挠子群

**已知结果**:

Mazur定理: $E(\mathbb{Q})_{\text{tors}}$ 只有有限可能:
$$\mathbb{Z}/n\mathbb{Z}, \quad n = 1, \ldots, 10, 12$$
$$\mathbb{Z}/2\mathbb{Z} \times \mathbb{Z}/2n\mathbb{Z}, \quad n = 1, \ldots, 4$$

**秩的分布**: 猜想一半曲线秩为0，一半秩为1，更高秩稀少。

---

#### (c) 有限域上的点计数

曲线 $C: y^2 = x^3 - x$ 在 $\mathbb{F}_p$ 上。

**$p = 3$**:

$x \in \{0, 1, 2\}$
- $x = 0$: $y^2 = 0$，$y = 0$（1点）
- $x = 1$: $y^2 = 0$，$y = 0$（1点）
- $x = 2$: $y^2 = 2^3 - 2 = 6 = 0$，$y = 0$（1点）

无穷远点: 1点

总数: $|C(\mathbb{F}_3)| = 4$

**$p = 5$**:

$x \in \{0, 1, 2, 3, 4\}$
- $x = 0$: $y^2 = 0$，$y = 0$（1点）
- $x = 1$: $y^2 = 0$，$y = 0$（1点）
- $x = 2$: $y^2 = 6 = 1$，$y = \pm 1$（2点）
- $x = 3$: $y^2 = 24 = 4$，$y = \pm 2$（2点）
- $x = 4$: $y^2 = 60 = 0$，$y = 0$（1点）

无穷远点: 1点

总数: $|C(\mathbb{F}_5)| = 8$

**$p = 7$**:

类似计算（QR: 1, 2, 4 是平方；3, 5, 6 非平方）:
- $x = 0$: 1点
- $x = 1$: 1点
- $x = 2$: $y^2 = 6$（非QR，0点）
- $x = 3$: $y^2 = 24 = 3$（非QR，0点）
- $x = 4$: $y^2 = 60 = 4$（QR，2点）
- $x = 5$: $y^2 = 120 = 1$（QR，2点）
- $x = 6$: $y^2 = 210 = 0$（1点）

无穷远点: 1点

总数: $|C(\mathbb{F}_7)| = 8$

---

### 应用题目解答

#### (a) Hasse原理

**定义**: Hasse原理成立是指局部可解（所有完备化有解）蕴含整体可解。

**二次型** (Hilbert-Speiser):

Hasse-Minkowski定理: 二次型的局部-整体原理成立。

**椭圆曲线**:

Hasse原理**失效**！

**反例**: Selmer曲线 $3x^3 + 4y^3 + 5z^3 = 0$。

- 局部处处可解
- 无有理点

**解释**: 椭圆曲线的Tate-Shafarevich群 $\text{Sha}(E/\mathbb{Q})$ 测量Hasse原理的失效。

---

#### (b) 实点连通分支

曲线 $E: y^2 = x^3 - x = x(x-1)(x+1)$。

**实根**: $x = -1, 0, 1$。

**分支分析**:

- $x < -1$: $y^2 < 0$（无实点）
- $-1 < x < 0$: $y^2 > 0$（两点）
- $0 < x < 1$: $y^2 < 0$（无实点）
- $x > 1$: $y^2 > 0$（两点）

**连通分支**:

$E(\mathbb{R})$ 有**两个**连通分支:
1. 紧致分支: $-1 \leq x \leq 0$
2. 非紧致分支: $x \geq 1$（连通到无穷远点）

**拓扑**: $E(\mathbb{R}) \cong S^1 \sqcup S^1$（两个圆）。

---

#### (c) BSD猜想

**设定**:

$L(E, s)$ 是椭圆曲线的Hasse-Weil $L$-函数。

**BSD猜想**:

$$\text{ord}_{s=1} L(E, s) = \text{rank}(E(\mathbb{Q}))$$

且首项系数:
$$L^*(E, 1) = \frac{\Omega_E \cdot \text{Reg}(E) \cdot |\text{Sha}(E)| \cdot \prod_p c_p}{|E(\mathbb{Q})_{\text{tors}}|^2}$$

**其中**:
- $\Omega_E$: 周期
- $\text{Reg}$: 调节子（高度配对的行列式）
- $\text{Sha}$: Tate-Shafarevich群
- $c_p$: Tamagawa数

**现状**:

- 秩0和秩1情形: 大部分已知（Gross-Zagier, Kolyvagin）
- 高秩: 猜想为主
-  Millennium Prize Problem 之一

---

## 解题技巧

### 技巧1: 有限域点计数

```
┌─────────────────────────────────────────┐
│  F_p 上椭圆曲线的点计数:                │
│  |E(F_p)| = 1 + p + Σ χ(x^3+ax+b)      │
│                                         │
│  χ: Legendre符号                         │
│  Hasse界: |p + 1 - |E(F_p)|| ≤ 2√p     │
└─────────────────────────────────────────┘
```

### 技巧2: 椭圆曲线的约化

| 约化类型 | 定义 | $c_p$ |
|:---|:---|:---:|
| 好 | 光滑纤维 | 1 |
| 乘性 | 结点 | $v_p(\Delta)$ |
| 加性 | 尖点 | $\leq 4$ |

### 技巧3: L-函数计算

$$L(E, s) = \prod_{p \text{ good}} (1 - a_p p^{-s} + p^{1-2s})^{-1} \times \text{Euler factors at bad primes}$$

其中 $a_p = p + 1 - |E(\mathbb{F}_p)|$。

---

## 变式与推广

### 变式1: Weil猜想

对光滑射影簇 $X/\mathbb{F}_q$，证明:
- $\zeta_X(t)$ 是有理函数
- 函数方程
- Riemann假设类比

**已证**: Deligne (1974)

---

### 变式2: 高维Mordell

Bombieri-Lang猜想: 一般型的variety的有理点不Zariski稠密。

**问题**: 解释与Mordell猜想的联系。

---

### 变式3: p-adic方法

**问题**: 用p-adic积分计算有理点（Chabauty-Coleman方法）。

---

## 相关概念

| 概念 | 定义 | 符号 |
|:---|:---|:---:|
| Mordell-Weil群 | 有理点群 | $E(k)$ |
| L-函数 | Euler乘积 | $L(E, s)$ |
| Tate-Shafarevich | 主齐性空间 | $\text{Sha}$ |
| Hasse原理 | 局部-整体 | - |

## 参考文献

1. Silverman, J. *The Arithmetic of Elliptic Curves*
2. Faltings, G. *Endlichkeitssätze für abelsche Varietäten*
3. Wiles, A. *The Birch and Swinnerton-Dyer Conjecture* (Clay Math description)

---

**创建日期**: 2026-04-10  
**难度**: ⭐⭐⭐⭐  
**预计用时**: 120-150分钟
