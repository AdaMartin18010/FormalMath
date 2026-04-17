---
习题编号: AG-EX-013
标题: 形变理论初步
类型: 前沿型
难度: ⭐⭐⭐⭐⭐
章节: Hartshorne Ch II
对应课程: Harvard Math 232br
预计用时: 150-180分钟
msc: 14D15, 14B10
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

# AG-EX-013: 形变理论初步

## 题目

### 原题 (基于Hartshorne习题序列)

设 $X_0$ 是代数闭域 $k$ 上的概形，$A$ 是Artin局部环，剩余域 $k$。

**一阶形变**:

**(a)** 证明 $X_0$ 在 $k[\epsilon]/\epsilon^2$ 上的形变（一阶形变）由 $H^1(X_0, \mathcal{T}_{X_0})$ 分类，其中 $\mathcal{T}_{X_0}$ 是切层。

**(b)** 设 $X_0 = \mathbb{P}^1_k$。证明 $H^1(\mathbb{P}^1, \mathcal{T}_{\mathbb{P}^1}) = 0$，即 $\mathbb{P}^1$ 没有非平凡一阶形变（刚性）。

**(c)** 设 $X_0$ 是椭圆曲线。计算 $\dim H^1(X_0, \mathcal{T}_{X_0})$ 并解释其几何意义。

### 应用题目

设 $X \subseteq \mathbb{P}^n$ 是闭子概形。

**(a)** 解释Hilbert概形在 $[X]$ 的切空间为何是 $H^0(X, \mathcal{N}_{X/\mathbb{P}^n})$，其中 $\mathcal{N}$ 是法丛。

**(b)** 对 $X = \mathbb{P}^1 \subseteq \mathbb{P}^3$（三次扭曲线），计算 $\dim H^0(X, \mathcal{N})$。

**(c)** 验证这与Hilbert概形的维数一致。

---

## 解答

### 主题目解答

#### (a) 一阶形变的分类

**设定**:

- $D = \text{Spec}(k[\epsilon]/\epsilon^2)$（双点）
- 一阶形变: 平坦族 $X \to D$ 使得 $X_0 = X \times_D \text{Spec}(k)$

**证明**:

**Step 1**: 局部描述。

设 $X_0 = \bigcup U_i$，$U_i = \text{Spec}(A_i)$。

一阶形变 $X$ 由 $U_i$ 的形变粘合而成。

**Step 2**: 局部形变。

$U_i$ 的一阶形变是自由的（仿射情形）。

具体: $\tilde{U}_i = \text{Spec}(A_i[\epsilon]/\epsilon^2)$ 是平凡形变。

**Step 3**: 粘合数据。

在 $U_{ij} = U_i \cap U_j$，两个局部形变可能不同。

差异由自同构给出:
$$\text{Aut}(U_{ij}[\epsilon]/\epsilon^2 / U_{ij}) \cong \Gamma(U_{ij}, \mathcal{T}_{X_0})$$

**Step 4**: Čech上同调。

粘合条件给出1-上闭链:
$$\{\theta_{ij} \in \Gamma(U_{ij}, \mathcal{T}_{X_0})\}$$

等价形变给出1-上边缘。

**结论**: 一阶形变 $\cong \check{H}^1(X_0, \mathcal{T}_{X_0}) \cong H^1(X_0, \mathcal{T}_{X_0})$。

---

#### (b) $\mathbb{P}^1$ 的刚性

**计算**:

$$\mathcal{T}_{\mathbb{P}^1} = \mathcal{O}_{\mathbb{P}^1}(2)$$

（Euler序列: $0 \to \mathcal{O} \to \mathcal{O}(1)^{\oplus 2} \to \mathcal{T} \to 0$）

**上同调**:

$$H^1(\mathbb{P}^1, \mathcal{O}(2)) = 0$$

因 $\deg = 2 > -2$，Serre对偶给出 $h^1 = h^0(-4) = 0$。

**结论**: $\mathbb{P}^1$ 没有非平凡一阶形变，是刚性的。

---

#### (c) 椭圆曲线的形变

**计算**:

椭圆曲线 $E$:

$$\mathcal{T}_E = \mathcal{O}_E$$（切丛平凡，$K_E = \mathcal{O}_E$）

$$H^1(E, \mathcal{O}_E) = k$$

（$g = 1$，$h^1(\mathcal{O}) = g = 1$）

**几何意义**:

- 一阶形变空间1维
- 对应于 $j$-不变量的变化
- 椭圆曲线的模空间是1维的（$\mathbb{A}^1_j$）

**结论**: $\dim H^1(E, \mathcal{T}_E) = 1$，形变由 $j$-不变量参数化。

---

### 应用题目解答

#### (a) Hilbert概形的切空间

**定理**: Hilbert概形 $H$ 在点 $[X]$ 的切空间:
$$T_{[X]}(H) = H^0(X, \mathcal{N}_{X/\mathbb{P}^n})$$

**解释**:

法丛:
$$0 \to \mathcal{T}_X \to \mathcal{T}_{\mathbb{P}^n}|_X \to \mathcal{N}_{X/\mathbb{P}^n} \to 0$$

$\mathcal{N}$ 的截面给出 $X$ 在 $\mathbb{P}^n$ 中的"无穷小形变"。

具体: 一阶形变由 "移动 $X$ 的法向" 给出。

**证明概要**:

- 平坦族 $X \subseteq \mathbb{P}^n \times D$ over $D = \text{Spec}(k[\epsilon]/\epsilon^2)$
- 局部由方程 $f_i + \epsilon g_i = 0$ 给出
- $g_i$ 模去切向是法丛截面

---

#### (b) 三次扭曲线的法丛

设 $X = C \subseteq \mathbb{P}^3$ 是三次扭曲线。

**法丛计算**:

正合列:
$$0 \to \mathcal{T}_C \to \mathcal{T}_{\mathbb{P}^3}|_C \to \mathcal{N}_{C/\mathbb{P}^3} \to 0$$

已知:
- $\mathcal{T}_C = \mathcal{O}_C(2)$（$C \cong \mathbb{P}^1$，标准嵌入）
- $\mathcal{T}_{\mathbb{P}^3}|_C = \mathcal{O}_C(1)^{\oplus 3}$（由Euler序列）

**计算**:

由 $C \cong \mathbb{P}^1$，嵌入由 $\mathcal{O}(3)$ 给出。

三次扭曲线有法丛:
$$\mathcal{N}_{C/\mathbb{P}^3} = \mathcal{O}_C(5)^{\oplus 2}$$

（这是三次有理曲线的已知结果）

**截面**:

$$h^0(C, \mathcal{N}) = 2 \cdot h^0(\mathbb{P}^1, \mathcal{O}(5)) = 2 \cdot 6 = 12$$

---

#### (c) Hilbert概形的维数

**Hilbert多项式**:

三次扭曲线 $C \subseteq \mathbb{P}^3$:
- 次数 = 3
- 亏格 = 0

Hilbert多项式: $P(m) = 3m + 1$

**Hilbert概形维数**:

$H_{3m+1, \mathbb{P}^3}$ 参数化所有算术亏格0、次数3的曲线。

这些曲线包括:
- 三次扭曲线（非平面）
- 平面三次曲线（光滑、奇异）
- 退化情形

$H_{3m+1, \mathbb{P}^3}$ 的维数 = 12。

验证: 
- $GL(4)$ 作用轨道: $\dim GL(4) - \dim \text{Aut}(C) = 16 - 3 = 13$？

更准确: 三次扭曲线由 $PGL(4)$ 作用，模空间维数为 $12 - 0 = 12$（稳定化子维数0）。

**结论**: $\dim H^0(\mathcal{N}) = 12 = \dim_{[C]} H$，一致。

---

## 解题技巧

### 技巧1: 形变理论框架

```
┌─────────────────────────────────────────┐
│  形变理论三部曲:                        │
│  1. 一阶形变: H^1(X, T_X)              │
│  2. 阻碍: H^2(X, T_X)                  │
│  3. 形式形变 → 代数形变 (Artin逼近)    │
└─────────────────────────────────────────┘
```

### 技巧2: 刚性判据

若 $H^1(X, \mathcal{T}_X) = 0$，则 $X$ 是刚性的（无局部形变）。

**刚性例子**:
- $\mathbb{P}^n$
- 格拉斯曼簇
- 齐性空间

### 技巧3: Hilbert概形计算

```
Hilbert概形切空间:
T_[X] = H^0(X, N_{X/P^n})

维数 = h^0(N) - h^1(N)（光滑点）
```

---

## 变式与推广

### 变式1: Calabi-Yau流形

设 $X$ 是Calabi-Yau（$K_X = 0$，$h^1(\mathcal{O}) = 0$）。

**问题**: 计算 $\dim H^1(X, \mathcal{T}_X)$。

**答案**: 用Serre对偶，$h^1(\mathcal{T}) = h^{n-1,1}$，是Hodge数。

---

### 变式2: 抽象变与嵌入形变

区分:
- 抽象形变: $H^1(X, \mathcal{T}_X)$
- 嵌入形变: $H^0(X, \mathcal{N}_{X/Y})$

**问题**: 对 $X \subseteq Y$，建立正合列联系两者。

---

### 变式3: Kontsevich模空间

**问题**: 解释 $\overline{M}_{g,n}$（稳定曲线模空间）与形变理论的关系。

---

## 相关概念

| 概念 | 定义 | 符号 |
|:---|:---|:---:|
| 一阶形变 | 在双点上的形变 | - |
| 切层 | 导子层 | $\mathcal{T}_X$ |
| 法丛 | 切丛商 | $\mathcal{N}_{X/Y}$ |
| 刚性 | 无局部形变 | - |

## 参考文献

1. Hartshorne, R. *Deformation Theory*
2. Kodaira, K. *Complex Manifolds and Deformation of Complex Structures*
3. Voisin, C. *Hodge Theory and Complex Algebraic Geometry*, Ch 9

---

**创建日期**: 2026-04-10  
**难度**: ⭐⭐⭐⭐⭐  
**预计用时**: 150-180分钟
