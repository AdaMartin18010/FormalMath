---
习题编号: AG-EX-007
标题: 爆破的几何
类型: 构造型
难度: ⭐⭐⭐⭐
章节: Hartshorne Ch V
对应课程: Harvard Math 232br
预计用时: 120-150分钟
msc: 14E15, 14C17
---

# AG-EX-007: 爆破的几何

## 题目

### 原题 (Hartshorne V.3.1)

设 $X$ 是光滑曲面，$P \in X$ 是一点。设 $\pi: \tilde{X} \to X$ 是在 $P$ 处的爆破，$E = \pi^{-1}(P)$ 是例外除子。

**(a)** 证明 $E \cong \mathbb{P}^1$，且 $E^2 = -1$（自交数为负一）。

**(b)** 证明 $\tilde{X}$ 是光滑的。

**(c)** 设 $C \subseteq X$ 是通过 $P$ 的曲线，$\tilde{C}$ 是其严格变换。证明:
$$\tilde{C} = \pi^*C - mE$$
其中 $m = \text{mult}_P(C)$ 是 $C$ 在 $P$ 的重数。

### 计算题目

设 $X = \mathbb{P}^2$，$P = [1:0:0]$。

**(a)** 描述 $\tilde{X}$ 作为 $\mathbb{P}^2 \times \mathbb{P}^1$ 的闭子簇。

**(b)** 计算 $\text{Pic}(\tilde{X})$ 及其相交形式。

**(c)** 设 $L$ 是 $X$ 中的直线，求 $\pi^*L$ 和 $\tilde{L}$ 的类。

---

## 解答

### 主题目解答

#### (a) 例外除子的性质

**Step 1: 局部描述**

在 $P$ 附近，$X \cong \mathbb{A}^2$（局部同构），坐标 $(x, y)$，$P = (0, 0)$。

爆破定义为:
$$\tilde{X} = \{((x, y), [u:v]) \in \mathbb{A}^2 \times \mathbb{P}^1 : xv = yu\}$$

**Step 2: 例外除子**

$$E = \{(0, 0)\} \times \mathbb{P}^1 \cong \mathbb{P}^1$$

坐标 $[u:v]$ 对应于切方向。

**Step 3: 计算 $E^2$**

取 $X$ 中过 $P$ 的两条不同曲线 $C_1, C_2$，光滑且在 $P$ 横截相交。

严格变换 $\tilde{C}_1, \tilde{C}_2$ 与 $E$ 交于不同点（对应不同切方向）。

由 $\pi^*C_i = \tilde{C}_i + E$:
$$\pi^*C_1 \cdot \pi^*C_2 = (\tilde{C}_1 + E) \cdot (\tilde{C}_2 + E)$$

左边: $\pi^*(C_1 \cdot C_2) = C_1 \cdot C_2 = 1$（横截相交）

右边展开:
$$\tilde{C}_1 \cdot \tilde{C}_2 + \tilde{C}_1 \cdot E + E \cdot \tilde{C}_2 + E^2$$

- $\tilde{C}_1 \cdot \tilde{C}_2 = 0$（不相交，原像相交在 $P$ 上方被"拉开"）
- $\tilde{C}_i \cdot E = 1$（每个严格变换与 $E$ 交于一点）

故:
$$1 = 0 + 1 + 1 + E^2 \Rightarrow E^2 = -1$$

**结论**: $E \cong \mathbb{P}^1$，$E^2 = -1$。

---

#### (b) $\tilde{X}$ 的光滑性

**局部验证**:

在仿射开集 $u = 1$ 上，方程为 $xv = y$，即 $y = xv$。

这是 $\mathbb{A}^3$ 中的光滑超曲面（Jacobian处处非零）。

在仿射开集 $v = 1$ 上，方程为 $x = yu$，同样光滑。

**结论**: $\tilde{X}$ 光滑。

---

#### (c) 严格变换的公式

**定义**: 严格变换 $\tilde{C}$ 是 $\pi^{-1}(C \setminus \{P\})$ 的闭包。

**证明**:

**Step 1**: 计算 $\pi^*C$。

$$\pi^*C = \tilde{C} + mE$$

其中 $m$ 是 $E$ 在 $\pi^*C$ 中的重数。

**Step 2**: 计算重数。

局部上，$C$ 的方程为 $f(x, y) = 0$，在 $P$ 处有展开:
$$f = f_m + f_{m+1} + \cdots$$

其中 $f_m$ 是最低次齐次部分，$m = \text{mult}_P(C)$。

在爆破的坐标卡 $y = xv$ 中:
$$f(x, xv) = x^m f_m(1, v) + x^{m+1}(\cdots)$$

故在 $E$（即 $x = 0$）上，$f$ 有 $x^m$ 因子。

**结论**: $m = \text{mult}_P(C)$。

---

### 计算题目解答

#### (a) $\tilde{\mathbb{P}}^2$ 的嵌入

**定义**:
$$\tilde{X} = \{([x_0:x_1:x_2], [u_1:u_2]) \in \mathbb{P}^2 \times \mathbb{P}^1 : x_1u_2 = x_2u_1\}$$

在 $P = [1:0:0]$ 附近，$x_0 \neq 0$，局部坐标 $y_1 = x_1/x_0$, $y_2 = x_2/x_0$。

方程变为 $y_1u_2 = y_2u_1$，即 $\mathbb{A}^2$ 的爆破。

**验证闭子簇**:

方程 $x_1u_2 - x_2u_1 = 0$ 是双线性的，定义了 $\mathbb{P}^2 \times \mathbb{P}^1$ 的闭子簇。

---

#### (b) $\text{Pic}(\tilde{X})$ 和相交形式

**Step 1**: Picard群结构。

$$\text{Pic}(\tilde{X}) = \mathbb{Z} \cdot H \oplus \mathbb{Z} \cdot E$$

其中:
- $H = \pi^*(\text{超平面类})$
- $E$ = 例外除子

**Step 2**: 相交形式。

计算相交矩阵:

| 类 | $H$ | $E$ |
|:---:|:---:|:---:|
| $H$ | $H^2 = 1$ | $H \cdot E = 0$ |
| $E$ | $E \cdot H = 0$ | $E^2 = -1$ |

验证:
- $H^2 = 1$: 超平面的自交
- $H \cdot E = 0$: $E$ 在纤维中
- $E^2 = -1$: 已证

**相交形式矩阵**:
$$\begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$$

---

#### (c) 直线类

设 $L \subseteq \mathbb{P}^2$ 是过 $P$ 的直线。

**原像**:
$$\pi^*L = \tilde{L} + E$$

**严格变换**:

$\tilde{L}$ 是 $L$ 的严格变换，类为:
$$\tilde{L} = \pi^*L - E = H - E$$

**验证相交**:
$$\tilde{L}^2 = (H - E)^2 = H^2 - 2H \cdot E + E^2 = 1 - 0 - 1 = 0$$

（两个不同直线的严格变换不相交）

---

## 解题技巧

### 技巧1: 爆破公式速查

```
┌─────────────────────────────────────────┐
│  爆破 π: X̃ → X 在点 P                   │
│                                         │
│  例外除子 E ≅ P^{n-1}, E^n = (-1)^{n-1} │
│                                         │
│  严格变换: C̃ = π*C - mE                │
│  m = mult_P(C)                          │
│                                         │
│  典范除子: K_X̃ = π*K_X + (n-1)E        │
└─────────────────────────────────────────┘
```

### 技巧2: 相交数计算

**爆破后相交数变化**:
- $C, D$ 不过 $P$: $\tilde{C} \cdot \tilde{D} = C \cdot D$
- $C$ 过 $P$，$D$ 不过 $P$: $\tilde{C} \cdot \tilde{D} = C \cdot D$
- 都过 $P$: 需用严格变换公式

### 技巧3: 消没定理应用

**Castelnuovo判别**: 若 $E \cong \mathbb{P}^1$，$E^2 = -1$，则 $E$ 可收缩。

这是"逆爆破"的充分条件。

---

## 变式与推广

### 变式1: 一般子簇的爆破

设 $Y \subseteq X$ 是光滑子簇，余维 $r$。

**问题**: 描述爆破 $\tilde{X} \to X$ 沿 $Y$，例外除子 $E$ 的性质。

---

### 变式2: 有理映射与爆破

设 $\phi: X \dashrightarrow Y$ 是有理映射，无定义点集为 $Z$。

**问题**: 证明存在爆破 $\pi: \tilde{X} \to X$ 使得 $\phi \circ \pi$ 是态射。

---

### 变式3: Hironaka奇点消解

**定理**: 特征0的域上，任何簇都存在由爆破构成的奇点消解。

**问题**: 对曲线 $y^2 = x^3$（尖点），找出奇点消解的爆破序列。

---

## 相关概念

| 概念 | 定义 | 符号 |
|:---|:---|:---:|
| 爆破 | 沿子簇的变换 | $\text{Bl}_Y(X)$ |
| 例外除子 | 子簇的原像 | $E$ |
| 严格变换 | 原像的闭包 | $\tilde{C}$ |
| 自交数 | 曲线与自己的相交 | $C^2$ |

## 参考文献

1. Hartshorne, R. *Algebraic Geometry*, Ch V, §3
2. Beauville, A. *Complex Algebraic Surfaces*, Ch II
3. Griffiths, Harris. *Principles of Algebraic Geometry*, Ch 4

---

**创建日期**: 2026-04-10  
**难度**: ⭐⭐⭐⭐  
**预计用时**: 120-150分钟
