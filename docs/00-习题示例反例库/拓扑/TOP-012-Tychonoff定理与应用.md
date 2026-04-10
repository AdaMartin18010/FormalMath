---
number: "TOP-012"
category: 拓扑
topic: 紧致性
difficulty: ⭐⭐⭐⭐
title: Tychonoff定理及其应用
keywords: [Tychonoff定理, 乘积拓扑, 紧致, 选择公理, 超滤子]
prerequisites: [TOP-011]
source: 经典拓扑习题
---

## 题目

**Tychonoff定理：** 任意一族紧致空间的乘积（乘积拓扑）是紧致的。

**(a)** 用超滤子证明Tychonoff定理。

**(b)** 证明：Tychonoff定理等价于选择公理。

**(c)** 证明：$[0, 1]^I$ 对任意集合 $I$ 紧致（Tychonoff立方体）。

**(d)** 证明：完全正则空间可嵌入某Tychonoff立方体。

## 详细解答

### (a) 用超滤子证明Tychonoff定理

**证明：**

**超滤子刻画：** 空间紧致 $\Leftrightarrow$ 每个超滤子收敛。

设 $X_i$ 紧致，$i \in I$，$X = \prod X_i$。

设 $\mathcal{U}$ 是 $X$ 上的超滤子。

**步骤1：** 投影超滤子

对每个 $i$，$(\pi_i)_*\mathcal{U} = \{A \subset X_i : \pi_i^{-1}(A) \in \mathcal{U}\}$ 是 $X_i$ 上的超滤子。

**步骤2：** 收敛性

$X_i$ 紧致，$(\pi_i)_*\mathcal{U} \to x_i$ 某 $x_i \in X_i$。

**步骤3：** 乘积收敛

设 $x = (x_i)_{i \in I}$。

$x$ 的邻域基元：$U = \bigcap_{j=1}^n \pi_{i_j}^{-1}(U_{i_j})$。

$(\pi_{i_j})_*\mathcal{U} \to x_{i_j}$，故 $U_{i_j} \in (\pi_{i_j})_*\mathcal{U}$。

$\pi_{i_j}^{-1}(U_{i_j}) \in \mathcal{U}$，有限交 $U \in \mathcal{U}$。

故 $\mathcal{U} \to x$。

**证毕。**

### (b) Tychonoff定理与选择公理的等价性

**证明：**

**(Tychonoff $\Rightarrow$ AC)**

设 $\{X_i\}_{i \in I}$ 是非空集族。

赋予离散拓扑（紧致当有限，但 $X_i$ 可能无限）。

令 $Y_i = X_i \cup \{\infty_i\}$，单点紧化（紧致）。

$\prod Y_i$ 紧致（Tychonoff）。

定义闭集 $F_i = \pi_i^{-1}(X_i) = \{y : y_i \in X_i\}$。

有限交：$F_{i_1} \cap ... \cap F_{i_n}$ 非空（选 $y_{i_j} \in X_{i_j}$，其余为$\infty$）。

$\bigcap_i F_i = \prod X_i \neq \emptyset$（紧致性）。

**(AC $\Rightarrow$ Tychonoff)**

(a)中证明用到了选择公理（为每个超滤子选极限）。

**证毕。**

### (c) Tychonoff立方体

**证明：**

$[0, 1]$ 紧致。

$[0, 1]^I = \prod_{i \in I} [0, 1]$ 是紧致空间的乘积。

由Tychonoff定理，紧致。

**证毕。**

### (d) 完全正则空间的嵌入

**证明：**

**完全正则：** 点和闭集可用连续函数分离。

设 $X$ 完全正则，$\mathcal{F} = C(X, [0, 1])$ 是连续函数集。

定义 $\Phi: X \to [0, 1]^\mathcal{F}$，$\Phi(x)(f) = f(x)$。

**连续：** 每个坐标连续。

**单射：** 若 $x \neq y$，完全正则性给出 $f$ 使 $f(x) \neq f(y)$，故 $\Phi(x) \neq \Phi(y)$。

**开映射到像：** 需证 $X$ 的拓扑是子空间拓扑。

对开集 $U \subset X$，$x \in U$，找 $f$ 使 $f(x) = 0$，$f(X \setminus U) = 1$。

则 $\Phi(x) \in \pi_f^{-1}([0, 1)) \cap \Phi(X) \subset \Phi(U)$。

**证毕。**

## 证明技巧

1. **超滤子的应用：** 紧致性 = 超滤子收敛
2. **选择公理的等价形式：** Tychonoff是强的紧致性命题
3. **嵌入定理：** 用连续函数族分离点和闭集

## 常见错误

| 错误 | 说明 |
|------|------|
| 混淆乘积拓扑与箱拓扑 | Tychonoff对箱拓扑不成立 |
| 忘记选择公理的作用 | Tychonoff需要AC |
| 嵌入定理需完全正则 | Hausdorff不足以保证嵌入立方体 |

## 变式练习

**变式1：** 证明：局部紧致空间的乘积局部紧致（有限乘积）。

**变式2：** 证明Stone-Čech紧化：完全正则空间到紧致的极大紧化。

**变式3：** 证明：紧致Hausdorff空间是Baire空间。
