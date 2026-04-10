---
习题编号: ANA-111
学科: 实分析
知识点: 位势论-Perron方法
难度: ⭐⭐⭐⭐
预计时间: 35分钟
---

# Perron方法与Dirichlet问题

## 题目

设 $\Omega \subset \mathbb{R}^n$ 是有界开集，$\varphi \in C(\partial\Omega)$。

**Dirichlet问题**：求 $u \in C^2(\Omega) \cap C(\bar{\Omega})$ 使得：
$$\begin{cases} \Delta u = 0 & \text{于 } \Omega \\ u = \varphi & \text{于 } \partial\Omega \end{cases}$$

(a) 证明调和函数的最大值原理。

(b) 定义下调和函数，构造Perron族并证明上确界是调和的。

(c) 讨论边界正则性：何时Perron解连续到边界？

## 解答

### (a) 最大值原理

**定理**：若 $u$ 在 $\Omega$ 上调和，在 $\bar{\Omega}$ 连续，则：
$$\max_{\bar{\Omega}} u = \max_{\partial\Omega} u$$

**证明：**

**Step 1**：强最大值原理。

设 $u$ 在 $x_0 \in \Omega$ 达到最大值。

由平均值性质：
$$u(x_0) = \frac{1}{|B_r|} \int_{B_r(x_0)} u(y) dy \leq u(x_0)$$

等号成立当且仅当 $u = u(x_0)$ 于 $B_r(x_0)$。

由连通性，$u$ 恒等于常数。

**Step 2**：弱形式。

若 $u$ 非常数，则最大值不在内部达到，故在边界达到。$\square$

### (b) Perron方法

**定义**：$v$ 是**下调和**的，若对任意球 $B \subset\subset \Omega$：
$$v(x) \leq \frac{1}{|\partial B|} \int_{\partial B} v(y) dS_y \quad \text{（次平均值性质）}$$

**Perron族**：
$$\mathcal{S}_\varphi = \{v \in C(\bar{\Omega}) : v \text{ 下调和于 } \Omega, v \leq \varphi \text{ 于 } \partial\Omega\}$$

**Perron解**：$u(x) = \sup_{v \in \mathcal{S}_\varphi} v(x)$。

**证明 $u$ 调和**：

**Step 1**：局部上调和修正。

对 $v \in \mathcal{S}_\varphi$，球 $B \subset\subset \Omega$，定义：
$$\bar{v}(x) = \begin{cases} v(x) & x \notin B \\ h(x) & x \in B \end{cases}$$

其中 $h$ 是Dirichlet问题的解：$\Delta h = 0$ 于 $B$，$h = v$ 于 $\partial B$。

由最大值原理，$\bar{v} \geq v$ 且 $\bar{v} \in \mathcal{S}_\varphi$。

**Step 2**：构造单调序列。

取一列球 $\{B_k\}$ 覆盖 $\Omega$，反复做上调和修正。

得单调递增序列 $v_n \leq u$，$v_n \to u$。

**Step 3**：$u$ 调和。

在每个球上，$v_n$ 最终变为调和的（修正后不变）。

调和函数列的一致极限是调和的（内部估计）。

故 $u$ 调和。$\square$

### (c) 边界正则性

**定义**：$\xi \in \partial\Omega$ 是**正则点**，若Perron解满足 $\lim_{x \to \xi} u(x) = \varphi(\xi)$。

**Barrier判别法**：

$\xi$ 正则当且仅当存在**闸函数**（barrier）：

$w \in C(\bar{\Omega})$ 下调和，$w(\xi) = 0$，$w > 0$ 于 $\partial\Omega \setminus \{\xi\}$。

**几何条件**：

- 外球条件：存在球 $B$ 使 $\bar{B} \cap \bar{\Omega} = \{\xi\}$。
- 锥条件：存在锥在 $\xi$ 外切于 $\Omega$。

这些条件保证闸函数存在。$\square$

## 证明技巧

1. **平均值性质**：调和函数的核心特征
2. **上调和修正**：在不破坏下调和性的前提下提升函数
3. **闸函数构造**：边界行为的局部控制

## 常见错误

- ❌ 混淆下调和与次调和（subharmonic）
- ❌ Perron族为空或不包含足够多函数
- ❌ 忘记验证边界条件

## 变式练习

**变式1：** 用Perron方法解单位圆盘上的Dirichlet问题，验证与Poisson积分一致。

**变式2：** 讨论非正则边界点的例子（如Lebesgue刺）。
