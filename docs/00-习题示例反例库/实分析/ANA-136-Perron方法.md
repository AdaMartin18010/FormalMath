---
msc_primary: 00A99
习题编号: ANA-136
学科: 实分析
知识点: 分布理论-Perron方法
难度: ⭐⭐⭐⭐
预计时间: 40分钟
---

# Perron方法

## 题目

设 $\Omega \subset \mathbb{R}^n$ 是有界区域，Dirichlet问题：
$$\begin{cases} \Delta u = 0 & \text{于 } \Omega \\ u = f & \text{于 } \partial\Omega \end{cases}$$

**(a)** 定义下调和函数：$u \in C(\Omega)$ 满足对任意球 $B \subset \subset \Omega$：
$$u(x) \leq \frac{1}{|B|} \int_B u(y) dy, \quad x \in B$$
证明最大值原理：若 $u$ 下调和，则 $\sup_\Omega u = \sup_{\partial\Omega} u$。

**(b)** 定义Perron族：对边界数据 $f$，设
$$\mathcal{S}_f = \{v \in C(\bar{\Omega}) : v \text{ 下调和}, v|_{\partial\Omega} \leq f\}$$
证明 $u(x) = \sup_{v \in \mathcal{S}_f} v(x)$ 在 $\Omega$ 内调和。

**(c)** 讨论边界正则性：何种条件下 $u$ 连续延拓到边界且 $u|_{\partial\Omega} = f$？

## 解答

### (a) 下调和函数最大值原理

**证明：**

设 $M = \sup_\Omega u$，$E = \{x \in \Omega : u(x) = M\}$。

若 $E \neq \emptyset$，取 $x_0 \in E$。

对任意 $B_r(x_0) \subset \Omega$：
$$M = u(x_0) \leq \frac{1}{|B_r|} \int_{B_r(x_0)} u \leq M$$

故等号成立，$u = M$ a.e. 于 $B_r(x_0)$。

由连续性，$u = M$ 于 $B_r(x_0)$，故 $B_r(x_0) \subset E$。

$E$ 开。若 $E \neq \emptyset$，连通性推出 $E = \Omega$，即 $u$ 常数。

否则 $E = \emptyset$，$u < M$ 于 $\Omega$，$M$ 在边界达到。$\square$

### (b) Perron解的调和性

**证明：**

**Step 1**：$\mathcal{S}_f$ 非空且有上界。

$\inf f$ 是下调和（常数），属于 $\mathcal{S}_f$。

$\sup f$ 是上界。

**Step 2**：上调和修正。

对 $v \in \mathcal{S}_f$ 和球 $B \subset \subset \Omega$，定义
$$v_B = \begin{cases} v & \text{于 } \Omega \setminus B \\ h & \text{于 } B \end{cases}$$

其中 $h$ 是 $B$ 内Dirichlet问题的解，边界值 $v|_{\partial B}$。

$v_B \in \mathcal{S}_f$ 且 $v_B \geq v$。

**Step 3**：$u$ 的调和性。

对任意 $B \subset \subset \Omega$，取 $v_n \in \mathcal{S}_f$ 使 $v_n(x_0) \to u(x_0)$。

不妨设 $v_n = (v_n)_B$（调和于 $B$）。

在 $B$ 内，$v_n$ 一致有界调和列，有子列一致收敛于调和函数 $h$。

$h \leq u$，$h(x_0) = u(x_0)$。

由强最大值原理，$h = u$ 于 $B$，故 $u$ 调和。$\square$

### (c) 边界正则性

**解答：**

**障碍函数判别法**：$\xi \in \partial\Omega$ 是正则边界点当存在 **障碍函数** $\omega$：
- $\omega$ 于 $\Omega$ 上调和
- $\omega > 0$ 于 $\Omega$
- $\omega(x) \to 0$ 当 $x \to \xi$

**充分条件**：
- 外球条件：存在球 $B$ 使 $\bar{B} \cap \bar{\Omega} = \{\xi\}$
- 锥条件：外有锥
- Wiener判别法：容量条件$\sum_{k=1}^{\infty} \frac{\text{cap}(\Omega^c \cap B_{2^{-k}}(\xi))}{2^{-k(n-2)}} = \infty$
$\square$
