---
exercise_id: ANA-079
title: 凸分析基础与不等式应用
difficulty: ⭐⭐⭐
topics: [凸函数, Jensen不等式, 次梯度, Legendre变换]
created: 2026-04-10
---

## 题目

设 $\varphi: \mathbb{R} \to \mathbb{R}$ 是凸函数，$(X, \mathcal{M}, \mu)$ 是概率测度空间（$\mu(X) = 1$）。

(1) 证明 **Jensen不等式**：若 $f \in L^1(\mu)$，则

$$\varphi\left(\int_X f d\mu\right) \leq \int_X \varphi(f) d\mu$$

(2) 设 $\varphi$ 可微，证明在点 $x_0$ 处存在**支撑超平面**：

$$\varphi(x) \geq \varphi(x_0) + \varphi'(x_0)(x - x_0), \quad \forall x$$

(3) 应用：设 $a_1, ..., a_n > 0$，$p_1, ..., p_n > 0$，$\sum p_i = 1$，证明加权AM-GM不等式：

$$\prod_{i=1}^n a_i^{p_i} \leq \sum_{i=1}^n p_i a_i$$

## 详细解答

### (1) Jensen不等式证明

**离散情形先证**（归纳法）：

对 $n=2$：设 $p + q = 1$，$p,q \geq 0$，由凸性定义：

$$\varphi(px_1 + qx_2) \leq p\varphi(x_1) + q\varphi(x_2)$$

假设对 $n$ 成立，证 $n+1$：

$$\varphi\left(\sum_{i=1}^{n+1}p_i x_i\right) = \varphi\left((1-p_{n+1})\sum_{i=1}^n\frac{p_i}{1-p_{n+1}}x_i + p_{n+1}x_{n+1}\right)$$

$$\leq (1-p_{n+1})\varphi\left(\sum_{i=1}^n\frac{p_i}{1-p_{n+1}}x_i\right) + p_{n+1}\varphi(x_{n+1})$$

$$\leq (1-p_{n+1})\sum_{i=1}^n\frac{p_i}{1-p_{n+1}}\varphi(x_i) + p_{n+1}\varphi(x_{n+1}) = \sum_{i=1}^{n+1}p_i\varphi(x_i)$$

**连续情形**（简单函数逼近）：

设 $f$ 是简单函数：$f = \sum_{i=1}^n a_i \chi_{E_i}$，$\mu(E_i) = p_i$。

$$\varphi\left(\int f\right) = \varphi\left(\sum p_i a_i\right) \leq \sum p_i \varphi(a_i) = \int \varphi(f)$$

对一般 $f \in L^1$，取简单函数列 $f_k \to f$ a.e. 且 $|f_k| \leq |f|$。

由连续性：$\varphi(f_k) \to \varphi(f)$。

若 $\varphi \geq 0$ 或适当控制，用Fatou引理或控制收敛完成证明。

### (2) 支撑超平面

**证明**：对 $x > x_0$，由凸性：

$$\frac{\varphi(x) - \varphi(x_0)}{x - x_0} \geq \varphi'_+(x_0)$$

（右导数存在且等于次梯度）

因此 $\varphi(x) - \varphi(x_0) \geq \varphi'(x_0)(x - x_0)$。

对 $x < x_0$，类似用左导数。

若 $\varphi$ 可微，则 $\varphi'_+(x_0) = \varphi'_-(x_0) = \varphi'(x_0)$。

**几何意义**：凸函数的图像总在任意点切线的上方。

### (3) AM-GM不等式

取 $\varphi(x) = e^x$（凸函数），$x_i = \ln a_i$。

由Jensen不等式：

$$\exp\left(\sum p_i \ln a_i\right) \leq \sum p_i \exp(\ln a_i) = \sum p_i a_i$$

左边：$\exp\left(\ln \prod a_i^{p_i}\right) = \prod a_i^{p_i}$

故：

$$\prod_{i=1}^n a_i^{p_i} \leq \sum_{i=1}^n p_i a_i$$

**等号成立条件**：当且仅当所有 $a_i$ 相等（$\varphi$ 严格凸时）。

## 证明技巧

1. **归纳与逼近**：离散到连续的桥梁
2. **次梯度几何**：凸分析的直观理解
3. **函数选择**：将目标不等式转化为Jensen的标准形式

## 常见错误

| 错误类型 | 错误表现 | 正确做法 |
|---------|---------|---------|
| 积分存在性 | 默认 $\varphi(f)$ 可积 | 需假设 $f$ 使两边有意义 |
| 严格凸 | 认为等号总不成立 | 等号当 $f$ a.e.常数时成立 |
| 概率条件 | 忽视 $\mu(X)=1$ | Jensen需要概率测度或归一化 |

## 变式练习

**变式1（难度⭐⭐）**：用Jensen证明 Hölder不等式。

**变式2（难度⭐⭐⭐）**：设 $\varphi$ 严格凸，证明Jensen等号成立当且仅当 $f$ a.e.常数。

**变式3（难度⭐⭐⭐⭐）**：定义Legendre变换 $\varphi^*(y) = \sup_x(xy - \varphi(x))$，证明其对偶性。
