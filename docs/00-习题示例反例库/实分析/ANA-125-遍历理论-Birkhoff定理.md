---
习题编号: ANA-125
学科: 实分析
知识点: 遍历理论-Birkhoff遍历定理
难度: ⭐⭐⭐⭐
预计时间: 45分钟
---

# Birkhoff遍历定理

## 题目

设 $(X, \mathcal{B}, \mu)$ 是概率空间，$T: X \to X$ 是保测变换（即 $\mu(T^{-1}E) = \mu(E)$ 对所有可测 $E$）。

定义遍历平均：$A_n f(x) = \frac{1}{n} \sum_{k=0}^{n-1} f(T^k x)$

**(a)** 证明Birkhoff遍历定理：对 $f \in L^1(\mu)$，$A_n f(x)$ 几乎处处收敛于某 $f^* \in L^1$。

**(b)** 若 $T$ 是**遍历的**（即 $T^{-1}E = E$ 蕴含 $\mu(E) \in \{0,1\}$），证明 $f^* = \int f d\mu$ a.e.。

**(c)** 将结果应用于旋转 $T(x) = x + \alpha \pmod{1}$ 于 $[0,1)$，讨论遍历性条件。

## 解答

### (a) Birkhoff遍历定理

**证明概要：**

**Step 1**：最大值不等式。

设 $f \in L^1$，$M_n f(x) = \max_{1 \leq k \leq n} \sum_{j=0}^{k-1} f(T^j x)$。

证明：$\int_{\{M_n f > 0\}} f d\mu \geq 0$。

这是Wiener极大遍历定理的关键。

**Step 2**：几乎处处收敛。

令 $\bar{f}(x) = \limsup A_n f(x)$，$\underline{f}(x) = \liminf A_n f(x)$。

需证 $\bar{f} = \underline{f}$ a.e.。

对任意有理数 $\alpha < \beta$，令 $E_{\alpha,\beta} = \{x : \underline{f}(x) < \alpha < \beta < \bar{f}(x)\}$。

用最大值不等式证明 $\mu(E_{\alpha,\beta}) = 0$。

**Step 3**：极限的可积性。

由Fatou引理，$f^* \in L^1$。$\square$

### (b) 遍历系统的平均

**证明：**

由(a)，$f^*$ 满足 $f^* \circ T = f^*$ a.e.（不变性）。

若 $T$ 遍历，不变函数必为常数a.e.。

由 $\int A_n f = \int f$ 和 $A_n f \to f^*$，用控制收敛（或Fatou）：
$$\int f^* = \lim \int A_n f = \int f$$

因此 $f^* = \int f$ a.e.$\square$

### (c) 圆周旋转

**分析：**

$\alpha$ 无理数时，$T$ 遍历。

**证明**：设 $E$ 可测，$T^{-1}E = E$。

Fourier级数：$\chi_E(x) = \sum_n c_n e^{2\pi i n x}$。

$T$ 不变性：$\chi_E(x+\alpha) = \chi_E(x)$。

$$\sum_n c_n e^{2\pi i n \alpha} e^{2\pi i n x} = \sum_n c_n e^{2\pi i n x}$$

因此 $c_n (e^{2\pi i n \alpha} - 1) = 0$。

$\alpha$ 无理 $\Rightarrow$ $e^{2\pi i n \alpha} \neq 1$ 对 $n \neq 0$。

故 $c_n = 0$ 对 $n \neq 0$，即 $\chi_E = c_0$ 是常数。

因此 $\mu(E) \in \{0,1\}$，$T$ 遍历。$\square$

## 证明技巧

1. **极大函数技巧**：Wiener不等式的应用
2. **不变函数刻画**：遍历性的等价位述
3. **Fourier分析**：具体系统的遍历性证明

## 常见错误

- ❌ 将$L^1$收敛与a.e.收敛混淆
- ❌ 忽略遍历定理中极限可积性验证
- ❌ 无理旋转遍历性证明中的有理逼近

## 变式练习

**变式1：** 证明von Neumann平均遍历定理（$L^2$版本）。

**变式2：** 证明 doubling map $T(x) = 2x \pmod 1$ 是遍历的。
