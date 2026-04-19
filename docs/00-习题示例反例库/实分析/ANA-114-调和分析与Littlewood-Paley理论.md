---
msc_primary: 00A99
习题编号: ANA-114
学科: 实分析
知识点: 调和分析-Littlewood-Paley分解
难度: ⭐⭐⭐⭐⭐
预计时间: 45分钟
---

# 调和分析与Littlewood-Paley理论

## 题目

**Littlewood-Paley分解**：设 $\psi \in C_c^\infty(\mathbb{R}^n)$，$\psi = 1$ 于 $B_1(0)$，$\psi = 0$ 于 $B_2(0)^c$。

令 $\varphi_j(\xi) = \psi(2^{-j}\xi) - \psi(2^{-j+1}\xi)$，$j \in \mathbb{Z}$。

则 $\sum_{j \in \mathbb{Z}} \varphi_j(\xi) = 1$（$\xi \neq 0$）。

定义频率局部化算子：$\widehat{\Delta_j f} = \varphi_j \hat{f}$。

(a) 证明Littlewood-Paley平方函数定理（$L^p$ 情形）：
$$\|f\|_{L^p} \approx \left\|\left(\sum_j |\Delta_j f|^2\right)^{1/2}\right\|_{L^p}, \quad 1 < p < \infty$$

(b) 用LP分解刻画Sobolev空间：$f \in H^s \Leftrightarrow \sum_j 2^{2js} \|\Delta_j f\|_2^2 < \infty$。

(c) 证明Mikhlin乘子定理：若 $m$ 满足 $|\partial^\alpha m(\xi)| \leq C_\alpha |\xi|^{-|\alpha|}$，则 $T_m$ 是 $L^p$ 有界的。

## 解答

### (a) Littlewood-Paley平方函数定理

**证明概要：**

**Step 1**：$p=2$ 情形。

由Plancherel：
$$\|f\|_2^2 = \int |\hat{f}|^2 = \int \sum_j |\varphi_j \hat{f}|^2 = \sum_j \|\Delta_j f\|_2^2$$

几乎正交性。

**Step 2**：$p \neq 2$ 的插值。

定义平方函数：
$$Sf(x) = \left(\sum_j |\Delta_j f(x)|^2\right)^{1/2}$$

需证 $\|Sf\|_p \approx \|f\|_p$。

**上界**：用向量值奇异积分理论或Khintchine不等式。

**下界**：对偶性。$S$ 的伴随算子本质上是自身。

**向量值估计**：

对序列值函数 $(f_j)$，定义：
$$\|(f_j)\|_{L^p(\ell^2)} = \left\|\left(\sum_j |f_j|^2\right)^{1/2}\right\|_p$$

证明向量值奇异积分的有界性。$\square$

### (b) Sobolev空间的LP刻画

**证明：**

**定义**：$f \in H^s \Leftrightarrow \int (1+|\xi|^2)^s |\hat{f}(\xi)|^2 d\xi < \infty$。

**LP分解**：

在环形区域 $2^{j-1} \leq |\xi| \leq 2^{j+1}$，$(1+|\xi|^2)^s \approx 2^{2js}$。

因此：
$$\|f\|_{H^s}^2 = \int (1+|\xi|^2)^s |\hat{f}|^2 \approx \sum_j 2^{2js} \int_{\text{ring } j} |\hat{f}|^2$$

$$\approx \sum_j 2^{2js} \|\Delta_j f\|_2^2$$
$\square$

### (c) Mikhlin乘子定理

**证明概要：**

**Step 1**：分解乘子。

$m_j(\xi) = m(\xi) \varphi_j(\xi)$ 支集在 $|\xi| \approx 2^j$。

$\widehat{T_{m_j} f} = m_j \hat{f} = m_j \sum_{|k-j| \leq 1} \widehat{\Delta_k f}$。

**Step 2**：估计核。

$m_j$ 的逆Fourier变换 $K_j$ 满足：
$$|K_j(x)| \leq C_N 2^{jn} (1 + 2^j|x|)^{-N}$$

（由光滑性和支集大小）

**Step 3**：应用Calderón-Zygmund理论。

验证 $T_m$ 的核满足Hörmander条件。

由LP分解和平方函数：
$$\|T_m f\|_p \approx \left\|\left(\sum_j |T_{m_j} f|^2\right)^{1/2}\right\|_p$$

逐频率块估计，用Mikhlin条件控制。$\square$

## 证明技巧

1. **几乎正交分解**：频率空间的二进分割
2. **向量值估计**：从标量到序列值的推广
3. **核估计**：逆Fourier变换的衰减控制

## 常见错误

- ❌ 忽略低频（$j < 0$）或高频的单独处理
- ❌ 忘记验证LP分解的单位分解性质
- ❌ 乘子条件中导数阶数与维数的关系

## 变式练习

**变式1：** 用LP分解证明Sobolev嵌入定理。

**变式2：** 证明Besov空间 $B^s_{p,q}$ 的LP刻画。
