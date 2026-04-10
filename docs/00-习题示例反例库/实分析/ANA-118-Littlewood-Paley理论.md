---
习题编号: ANA-118
学科: 实分析
知识点: 调和分析-Littlewood-Paley理论
难度: ⭐⭐⭐⭐⭐
预计时间: 50分钟
---

# Littlewood-Paley理论

## 题目

设 $\psi \in C_c^\infty(\mathbb{R}^n)$ 满足 $\text{supp}(\psi) \subset \{\frac{1}{2} < |\xi| < 2\}$ 且 $\sum_{j \in \mathbb{Z}} \psi(2^{-j}\xi) = 1$ 对所有 $\xi \neq 0$。

定义Littlewood-Paley投影：
$$\widehat{\Delta_j f}(\xi) = \psi(2^{-j}\xi) \hat{f}(\xi)$$

和平方函数：
$$S(f)(x) = \left( \sum_{j \in \mathbb{Z}} |\Delta_j f(x)|^2 \right)^{1/2}$$

**(a)** 证明：对 $1 < p < \infty$，存在常数 $C_p, c_p > 0$ 使得
$$c_p \|f\|_{L^p} \leq \|S(f)\|_{L^p} \leq C_p \|f\|_{L^p}$$
对所有 $f \in L^p(\mathbb{R}^n)$ 成立。

**(b)** 设 $f \in L^p(\mathbb{R})$，$1 < p < \infty$，用Littlewood-Paley分解证明：
$$\|f\|_{L^p} \sim \left\| \left( \sum_{j} |\Delta_j f|^2 \right)^{1/2} \right\|_{L^p}$$

**(c)** 证明Bernstein不等式：若 $\text{supp}(\hat{f}) \subset \{\xi : |\xi| \sim 2^j\}$，则
$$\|\partial^\alpha f\|_{L^p} \leq C_\alpha 2^{j|\alpha|} \|f\|_{L^p}$$

## 解答

### (a) Littlewood-Paley定理

**证明概要：**

这是调和分析的核心定理，证明需用到向量值奇异积分理论。

**Step 1**：定义向量值算子
$$T: L^p \to L^p(l^2), \quad Tf = (\Delta_j f)_{j \in \mathbb{Z}}$$

**Step 2**：$L^2$ 估计
$$\|S(f)\|_{L^2}^2 = \sum_j \|\Delta_j f\|_{L^2}^2 = \sum_j \|\psi(2^{-j}\cdot)\hat{f}\|_{L^2}^2$$

由 $\sum_j |\psi(2^{-j}\xi)|^2 \sim 1$（几乎正交性）：
$$\|S(f)\|_{L^2}^2 \sim \|\hat{f}\|_{L^2}^2 = \|f\|_{L^2}^2$$

**Step 3**：核的Hörmander条件
$\Delta_j$ 的核 $K_j(x) = 2^{jn} \check{\psi}(2^j x)$ 满足：
$$\sum_j \int_{|x| > 2|y|} |K_j(x-y) - K_j(x)| dx \leq C$$

这是向量值Calderón-Zygmund理论的标准应用。

**Step 4**：由向量值C-Z理论，$T$ 在 $L^p$ ($1 < p < \infty$) 有界。

逆不等式由对偶性得到。$\square$

### (b) 具体估计

**证明：**

**上界**：如(a)所述，用向量值C-Z理论。

**下界**：设 $g \in L^{p'}$，$\|g\|_{p'} = 1$，$\frac{1}{p} + \frac{1}{p'} = 1$。

由对偶性：
$$\|f\|_p = \sup_{\|g\|_{p'}=1} |\langle f, g \rangle|$$

Littlewood-Paley算子几乎正交：
$$\langle f, g \rangle = \sum_j \langle \Delta_j f, \tilde{\Delta}_j g \rangle$$

其中 $\tilde{\Delta}_j$ 是稍大频率局部化。

由Cauchy-Schwarz：
$$|\langle f, g \rangle| \leq \int S(f) \tilde{S}(g) \leq \|S(f)\|_p \|\tilde{S}(g)\|_{p'} \leq C \|S(f)\|_p$$

取上确界得 $\|f\|_p \leq C \|S(f)\|_p$。$\square$

### (c) Bernstein不等式

**证明：**

设 $\text{supp}(\hat{f}) \subset \{c_1 2^j \leq |\xi| \leq c_2 2^j\}$。

$$\partial^\alpha f = \mathcal{F}^{-1}((2\pi i \xi)^\alpha \hat{f})$$

令 $\tilde{\psi}$ 在 $\text{supp}(\hat{f})$ 的邻域上为1，$\tilde{\psi}_j(\xi) = \tilde{\psi}(2^{-j}\xi)$。

$$(2\pi i \xi)^\alpha \hat{f}(\xi) = (2\pi i \xi)^\alpha \tilde{\psi}_j(\xi) \hat{f}(\xi)$$

因此：
$$\partial^\alpha f = 2^{j|\alpha|} \mathcal{F}^{-1}((2^{-j}\xi)^\alpha \tilde{\psi}(2^{-j}\xi)) * f$$

核 $\check{\varphi}_j(x) = 2^{jn} \check{\varphi}(2^j x)$，其中 $\varphi(\xi) = (2\pi i \xi)^\alpha \tilde{\psi}(\xi)$。

$$\|\check{\varphi}_j\|_{L^1} = \|\check{\varphi}\|_{L^1} < \infty$$

因此：
$$\|\partial^\alpha f\|_{L^p} \leq 2^{j|\alpha|} \|\check{\varphi}\|_{L^1} \|f\|_{L^p}$$
$\square$

## 证明技巧

1. **向量值算子**：将Littlewood-Paley理论纳入C-Z框架
2. **几乎正交性**：频率局部化的关键性质
3. **尺度分析**：Bernstein不等式体现不同频率的行为差异

## 常见错误

- ❌ 忽略频率支撑条件的精确刻画
- ❌ 向量值算子范数估计时漏掉$l^2$结构
- ❌ 尺度变换时忽略各向异性

## 变式练习

**变式1：** 证明Sobolev空间 $H^s$ 的Littlewood-Paley刻画：
$$\|f\|_{H^s} \sim \left\| \left( \sum_j 2^{2js} |\Delta_j f|^2 \right)^{1/2} \right\|_{L^2}$$

**变式2：** 证明Besov空间的等价定义：
$$\|f\|_{B^s_{p,q}} = \left( \sum_j 2^{jsq} \|\Delta_j f\|_{L^p}^q \right)^{1/q}$$
