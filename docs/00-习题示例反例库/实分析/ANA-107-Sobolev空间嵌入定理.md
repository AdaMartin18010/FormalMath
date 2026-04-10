---
习题编号: ANA-107
学科: 实分析
知识点: Sobolev空间-嵌入定理
难度: ⭐⭐⭐⭐⭐
预计时间: 35分钟
---

# Sobolev空间嵌入定理

## 题目

设 $\Omega \subset \mathbb{R}^n$ 是有界开集，$W^{k,p}(\Omega)$ 是Sobolev空间。

**Sobolev嵌入**：若 $kp < n$，则 $W^{k,p}(\Omega) \hookrightarrow L^q(\Omega)$，其中 $\frac{1}{q} = \frac{1}{p} - \frac{k}{n}$。

若 $kp > n$，则 $W^{k,p}(\Omega) \hookrightarrow C^{k-[n/p]-1,\gamma}(\bar{\Omega})$。

(a) 证明Gagliardo-Nirenberg-Sobolev不等式（$k=1$，$p < n$）：
$$\|u\|_{L^{p^*}} \leq C \|\nabla u\|_{L^p}, \quad \frac{1}{p^*} = \frac{1}{p} - \frac{1}{n}$$

(b) 证明Rellich-Kondrachov紧嵌入：$W^{1,p}(\Omega) \hookrightarrow\hookrightarrow L^q(\Omega)$ 对 $q < p^*$。

(c) 设 $n=3$，$p=2$，给出 $H^1(\Omega) \hookrightarrow L^6(\Omega)$ 的具体估计。

## 解答

### (a) Gagliardo-Nirenberg-Sobolev不等式

**证明概要：**

**情形 $p=1$**：

对 $u \in C_c^1(\mathbb{R}^n)$：
$$|u(x)| \leq \int_{-\infty}^{x_i} |\partial_i u(x_1,\ldots,t,\ldots,x_n)| dt$$

$$|u(x)|^{n/(n-1)} \leq \prod_{i=1}^n \left(\int_{-\infty}^\infty |\partial_i u| dx_i\right)^{1/(n-1)}$$

积分并用Hölder：
$$\int |u|^{n/(n-1)} \leq \prod_{i=1}^n \left(\int |\partial_i u|\right)^{1/(n-1)} \leq \|\nabla u\|_1^{n/(n-1)}$$

即 $\|u\|_{n/(n-1)} \leq \|\nabla u\|_1$。

**一般 $p < n$**：

用 $v = |u|^\gamma$ 代入 $p=1$ 情形，优化 $\gamma$。

得 $p^* = \frac{np}{n-p}$。$\square$

### (b) Rellich-Kondrachov紧嵌入

**证明概要：**

有界序列 $\{u_k\} \subset W^{1,p}(\Omega)$ 需证明在 $L^q$ 中有收敛子列。

**Step 1**：由Sobolev嵌入，$\{u_k\}$ 在 $L^{p^*}$ 中有界。

**Step 2**：用磨光或平移估计证明等度连续性（$L^q$ 意义下）。

**Step 3**：Arzelà-Ascoli类型的紧性论证。

或用对偶方法：$W^{1,p}$ 自反，弱收敛+范数收敛 $\Rightarrow$ 强收敛。

紧性来自低阶逼近：高频部分可被控制。$\square$

### (c) 三维情形

**解答：**

$n=3$，$p=2$：
$$p^* = \frac{3 \cdot 2}{3-2} = 6$$

Sobolev不等式：
$$\|u\|_{L^6(\Omega)} \leq C \|\nabla u\|_{L^2(\Omega)}$$

常数 $C$ 依赖 $\Omega$，但对 $\mathbb{R}^3$：
$$C = \frac{1}{\sqrt{3}\pi^{2/3}}$$

等价于：
$$\int_\Omega |u|^6 dx \leq C^6 \left(\int_\Omega |\nabla u|^2 dx\right)^3$$
$\square$

## 证明技巧

1. **逐点表示**：用积分表示函数值
2. **乘积技巧**：$|u|^\gamma$ 的插值
3. **紧性论证**：Arzelà-Ascoli + 逼近

## 常见错误

- ❌ Sobolev共轭指数计算错误
- ❌ 忘记 $kp=n$ 情形的临界嵌入（如BMO）
- ❌ 紧嵌入中 $q = p^*$ 不成立

## 变式练习

**变式1：** 证明Poincaré不等式：$\|u - \bar{u}\|_{L^p} \leq C \|\nabla u\|_{L^p}$。

**变式2：** 讨论 $W^{1,n}(\mathbb{R}^n)$ 的临界嵌入（Trudinger不等式）。
