---
number: "ANA-069"
category: 实分析
topic: 综合练习
difficulty: ⭐⭐⭐⭐
title: 函数空间中的紧致性理论
msc_primary: 00A99
keywords: [等度连续, Arzelà-Ascoli, 函数空间, 相对紧致, 相对列紧]
prerequisites: [ANA-068, ANA-060]
source: 经典分析习题
---

## 题目

设 $(X, d)$ 是紧致度量空间，$C(X)$ 是连续函数空间，赋予上确界范数。

**(a)** 证明 $\mathcal{F} \subset C(X)$ 相对紧致（闭包紧致）当且仅当 $\mathcal{F}$ 一致有界且等度连续。

**(b)** 设 $K \subset \mathbb{R}^n$ 紧致，$\alpha \in (0,1]$。定义Hölder空间：
$$\text{Lip}_\alpha(K) = \left\{f : |f(x) - f(y)| \leq L|x-y|^\alpha, \|f\|_\infty \leq M\right\}$$
证明这是 $C(K)$ 中的紧致子集。

**(c)** 设 $\{f_n\} \subset C[0,1]$ 满足 $\int_0^1 f_n^2 \leq 1$ 和 $\int_0^1 (f_n')^2 \leq 1$。证明有在 $L^2$ 和 $C[0,1]$ 中都收敛的子列。

**(d)** 证明Ascoli定理的推广：若 $X$ 是局部紧致Hausdorff空间，$\mathcal{F} \subset C_0(X)$（在无穷远消失的连续函数），等度连续且等度消失，则 $\mathcal{F}$ 相对紧致。

## 详细解答

### (a) Arzelà-Ascoli定理的完整形式

**证明：**

**($\Rightarrow$) 相对紧致 $\Rightarrow$ 一致有界且等度连续**

设 $\overline{\mathcal{F}}$ 紧致。

**一致有界：** 紧致度量空间中的集合完全有界，故有界。

**等度连续：** 紧致集上的连续函数一致连续。对 $\varepsilon > 0$，$\overline{\mathcal{F}}$ 有有限 $\varepsilon/3$-网 $\{g_1, ..., g_k\}$。

每个 $g_i$ 一致连续，存在 $\delta_i$。取 $\delta = \min \delta_i$。

对任意 $f \in \mathcal{F}$，存在 $g_i$ 使 $\|f - g_i\|_\infty < \varepsilon/3$。

$d(x,y) < \delta$ 时：
\begin{align*}
|f(x) - f(y)| &\leq |f(x) - g_i(x)| + |g_i(x) - g_i(y)| + |g_i(y) - f(y)| \\
&< \frac{\varepsilon}{3} + \frac{\varepsilon}{3} + \frac{\varepsilon}{3} = \varepsilon
\end{align*}

**($\Leftarrow$) 一致有界且等度连续 $\Rightarrow$ 相对紧致**

设 $\mathcal{F}$ 一致有界且等度连续。

**步骤1：** $X$ 紧致，故可分。设 $\{x_1, x_2, ...\}$ 可数稠密。

**步骤2：** 对角线法提取逐点收敛子列（同ANA-060(c)）。

**步骤3：** 等度连续 + 逐点收敛在稠密集 $\Rightarrow$ 一致收敛

对 $\varepsilon > 0$，取等度连续的 $\delta$。用有限 $\delta$-网覆盖 $X$。

在有限个点上逐点收敛，故最终一致逼近。

**证毕。**

### (b) Hölder空间的紧致性

**证明：**

需证 $\text{Lip}_\alpha(K)$ 一致有界且等度连续。

**一致有界：** 由定义 $\|f\|_\infty \leq M$。

**等度连续：** 对 $f \in \text{Lip}_\alpha(K)$：
$$|f(x) - f(y)| \leq L|x-y|^\alpha$$

给定 $\varepsilon > 0$，取 $\delta = (\varepsilon/L)^{1/\alpha}$，则 $|x-y| < \delta$ 时 $|f(x) - f(y)| < \varepsilon$。

这对所有 $f$ 同时成立，故等度连续。

由Arzelà-Ascoli，$\text{Lip}_\alpha(K)$ 相对紧致。

**注：** 这是紧嵌入定理 $C^{0,\alpha} \hookrightarrow C^0$ 紧致。

**证毕。**

### (c) Sobolev空间的紧嵌入

**证明：**

这是Rellich-Kondrachov定理的一维特例。

**步骤1：** 一致有界性

由ANA-060(d)的方法，从 $\int (f_n')^2 \leq 1$ 和 $\int f_n^2 \leq 1$ 得 $\|f_n\|_\infty \leq C$。

**步骤2：** 等度连续性

$$|f_n(x) - f_n(y)| = \left|\int_y^x f_n'\right| \leq |x-y|^{1/2} \|f_n'\|_{L^2} \leq |x-y|^{1/2}$$

故等度连续。

**步骤3：** 应用Arzelà-Ascoli

有子列 $f_{n_k} \rightrightarrows f$ 一致收敛，故也在 $L^2$ 中收敛。

**证毕。**

### (d) 局部紧致情形的Ascoli定理

**证明概要：**

$X$ 局部紧致Hausdorff，可用单点紧化 $X^* = X \cup \{\infty\}$。

$C_0(X)$ 可延拓到 $C(X^*)$：$\tilde{f}(\infty) = 0$。

**等度消失：** 对 $\varepsilon > 0$，存在紧致 $K \subset X$ 使 $|f(x)| < \varepsilon$ 对 $x \not\in K$ 和所有 $f$。

这保证函数在"无穷远"一致小。

在 $K$ 上应用Arzelà-Ascoli，结合等度消失条件，得整体紧致性。

**证毕。**

## 证明技巧

1. **函数空间紧致的判断：** 一致有界 + 等度连续是核心
2. **Sobolev嵌入：** 积分的有界性蕴含点态控制
3. **局部紧致的单点紧化：** 将问题约化到紧致情形

## 常见错误

| 错误 | 说明 |
|------|------|
| 等度连续与一致连续混淆 | 等度连续要求$\delta$与函数无关 |
| 忘记验证等度消失 | 非紧致情形需要额外条件 |
| Hölder指数与可微性混淆 | $\alpha = 1$是Lipschitz，$\alpha > 1$意味着常数 |

## 变式练习

**变式1：** 证明 $C^k[a,b]$ 到 $C^{k-1}[a,b]$ 的嵌入是紧致的。

**变式2：** 设 $\{f_n\}$ 在 $\mathbb{R}$ 上等度连续且一致有界，证明有在紧集上一致收敛的子列。

**变式3：** 用Arzelà-Ascoli证明Montel定理：全纯函数族的正规性。
