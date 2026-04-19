---
number: "ANA-067"
category: 实分析
topic: 综合练习
difficulty: ⭐⭐⭐
title: Baire纲定理及其应用
msc_primary: 00A99
keywords: [Baire纲定理, 剩余集, 纲, 一致有界原理, 开映射]
prerequisites: [ANA-066, ANA-033]
source: 经典分析习题
---

## 题目

**Baire纲定理：** 完备度量空间是第二纲的（不能表示为可数个无处稠密集的并）。

**(a)** 证明：$[0,1]$ 不能表示为可数个无处稠密闭集的并。

**(b)** 证明连续无处可微函数在 $C[0,1]$ 中稠密（Baire意义下）。

**(c)** （一致有界原理）设 $X$ 是Banach空间，$Y$ 是赋范空间，$\{T_\alpha\}_{\alpha \in A} \subset \mathcal{L}(X,Y)$。若对每个 $x \in X$，$\sup_\alpha \|T_\alpha x\| < \infty$，证明 $\sup_\alpha \|T_\alpha\| < \infty$。

**(d)** 证明：无理数集是第二纲的，而有理数集是第一纲的。

## 详细解答

### (a) Baire纲定理的特殊情形

**证明：**

设 $[0,1] = \bigcup_{n=1}^{\infty} F_n$，每个 $F_n$ 是无处稠密闭集。

**步骤1：** $F_1$ 无处稠密，故 $\overline{F_1}^\circ = \emptyset$，即 $F_1^\circ = \emptyset$（$F_1$ 闭）。

$[0,1] \setminus F_1$ 是非空开集，包含某闭区间 $[a_1, b_1]$，$b_1 - a_1 < 1$。

**步骤2：** $F_2$ 无处稠密，$[a_1, b_1] \setminus F_2$ 含某闭区间 $[a_2, b_2] \subset (a_1, b_1)$，$b_2 - a_2 < \frac{1}{2}$。

**步骤n：** 归纳得到嵌套闭区间：
$$[a_1, b_1] \supset [a_2, b_2] \supset ... \supset [a_n, b_n] \supset ...$$

满足 $b_n - a_n < \frac{1}{n}$。

**步骤4：** 由区间套定理，存在唯一的 $x \in \bigcap_{n=1}^{\infty} [a_n, b_n]$。

但 $x \not\in F_n$ 对所有 $n$（因 $x \in [a_n, b_n] \subset [0,1] \setminus F_n$）。

故 $x \not\in \bigcup F_n = [0,1]$，矛盾！

**证毕。**

### (b) 无处可微函数的普遍性

**证明：**

设 $E_n = \{f \in C[0,1] : \exists x, |f(x+h) - f(x)| \leq n|h| \text{ 对某邻域}\}$（粗略描述）。

严格定义：设
$$E_{n,m} = \left\{f : \exists x, \forall |h| < \frac{1}{m}, \left|\frac{f(x+h)-f(x)}{h}\right| \leq n\right\}$$

可微函数 $\subset \bigcup_{n,m} E_{n,m}$。

**步骤1：** 证明 $E_{n,m}$ 闭

若 $f_k \in E_{n,m}$，$f_k \rightrightarrows f$，对应点 $x_k$。取子列 $x_k \to x$。

验证 $f \in E_{n,m}$。

**步骤2：** 证明 $E_{n,m}$ 无处稠密

对任意 $f \in C[0,1]$ 和 $\varepsilon > 0$，用Weierstrass逼近或分段线性函数逼近，再扰动使不可微。

实际上，多项式在 $E_{n,m}$ 外（多项式可微），且多项式稠密，故 $E_{n,m}^\circ = \emptyset$。

**步骤3：** 可微函数是第一纲集的子集

由Baire定理，$C[0,1]$（完备）不能是第一纲集。

故无处可微函数是剩余集（第二纲），特别稠密。

**证毕。**

### (c) 一致有界原理（共鸣定理）

**证明：**

设 $E_n = \{x \in X : \sup_\alpha \|T_\alpha x\| \leq n\} = \bigcap_\alpha \{x : \|T_\alpha x\| \leq n\}$。

每个 $\{x : \|T_\alpha x\| \leq n\}$ 是闭集（$T_\alpha$ 连续），故 $E_n$ 闭。

由假设，$\bigcup_{n=1}^{\infty} E_n = X$。

$X$ 是Banach空间（完备），由Baire定理，某 $E_N$ 含内点。

即存在 $x_0$，$r > 0$ 使 $B(x_0, r) \subset E_N$。

对任意 $\|x\| \leq 1$：
$$x_0 + \frac{r}{2}x \in B(x_0, r) \subset E_N$$

故 $\|T_\alpha(x_0 + \frac{r}{2}x)\| \leq N$ 对所有 $\alpha$。

$$\|T_\alpha x\| = \frac{2}{r}\|T_\alpha(x_0 + \frac{r}{2}x) - T_\alpha x_0\| \leq \frac{2}{r}(N + \sup_\alpha\|T_\alpha x_0\|)$$

因 $x_0$ 固定，$\sup_\alpha\|T_\alpha x_0\| < \infty$。

故 $\|T_\alpha\|$ 一致有界。

**证毕。**

### (d) 有理数与无理数的纲

**有理数集 $\mathbb{Q}$：**

$\mathbb{Q} = \bigcup_{q \in \mathbb{Q}} \{q\}$，单点集是无处稠密闭集。

$\mathbb{Q}$ 可数，故是第一纲集。

**无理数集 $\mathbb{R} \setminus \mathbb{Q}$：**

若 $\mathbb{R} \setminus \mathbb{Q}$ 是第一纲集，则：
$$\mathbb{R} = \mathbb{Q} \cup (\mathbb{R} \setminus \mathbb{Q})$$

是两个第一纲集的并，仍第一纲，与Baire定理矛盾。

故 $\mathbb{R} \setminus \mathbb{Q}$ 是第二纲集。

## 证明技巧

1. **Baire定理的证明核心：** 区间套/球套构造，利用完备性
2. **纲论证的模板：** 将目标集表示为$F_{\sigma}$，证明无处稠密
3. **一致有界原理的关键：** 从点态有界推出一致有界，需要完备性

## 常见错误

| 错误 | 说明 |
|------|------|
| 混淆第一纲与第二纲 | 第一纲="小"集合，第二纲="大"集合 |
| 忽略完备性要求 | Baire定理需要完备度量空间 |
| 证明无处稠密时忘记验证闭性 | 纲定理通常应用于闭集 |

## 变式练习

**变式1：** 证明开映射定理：Banach空间之间的满射有界线性算子是开映射。

**变式2：** 证明闭图像定理：图像闭的线性算子有界。

**变式3：** 证明：$[0,1]$ 上的单调函数集合在 $C[0,1]$ 中无处稠密。
