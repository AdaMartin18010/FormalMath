---
id: ANA-010
title: Weierstrass M-判别法应用
difficulty: ⭐⭐⭐
type: application
topic: 实分析
course: MIT 18.100A Real Analysis
source: 经典方法
keywords: [Weierstrass M-判别法, 函数项级数, 一致收敛, 绝对收敛, 连续性保持]
author: FormalMath Team
version: 1.0
created: 2026-04-09
---

# ANA-010: Weierstrass M-判别法应用

## 题目陈述

**Weierstrass M-判别法**: 设 $\{f_n\}$ 是定义在集合 $E$ 上的函数序列。若存在正数序列 $\{M_n\}$ 使得

1. $|f_n(x)| \leq M_n$ 对所有 $x \in E$ 和 $n \in \mathbb{N}$ 成立
2. $\sum_{n=1}^{\infty} M_n$ 收敛

则 $\sum_{n=1}^{\infty} f_n(x)$ 在 $E$ 上**绝对且一致收敛**。

**问题**:

1. 证明 Weierstrass M-判别法
2. 用M-判别法判定下列级数的一致收敛性：
   - $\sum_{n=1}^{\infty} \frac{\sin(nx)}{n^2}$ on $\mathbb{R}$
   - $\sum_{n=1}^{\infty} \frac{x^n}{n!}$ on $[-R, R]$（对任意 $R > 0$）
   - $\sum_{n=1}^{\infty} \frac{1}{n^x}$ on $[a, \infty)$（$a > 1$）
3. 证明 $f(x) = \sum_{n=1}^{\infty} \frac{\cos(nx)}{n^2}$ 在 $\mathbb{R}$ 上连续
4. 讨论M-判别法的局限性和更精细的判别法

## 详细解答

### 例1：Weierstrass M-判别法的证明

**定理**: 在上述条件下，$\sum f_n$ 在 $E$ 上绝对且一致收敛。

**证明**:

**步骤1：逐点绝对收敛**

对每个固定的 $x \in E$，$\sum |f_n(x)| \leq \sum M_n < \infty$。

由比较判别法，$\sum f_n(x)$ 绝对收敛。定义 $S(x) = \sum_{n=1}^{\infty} f_n(x)$。

**步骤2：一致收敛的Cauchy准则**

对任意 $\varepsilon > 0$，由于 $\sum M_n$ 收敛，存在 $N$ 使得
$$\sum_{k=n+1}^{m} M_k < \varepsilon \quad \text{对所有 } m > n \geq N$$

**步骤3：估计部分和的尾部**

对 $m > n \geq N$ 和任意 $x \in E$：
$$\left|\sum_{k=n+1}^{m} f_k(x)\right| \leq \sum_{k=n+1}^{m} |f_k(x)| \leq \sum_{k=n+1}^{m} M_k < \varepsilon$$

**步骤4：令 $m \to \infty$**

$$\left|\sum_{k=n+1}^{\infty} f_k(x)\right| = |S(x) - S_n(x)| \leq \varepsilon$$

对所有 $n \geq N$ 和 $x \in E$ 成立。故一致收敛。 $\square$

---

### 例2：级数的一致收敛性判定

#### 2.1 $\sum_{n=1}^{\infty} \frac{\sin(nx)}{n^2}$ on $\mathbb{R}$

**估计**: 对所有 $x \in \mathbb{R}$：
$$\left|\frac{\sin(nx)}{n^2}\right| \leq \frac{1}{n^2}$$

**判别**: 取 $M_n = \frac{1}{n^2}$，$\sum M_n = \sum \frac{1}{n^2} = \frac{\pi^2}{6} < \infty$。

**结论**: 由M-判别法，级数在 $\mathbb{R}$ 上**绝对且一致收敛**。 $\square$

---

#### 2.2 $\sum_{n=1}^{\infty} \frac{x^n}{n!}$ on $[-R, R]$

**估计**: 对 $x \in [-R, R]$：
$$\left|\frac{x^n}{n!}\right| \leq \frac{R^n}{n!}$$

**判别**: 取 $M_n = \frac{R^n}{n!}$，由比值判别法：
$$\frac{M_{n+1}}{M_n} = \frac{R^{n+1}}{(n+1)!} \cdot \frac{n!}{R^n} = \frac{R}{n+1} \to 0$$

故 $\sum M_n$ 收敛（实际上是 $e^R$）。

**结论**: 级数在 $[-R, R]$ 上**绝对且一致收敛**（对任意 $R > 0$）。 $\square$

**注**: 这证明了 $e^x$ 的幂级数在任何有界区间上一致收敛。

---

#### 2.3 $\sum_{n=1}^{\infty} \frac{1}{n^x}$ on $[a, \infty)$（$a > 1$）

**估计**: 对 $x \geq a$：
$$\frac{1}{n^x} \leq \frac{1}{n^a}$$

**判别**: 取 $M_n = \frac{1}{n^a}$，由于 $a > 1$，$\sum M_n$ 收敛（p-级数）。

**结论**: 级数在 $[a, \infty)$ 上**绝对且一致收敛**（$a > 1$）。 $\square$

**注**: 这是Riemann zeta函数 $\zeta(x)$ 的部分和，在 $x > 1$ 的任何紧子集上一致收敛。

---

### 例3：连续性证明

**问题**: 证明 $f(x) = \sum_{n=1}^{\infty} \frac{\cos(nx)}{n^2}$ 在 $\mathbb{R}$ 上连续。

**证明**:

**步骤1：验证M-判别法条件**

对每个 $n$，$f_n(x) = \frac{\cos(nx)}{n^2}$ 在 $\mathbb{R}$ 上连续。

估计：$|f_n(x)| \leq \frac{1}{n^2} = M_n$，且 $\sum M_n < \infty$。

**步骤2：应用M-判别法**

$\sum f_n$ 在 $\mathbb{R}$ 上一致收敛于 $f$。

**步骤3：一致收敛保持连续性**

每个 $f_n$ 连续，一致收敛极限保持连续性。

故 $f$ 在 $\mathbb{R}$ 上连续。 $\square$

**扩展**: 事实上，由于 $\sum \frac{n}{n^2} = \sum \frac{1}{n}$ 发散，不能直接对 $f$ 逐项微分。但可以证明 $f$ 在 $\mathbb{R} \setminus 2\pi\mathbb{Z}$ 上可导。

---

### 例4：M-判别法的局限性

#### 局限性1：不能处理条件收敛

**例**: $\sum_{n=1}^{\infty} \frac{(-1)^n}{n}$ 收敛（交错级数），但M-判别法不适用。

原因：若取 $M_n = \frac{1}{n}$，则 $\sum M_n$ 发散。

**替代**: Abel判别法或Dirichlet判别法。

---

#### 局限性2：估计可能过粗糙

**例**: $\sum_{n=1}^{\infty} \frac{\sin(nx)}{n}$ on $[\delta, 2\pi - \delta]$（$\delta > 0$）。

直接估计：$|\frac{\sin(nx)}{n}| \leq \frac{1}{n}$，但 $\sum \frac{1}{n}$ 发散，M-判别法失效。

**事实**: 该级数在 $[\delta, 2\pi - \delta]$ 上**确实一致收敛**（用Dirichlet判别法）。

---

#### 局限性3：端点问题

**例**: $\sum_{n=1}^{\infty} \frac{x^n}{n}$ on $[-1, 1)$。

- 在 $[-1, 1-\delta]$ 上可用M-判别法
- 在 $[-1, 1)$ 整体上不能用（$x$ 接近1时项不趋于0）

**事实**: 级数在 $[-1, 1)$ 上一致收敛（需要Abel定理）。

---

#### 更精细的判别法

| 判别法 | 条件 | 适用场景 |
|--------|------|---------|
| **Weierstrass M** | $|f_n| \leq M_n$，$\sum M_n < \infty$ | 绝对收敛 |
| **Abel** | $\sum a_n$ 收敛，$b_n$ 单调有界 | 条件收敛 |
| **Dirichlet** | $S_n = \sum_{k=1}^n a_k$ 有界，$b_n \downarrow 0$ | 振荡级数 |
| **Dini** | 紧集上连续，单调逐点收敛 | 单调序列 |

## 证明技巧总结

### M-判别法的应用策略

```
1. 分析目标：确定函数的定义域 E
2. 逐项估计：找出 |f_n(x)| 在 E 上的上界
3. 选择 M_n：M_n 应尽可能小但保证 ΣM_n 收敛
4. 验证收敛：用比较、比值、根值等方法验证 ΣM_n < ∞
5. 得出结论：级数绝对且一致收敛
```

### 常见函数的估计技巧

| 函数类型 | 估计方法 | 典型M_n |
|----------|---------|---------|
| 三角函数 | 有界性 | $M \cdot a_n$ |
| 指数函数 | 指数增长 | $R^n / n!$ |
| 有理函数 | 分母次数 | $1/n^p$ ($p > 1$) |
| 对数函数 | 慢增长 | $(\log n)^{-p}$ |

### 从一致收敛导出性质

```
若 Σf_n 在 E 上一致收敛：
✓ 连续性：每个 f_n 连续 ⇒ 和函数连续
✓ 积分交换：∫(Σf_n) = Σ(∫f_n)
✓ 有界性：每个 f_n 有界 ⇒ 和函数有界
? 可微性：需要 Σf_n' 也一致收敛
```

## 常见错误分析

### 错误1：忽视定义域的影响

```
❌ 错误：对 Σx^n/n! 声称在 R 上"一致收敛"

✅ 正确：在任何有界区间上一致收敛，但在 R 上不整体一致收敛

💡 理由：sup_{x∈R} |x^n/n!| = ∞，无法找到统一的 M_n
```

### 错误2：M_n 选取不当

```
❌ 错误：对 Σsin(nx)/n^2，取 M_n = 1/n

✅ 正确：应取 M_n = 1/n^2

💡 原则：M_n 要同时满足 |f_n| ≤ M_n 和 ΣM_n < ∞
```

### 错误3：混淆点态与一致收敛

```
❌ 错误："Σf_n 在每个点收敛，故一致收敛"

✅ 正确：点态收敛 + 控制条件 ⇒ 一致收敛

💡 Weierstrass M-判别法提供了充分条件，非必要
```

### 错误4：忽视端点/边界

```
❌ 错误：对 Σ1/n^x 在 (1, ∞) 上用 M_n = 1/n^a（固定 a>1）

✅ 正确：需对每个 [a, ∞)（a>1）单独验证

💡 整体上 sup |1/n^x| = 1/n，Σ1/n 发散
```

## 变式练习

### 变式1（难度⭐⭐）

证明级数 $\sum_{n=1}^{\infty} \frac{x}{n(1+nx^2)}$ 在 $\mathbb{R}$ 上一致收敛。

<details>
<summary>提示</summary>
对固定的 $n$，求 $g_n(x) = \frac{x}{1+nx^2}$ 的最大值。

$g_n'(x) = 0$ 得 $x = \pm 1/\sqrt{n}$，最大值 $g_n(1/\sqrt{n}) = \frac{1}{2\sqrt{n}}$。

因此
$$\left|\frac{x}{n(1+nx^2)}\right| \leq \frac{1}{2n^{3/2}}$$

取 $M_n = \frac{1}{2n^{3/2}}$，$\sum M_n$ 收敛（p-级数，$p=3/2 > 1$）。 $\square$
</details>

### 变式2（难度⭐⭐⭐）

设 $f(x) = \sum_{n=1}^{\infty} \frac{e^{-nx}}{n^2}$ for $x \geq 0$。

1. 证明 $f$ 在 $[0, \infty)$ 上连续
2. 证明 $f$ 在 $(0, \infty)$ 上可导
3. 计算 $f'(x)$ for $x > 0$

<details>
<summary>提示</summary>
<strong>第一部分</strong>：
- 在 $[0, \infty)$ 上：$|e^{-nx}/n^2| \leq 1/n^2$，M-判别法
- 每项连续，一致收敛 ⇒ $f$ 连续

<strong>第二部分</strong>：

- 形式逐项微分：$\sum -e^{-nx}/n$
- 在 $[\delta, \infty)$（$\delta > 0$）上：$|e^{-nx}/n| \leq e^{-n\delta}/n \leq e^{-n\delta}$
- $\sum e^{-n\delta} = 1/(e^\delta - 1) < \infty$
- 故在 $[\delta, \infty)$ 上可逐项微分
- 由于 $\delta > 0$ 任意，在 $(0, \infty)$ 上可导

<strong>第三部分</strong>：
$$f'(x) = -\sum_{n=1}^{\infty} \frac{e^{-nx}}{n} = -\sum_{n=1}^{\infty} \frac{(e^{-x})^n}{n} = \ln(1 - e^{-x})$$
（利用 $-\ln(1-t) = \sum_{n=1}^{\infty} t^n/n$）
</details>

### 变式3（难度⭐⭐⭐⭐）

证明：若 $\sum a_n$ 绝对收敛，则 $\sum a_n \sin(nx)$ 和 $\sum a_n \cos(nx)$ 都在 $\mathbb{R}$ 上一致收敛。

由此证明：若 $\sum |a_n| < \infty$，则 $\sum a_n \sin(nx)$ 是 $\mathbb{R}$ 上的连续函数。

<details>
<summary>提示</summary>
<strong>一致收敛</strong>：
$$|a_n \sin(nx)| \leq |a_n|, \quad |a_n \cos(nx)| \leq |a_n|$$

取 $M_n = |a_n|$，由 $\sum |a_n| < \infty$ 和M-判别法即得。

<strong>连续性</strong>：

- 每个 $a_n \sin(nx)$ 在 $\mathbb{R}$ 上连续
- 级数一致收敛
- 一致收敛保持连续性

故和函数连续。 $\square$

<strong>应用</strong>：Fourier级数理论的基础结果。
</details>

## 相关概念链接

### 前置知识

- [ANA-009: 一致收敛与极限交换](./ANA-009-一致收敛与极限交换.md)
- [SER-001: 数项级数收敛判别法](../../级数/SER-001-数项级数收敛判别法.md)

### 后继内容

- [FOU-001: Fourier级数基础](../../傅里叶分析/FOU-001-Fourier级数基础.md)
- [CMP-001: 复变函数的一致收敛](../../复分析/CMP-001-复变函数的一致收敛.md)

### 扩展阅读

- [Abel判别法](../../级数/Abel判别法.md)
- [Dirichlet判别法](../../级数/Dirichlet判别法.md)
- [正规收敛](../../级数/正规收敛.md)
- [Fourier级数的一致收敛](../../傅里叶分析/Fourier级数的一致收敛.md)

### 外部资源

- MIT 18.100A Lecture Notes: Series of Functions
- Rudin 《Principles of Mathematical Analysis》Theorem 7.10
- Abbott 《Understanding Analysis》Section 6.4

---

**标签**: #Weierstrass-M-判别法 #函数项级数 #一致收敛 #绝对收敛 #连续性保持 #实分析 #MIT-18.100A
