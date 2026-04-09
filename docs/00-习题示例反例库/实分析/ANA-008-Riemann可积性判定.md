---
id: ANA-008
title: Riemann可积性判定
difficulty: ⭐⭐⭐
type: proof
topic: 实分析
course: MIT 18.100A Real Analysis
source: 经典方法
keywords: [Riemann积分, Darboux和, 可积性条件, 不连续点, Lebesgue零测集]
author: FormalMath Team
version: 1.0
created: 2026-04-09
---

# ANA-008: Riemann可积性判定

## 题目陈述

**定义（Riemann积分）**: 设 $f: [a, b] \to \mathbb{R}$ 有界。$f$ 称为**Riemann可积**，如果对任意 $\varepsilon > 0$，存在分划 $P$ 使得
$$U(P, f) - L(P, f) < \varepsilon$$

其中 $U(P, f)$ 和 $L(P, f)$ 分别是关于分划 $P$ 的Darboux上和与Darboux下和。

**问题**:

1. 证明：若 $f$ 在 $[a, b]$ 上连续，则 $f$ 可积
2. 证明：若 $f$ 在 $[a, b]$ 上单调，则 $f$ 可积
3. 设 $f(x) = \begin{cases} 0 & x \in \mathbb{Q} \cap [0, 1] \\ 1 & x \in [0, 1] \setminus \mathbb{Q} \end{cases}$（Dirichlet函数），证明 $f$ 不可积
4. 叙述并简要证明 Lebesgue 可积性准则

## 详细解答

### 例1：连续函数可积

**定理**: 若 $f$ 在 $[a, b]$ 上连续，则 $f$ 在 $[a, b]$ 上Riemann可积。

**证明**:

**步骤1：一致连续性**

$[a, b]$ 是紧集，$f$ 连续，故 $f$ 在 $[a, b]$ 上一致连续。

**步骤2：控制振幅**

对任意 $\varepsilon > 0$，由一致连续性，存在 $\delta > 0$ 使得
$$|x - y| < \delta \Rightarrow |f(x) - f(y)| < \frac{\varepsilon}{b - a}$$

**步骤3：构造分划**

取分划 $P = \{x_0, x_1, \ldots, x_n\}$ 满足 $\|P\| = \max_i (x_i - x_{i-1}) < \delta$。

在每个子区间 $[x_{i-1}, x_i]$ 上，由连续性，存在 $\xi_i, \eta_i$ 使得
$$M_i = \sup_{[x_{i-1}, x_i]} f = f(\xi_i), \quad m_i = \inf_{[x_{i-1}, x_i]} f = f(\eta_i)$$

**步骤4：估计上和减下和**

$$U(P, f) - L(P, f) = \sum_{i=1}^n (M_i - m_i)(x_i - x_{i-1})$$

由于 $|\xi_i - \eta_i| \leq x_i - x_{i-1} < \delta$，有
$$M_i - m_i = f(\xi_i) - f(\eta_i) < \frac{\varepsilon}{b - a}$$

因此
$$U(P, f) - L(P, f) < \sum_{i=1}^n \frac{\varepsilon}{b - a}(x_i - x_{i-1}) = \frac{\varepsilon}{b - a} \cdot (b - a) = \varepsilon$$

由可积性判别法，$f$ 可积。 $\square$

---

### 例2：单调函数可积

**定理**: 若 $f$ 在 $[a, b]$ 上单调，则 $f$ 在 $[a, b]$ 上Riemann可积。

**证明**（设 $f$ 递增）：

**步骤1：构造等距分划**

对任意 $\varepsilon > 0$，取 $n$ 充分大使得
$$\frac{(b - a)(f(b) - f(a))}{n} < \varepsilon$$

取等距分划 $P = \{x_0, x_1, \ldots, x_n\}$，其中 $x_i = a + i\frac{b-a}{n}$。

**步骤2：计算Darboux和**

由于 $f$ 递增：

- $M_i = \sup_{[x_{i-1}, x_i]} f = f(x_i)$
- $m_i = \inf_{[x_{i-1}, x_i]} f = f(x_{i-1})$

**步骤3：望远镜求和**

$$U(P, f) - L(P, f) = \sum_{i=1}^n (f(x_i) - f(x_{i-1}))(x_i - x_{i-1})$$

由于子区间等长，$x_i - x_{i-1} = \frac{b-a}{n}$：

$$= \frac{b-a}{n} \sum_{i=1}^n (f(x_i) - f(x_{i-1})) = \frac{b-a}{n}(f(b) - f(a)) < \varepsilon$$

故 $f$ 可积。 $\square$

---

### 例3：Dirichlet函数不可积

**定理**: Dirichlet函数 $f: [0, 1] \to \mathbb{R}$
$$f(x) = \begin{cases} 0 & x \in \mathbb{Q} \\ 1 & x \notin \mathbb{Q} \end{cases}$$

在 $[0, 1]$ 上不可积。

**证明**:

对任意分划 $P = \{x_0, x_1, \ldots, x_n\}$：

**在每个子区间 $[x_{i-1}, x_i]$ 上**：

- 有理数稠密，故存在有理数 $q \in [x_{i-1}, x_i]$，$f(q) = 0$
- 无理数稠密，故存在无理数 $r \in [x_{i-1}, x_i]$，$f(r) = 1$

因此：

- $M_i = \sup_{[x_{i-1}, x_i]} f = 1$
- $m_i = \inf_{[x_{i-1}, x_i]} f = 0$

**计算Darboux和**：
$$U(P, f) = \sum_{i=1}^n M_i (x_i - x_{i-1}) = \sum_{i=1}^n 1 \cdot (x_i - x_{i-1}) = 1$$
$$L(P, f) = \sum_{i=1}^n m_i (x_i - x_{i-1}) = \sum_{i=1}^n 0 \cdot (x_i - x_{i-1}) = 0$$

因此
$$U(P, f) - L(P, f) = 1 - 0 = 1$$

对任意分划都成立，不满足可积条件。 $\square$

---

### 例4：Lebesgue可积性准则

**定理（Lebesgue）**: 有界函数 $f: [a, b] \to \mathbb{R}$ Riemann可积当且仅当 $f$ 的不连续点集是**零测集**（Lebesgue零测）。

**零测集定义**: $E \subset \mathbb{R}$ 称为零测集，如果对任意 $\varepsilon > 0$，存在可数个开区间 $\{I_n\}$ 覆盖 $E$ 且 $\sum_n |I_n| < \varepsilon$。

**简要证明思路**：

**（⇒）可积 ⇒ 不连续点零测**：

设 $D$ 为不连续点集，$D_n = \{x: \omega_f(x) \geq 1/n\}$，其中 $\omega_f(x)$ 是 $f$ 在 $x$ 处的振幅。

则 $D = \bigcup_n D_n$。证明每个 $D_n$ 零测（用可积性条件）。可数并零测。

**（⇐）不连续点零测 ⇒ 可积**：

将 $[a, b]$ 分为两部分：

1. 不连续点附近：总长度可任意小，函数值有界，贡献可忽略
2. 连续点集：利用一致连续性（在紧子集上）控制振幅

综合得可积。 $\square$

**应用**：

- 连续函数：不连续点集为空，零测 ✓
- 单调函数：不连续点至多可数，零测 ✓
- Dirichlet函数：在无理点连续？不，处处不连续，$D = [0, 1]$ 非零测 ✗

## 证明技巧总结

### Riemann可积性的判定方法

| 方法 | 适用场景 | 核心工具 |
|------|---------|---------|
| **定义法** | 通用 | $U(P,f) - L(P,f) < \varepsilon$ |
| **连续性** | 连续函数 | 一致连续性 |
| **单调性** | 单调函数 | 振幅控制 + 望远镜求和 |
| **Lebesgue准则** | 复杂函数 | 不连续点分析 |

### 构造分划的策略

```
1. 连续函数：利用一致连续性，等距或自适应分划
2. 单调函数：等距分划即可，振幅 telescoping
3. 有限个间断点：在间断点附近细分，其他区域粗略
4. 一般情形：利用振幅函数控制，分层处理
```

### 不可积函数的证明模板

```
目标：证明 inf_P U(P,f) ≠ sup_P L(P,f)

方法：
1. 证明对所有分划 P，U(P,f) ≥ c₁
2. 证明对所有分划 P，L(P,f) ≤ c₂
3. 证明 c₁ > c₂

常用技巧：利用稠密性，在每个子区间上上下确界差距大
```

## 常见错误分析

### 错误1：混淆点态连续与一致连续

```
❌ 错误："f连续，故振幅可任意小"而不指定区间

✅ 正确：需要一致连续性，即δ不依赖于点的位置

💡 关键：在紧集上连续 ⇔ 一致连续
```

### 错误2：忽视函数有界性前提

```
❌ 错误：讨论无界函数的Riemann可积性

✅ 正确：Riemann积分定义要求函数有界

💡 无界函数的"积分"是反常积分，需单独讨论
```

### 错误3：Lebesgue准则的误用

```
❌ 错误："有限个不连续点 ⇒ 可积，无限个 ⇒ 不可积"

✅ 正确：关键是零测，而非有限/无限

💡 反例：
   - Riemann函数：不连续点=ℚ，可数（零测），可积
   - Cantor函数：不连续点为空，可积
   - 单调函数：不连续点至多可数，可积
```

### 错误4：Darboux和计算错误

```
❌ 错误：对Dirichlet函数计算积分值为0或1

✅ 正确：上和=1，下和=0，不可积

💡 注意：
   - 上和用sup，下和用inf
   - 每个子区间都要考虑
```

## 变式练习

### 变式1（难度⭐⭐）

设 $f$ 在 $[a, b]$ 上有界，且只有有限个间断点。证明 $f$ 在 $[a, b]$ 上Riemann可积。

<details>
<summary>提示</summary>
设间断点为 $c_1 < c_2 < \cdots < c_n$。

对任意 $\varepsilon > 0$，在每个 $c_i$ 附近取小区间 $(c_i - \delta, c_i + \delta)$，总长度 $2n\delta$。

在这些小区间上：上和-下和 ≤ $2M \cdot 2n\delta$（$M$ 是 $|f|$ 的上界）

在剩余部分：$f$ 连续，故可积分划使得上和-下和 < $\varepsilon/2$

取 $\delta$ 充分小使得 $4nM\delta < \varepsilon/2$，综合即得。 $\square$
</details>

### 变式2（难度⭐⭐⭐）

**Riemann函数**：$f: [0, 1] \to \mathbb{R}$
$$f(x) = \begin{cases} \frac{1}{q} & x = \frac{p}{q} \in \mathbb{Q}, \gcd(p,q) = 1, q > 0 \\ 0 & x \notin \mathbb{Q} \end{cases}$$

证明 $f$ 在无理点连续，在有理点间断，且Riemann可积，积分值为0。

<details>
<summary>提示</summary>
<strong>连续性分析</strong>：
- 无理点 $x$：对任意 $\varepsilon > 0$，使 $f(p/q) \geq \varepsilon$ 的有理数只有有限个（因 $q \leq 1/\varepsilon$）
- 故存在邻域不含这些有理数，$|f(y)| < \varepsilon$，连续
- 有理点：附近有无理点使 $f=0$，故间断

<strong>可积性</strong>：不连续点=ℚ，可数，零测。由Lebesgue准则，可积。

<strong>积分值</strong>：对任意分划，$L(P,f) = 0$（因每个区间有无理点），故 $\underline{\int} f = 0$。可积则积分值为0。
</details>

### 变式3（难度⭐⭐⭐⭐）

设 $f$ 在 $[a, b]$ 上可积，$g$ 在 $f$ 的值域上连续。证明 $g \circ f$ 在 $[a, b]$ 上可积。

<details>
<summary>提示</summary>
设 $E$ 是 $f$ 的不连续点集（零测），$F$ 是 $g \circ f$ 的不连续点集。

关键：若 $f$ 在 $x$ 连续且 $g$ 在 $f(x)$ 连续，则 $g \circ f$ 在 $x$ 连续。

因此 $F \subset E \cup f^{-1}(D)$，其中 $D$ 是 $g$ 的不连续点集。

由于 $g$ 连续，$D = \emptyset$，故 $F \subset E$ 零测。

由Lebesgue准则，$g \circ f$ 可积。 $\square$

<strong>注</strong>：这是复合函数可积性定理，说明可积性在连续复合下保持。
</details>

## 相关概念链接

### 前置知识

- [INT-001: 积分的定义](../../基础/INT-001-积分的定义.md)
- [ANA-006: 一致连续性的判定](./ANA-006-一致连续性的判定.md)

### 后继内容

- [ANA-009: 一致收敛与极限交换](./ANA-009-一致收敛与极限交换.md)
- [ANA-010: Weierstrass M-判别法应用](./ANA-010-Weierstrass-M-判别法应用.md)

### 扩展阅读

- [Lebesgue积分](../../实变函数/Lebesgue积分.md)
- [反常积分](../../微积分/反常积分.md)
- [Stieltjes积分](../../实分析/Stieltjes积分.md)

### 外部资源

- MIT 18.100A Lecture Notes: Riemann Integration
- Rudin 《Principles of Mathematical Analysis》Chapter 6
- Abbott 《Understanding Analysis》Section 7.2-7.6

---

**标签**: #Riemann积分 #Darboux和 #可积性条件 #不连续点 #Lebesgue零测集 #实分析 #MIT-18.100A
