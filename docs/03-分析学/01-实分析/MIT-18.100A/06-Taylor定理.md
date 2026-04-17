---
title: Taylor 定理（Taylor's Theorem）
course: MIT 18.100A Real Analysis
level: "silver"
target_courses: ["MIT 18.100A"]
difficulty: 核心定理
importance: 极高
prerequisites: [中值定理, 高阶导数, 数学归纳法, 连续性]
related: [中值定理, 罗尔定理, 洛必达法则, 幂级数]
tags: [实分析, 微分学, Taylor定理, 核心定理]
date: 2026-04-17
---

# Taylor 定理（Taylor's Theorem）

## 一、定理陈述

**定理（带 Lagrange 余项的 Taylor 定理）**：设函数 $f$ 在包含点 $a$ 的某个开区间 $I$ 内有 $n+1$ 阶导数。则对任意 $x \in I$，存在介于 $a$ 与 $x$ 之间的某个点 $c$（即 $c \in (a, x)$ 或 $c \in (x, a)$），使得：

$$f(x) = \underbrace{\sum_{k=0}^{n} \frac{f^{(k)}(a)}{k!}(x - a)^k}_{\text{Taylor 多项式 } P_n(x)} + \underbrace{\frac{f^{(n+1)}(c)}{(n+1)!}(x - a)^{n+1}}_{\text{Lagrange 余项 } R_n(x)}$$

**等价表述**：函数 $f$ 在点 $a$ 附近可以用一个 $n$ 次多项式逼近，误差项由 $f$ 的 $n+1$ 阶导数在某中间点 $c$ 处的值控制。

**特殊情形**：

- 当 $n = 0$ 时，Taylor 定理退化为**中值定理**：
  $$f(x) = f(a) + f'(c)(x - a)$$
- 当 $a = 0$ 时，称为**Maclaurin 展开**

---

## 二、证明思路

Taylor 定理是中值定理的**高阶推广**。证明的核心策略与中值定理类似：构造一个辅助函数，反复应用**罗尔定理**。

1. **定义余项函数**：$R_n(t) = f(t) - P_n(t)$，其中 $P_n(t)$ 是 $n$ 阶 Taylor 多项式
2. **观察性质**：$R_n(a) = R_n'(a) = R_n''(a) = \cdots = R_n^{(n)}(a) = 0$
3. **构造辅助函数**：引入一个含参数 $K$ 的函数 $F(t)$，使得 $F(x) = 0$
4. **反复应用罗尔定理**：利用 $F$ 及其各阶导数在多个点为零的性质，找到某点 $c$ 使得 $F^{(n+1)}(c) = 0$
5. **解出 $K$**：$K$ 恰好就是 Lagrange 余项

---

## 三、详细证明

不失一般性，假设 $a < x$。（若 $x < a$，证明完全对称。）

### 步骤 1：定义 Taylor 多项式和余项

记 $n$ 阶 Taylor 多项式：
$$P_n(t) = \sum_{k=0}^{n} \frac{f^{(k)}(a)}{k!}(t - a)^k$$

定义余项：
$$R_n(t) = f(t) - P_n(t)$$

### 步骤 2：分析余项在 $t = a$ 处的性质

直接计算可得：
$$R_n(a) = f(a) - f(a) = 0$$
$$R_n'(a) = f'(a) - f'(a) = 0$$
$$R_n''(a) = f''(a) - f''(a) = 0$$
$$\vdots$$
$$R_n^{(n)}(a) = f^{(n)}(a) - f^{(n)}(a) = 0$$

且：
$$R_n^{(n+1)}(t) = f^{(n+1)}(t)$$
（因为 $P_n$ 是 $n$ 次多项式，其 $n+1$ 阶导数为零）

### 步骤 3：构造辅助函数

我们的目标是找到 $K$ 使得：
$$R_n(x) = K \cdot (x - a)^{n+1}$$

定义辅助函数：
$$F(t) = R_n(t) - K \cdot (t - a)^{n+1}$$

要求 $F(x) = 0$，即：
$$K = \frac{R_n(x)}{(x - a)^{n+1}} = \frac{f(x) - P_n(x)}{(x - a)^{n+1}}$$

### 步骤 4：反复应用罗尔定理

**验证 $F$ 的性质**：

- $F(a) = R_n(a) - K \cdot 0 = 0$
- $F(x) = 0$（由 $K$ 的定义）

**第一次应用罗尔定理**：

由于 $F$ 在 $[a, x]$ 上连续，在 $(a, x)$ 内可导，且 $F(a) = F(x) = 0$，存在 $c_1 \in (a, x)$ 使得：
$$F'(c_1) = 0$$

**分析 $F'$**：
$$F'(t) = R_n'(t) - K \cdot (n+1)(t - a)^n$$

- $F'(a) = R_n'(a) - 0 = 0$
- $F'(c_1) = 0$

**第二次应用罗尔定理**：

存在 $c_2 \in (a, c_1)$ 使得：
$$F''(c_2) = 0$$

**归纳继续**：

一般地，若 $F^{(k)}$ 在 $a$ 和某点 $c_k$ 处为零，则存在 $c_{k+1} \in (a, c_k)$ 使得 $F^{(k+1)}(c_{k+1}) = 0$。

重复此过程 $n+1$ 次，最终得到存在 $c \in (a, c_n) \subseteq (a, x)$ 使得：
$$F^{(n+1)}(c) = 0$$

### 步骤 5：计算 $F^{(n+1)}(c)$ 并解出 $K$

$$F^{(n+1)}(t) = R_n^{(n+1)}(t) - K \cdot (n+1)!$$

在 $t = c$ 处：
$$0 = F^{(n+1)}(c) = R_n^{(n+1)}(c) - K \cdot (n+1)! = f^{(n+1)}(c) - K \cdot (n+1)!$$

因此：
$$K = \frac{f^{(n+1)}(c)}{(n+1)!}$$

回代到 $F(x) = 0$ 的表达式：
$$f(x) - P_n(x) = R_n(x) = K \cdot (x - a)^{n+1} = \frac{f^{(n+1)}(c)}{(n+1)!}(x - a)^{n+1}$$

即：
$$f(x) = \sum_{k=0}^{n} \frac{f^{(k)}(a)}{k!}(x - a)^k + \frac{f^{(n+1)}(c)}{(n+1)!}(x - a)^{n+1}$$

**结论**：Taylor 定理得证。∎

---

## 四、双语对照：自然语言证明 ↔ Lean4 代码

### Taylor 定理在 Mathlib4 中的表述

```lean4
-- 带拉格朗日余项的 Taylor 公式
theorem taylor_lagrange {f : ℝ → ℝ} {a b : ℝ} {n : ℕ} (hab : a < b)
    (h_continuous : ContinuousOn f (Icc a b))
    (h_differentiable : ∀ k ≤ n, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a b))
    (h_diff_n1 : DifferentiableOn ℝ (iteratedDeriv (n + 1) f) (Ioo a b)) :
    ∃ c ∈ Ioo a b, f b = ∑ k in Finset.range (n + 1),
      (iteratedDeriv k f a) / k.factorial * (b - a)^k +
      (iteratedDeriv (n + 1) f c) / (n + 1).factorial * (b - a)^(n + 1) := by
```

### 核心对应

| 数学概念 | Lean4 对应 |
|---------|-----------|
| $k$ 阶导数 | `iteratedDeriv k f` |
| Taylor 多项式 | `∑ k in Finset.range (n + 1), (iteratedDeriv k f a) / k.factorial * (b - a)^k` |
| Lagrange 余项 | `(iteratedDeriv (n + 1) f c) / (n + 1).factorial * (b - a)^(n + 1)` |
| 区间 $(a, b)$ | `Ioo a b` |
| 闭区间 $[a, b]$ | `Icc a b` |

---

## 五、典型例题

### 例题 1：$e^x$ 的 Maclaurin 展开及误差估计

**问题**：写出 $e^x$ 在 $a = 0$ 处的 3 阶 Taylor 展开，并估计 $x = 1$ 时的误差。

**解答**：由于 $f^{(k)}(x) = e^x$ 对所有 $k$ 成立，故 $f^{(k)}(0) = 1$。

$$e^x = 1 + x + \frac{x^2}{2!} + \frac{x^3}{3!} + \frac{e^c}{4!}x^4$$

其中 $c$ 介于 $0$ 与 $x$ 之间。

当 $x = 1$ 时：
$$e \approx 1 + 1 + \frac{1}{2} + \frac{1}{6} = \frac{16}{6} = \frac{8}{3} \approx 2.6667$$

**误差估计**：
$$|R_3(1)| = \frac{e^c}{24} \cdot 1^4 \leq \frac{e}{24} < \frac{3}{24} = 0.125$$

（因为 $c \in (0, 1)$，$e^c < e < 3$）

实际值 $e \approx 2.7183$，真实误差约为 $0.0516$。∎

---

### 例题 2：证明 $\sin x = x - \dfrac{x^3}{3!} + \dfrac{x^5}{5!} - \cdots$

**问题**：写出 $\sin x$ 在 $a = 0$ 处的 Taylor 展开。

**解答**：计算各阶导数在 $0$ 处的值：

| $k$ | $f^{(k)}(x)$ | $f^{(k)}(0)$ |
|:---:|:---|:---:|
| 0 | $\sin x$ | $0$ |
| 1 | $\cos x$ | $1$ |
| 2 | $-\sin x$ | $0$ |
| 3 | $-\cos x$ | $-1$ |
| 4 | $\sin x$ | $0$ |
| 5 | $\cos x$ | $1$ |

规律：$f^{(k)}(0) = \begin{cases} 0 & k \text{ 偶数} \\ (-1)^{\frac{k-1}{2}} & k \text{ 奇数} \end{cases}$

因此：
$$\sin x = x - \frac{x^3}{3!} + \frac{x^5}{5!} - \frac{x^7}{7!} + \cdots + R_n(x)$$

对于任意固定的 $x$，余项满足：
$$|R_n(x)| = \left|\frac{f^{(n+1)}(c)}{(n+1)!} x^{n+1}\right| \leq \frac{|x|^{n+1}}{(n+1)!} \to 0$$

因此：
$$\sin x = \sum_{k=0}^{\infty} (-1)^k \frac{x^{2k+1}}{(2k+1)!}$$

对所有 $x \in \mathbb{R}$ 成立。∎

---

## 六、常见误区分析

### ❌ 误区：忽视余项的重要性

**错误陈述**："Taylor 展开就是 $f(x) = \sum \dfrac{f^{(k)}(a)}{k!}(x-a)^k$。"

**纠正**：等号成立需要**余项趋于零**的保证。没有余项分析，等号不一定成立。

**反例**：考虑函数：
$$f(x) = \begin{cases} e^{-1/x^2} & x \neq 0 \\ 0 & x = 0 \end{cases}$$

这个函数在 $x = 0$ 处的所有阶导数都存在且等于 0：
$$f^{(k)}(0) = 0 \quad \text{对所有 } k \geq 0$$

因此其 Taylor 多项式为 $P_n(x) = 0$（对所有 $n$）。但 $f(x) \neq 0$ 对 $x \neq 0$。

这意味着：
$$f(x) \neq \sum_{k=0}^{\infty} \frac{f^{(k)}(0)}{k!}x^k = 0$$

**教训**：即使函数无限可导，其 Taylor 级数也不一定收敛于函数本身。必须验证余项是否趋于零。

---

## 七、关键洞察

1. **Taylor 定理 = 中值定理的高阶推广**：当 $n = 0$ 时，Taylor 定理 precisely 就是中值定理。因此，Taylor 定理将"一阶线性逼近 + 误差"推广到了"任意阶多项式逼近 + 高阶误差"。

2. **余项的两种常见形式**：
   - **Lagrange 余项**：$R_n(x) = \dfrac{f^{(n+1)}(c)}{(n+1)!}(x-a)^{n+1}$，适用于误差估计
   - **Cauchy 余项**：$R_n(x) = \dfrac{f^{(n+1)}(c)}{n!}(x-c)^n(x-a)$，在某些收敛性证明中更方便

3. **解析函数**：若函数 $f$ 在某点 $a$ 的某个邻域内可以表示为收敛的幂级数，则称 $f$ 在 $a$ 处**解析**。所有解析函数都是无限可导的，但反之不成立（如上例中的 $e^{-1/x^2}$）。

---

*文档版本: 1.0 | 创建日期: 2026-04-17 | 对应课程: MIT 18.100A*
