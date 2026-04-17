---
title: Weierstrass M-判别法
course: MIT 18.100A Real Analysis
level: silver
target_courses:
- MIT 18.100A
difficulty: 核心定理
importance: 高
prerequisites:
- 一致收敛
- 级数收敛
- 比较判别法
- Cauchy一致收敛准则
related:
- 一致收敛保持连续性
- 逐项积分
- 逐项求导
- 幂级数
tags:
- 实分析
- 函数项级数
- 一致收敛
- 核心定理
date: 2026-04-17
references:
  textbooks:
  - id: rudin_pma
    type: textbook
    title: Principles of Mathematical Analysis
    authors:
    - Walter Rudin
    publisher: McGraw-Hill
    edition: 3rd
    year: 1976
    isbn: 978-0070542358
    msc: 26-01
    chapters:
    - 'Chapter 7: Sequences and Series of Functions'
    url: null
    pages: 148-149
  databases:
  - id: nlab
    type: database
    name: nLab
    entry_url: https://ncatlab.org/nlab/show/{entry}
    consulted_at: 2026-04-17
  - id: stacks_project
    type: database
    name: Stacks Project
    entry_url: https://stacks.math.columbia.edu/tag/{tag}
    consulted_at: 2026-04-17
  - id: zbmath
    type: database
    name: zbMATH Open
    entry_url: https://zbmath.org/?q=an:{zb_id}
    consulted_at: 2026-04-17
---

# Weierstrass M-判别法

## 一、背景：点态收敛 vs 一致收敛

在分析函数项级数 $\sum_{n=1}^{\infty} u_n(x)$ 时，仅知道级数在每一点 $x$ 收敛（**点态收敛**）是不够的。点态收敛不能保持连续性、可积性和可微性。

**经典反例**：设 $f_n(x) = x^n$ 在 $[0, 1]$ 上。

- 每个 $f_n$ 都连续
- 点态极限为 $f(x) = \begin{cases} 0 & 0 \leq x < 1 \\ 1 & x = 1 \end{cases}$，不连续

**一致收敛**要求收敛速度在整个定义域上"均匀"，从而保证了极限运算的交换性。

---

## 二、定理陈述

**定理（Weierstrass M-判别法）**：设函数项级数 $\sum_{n=1}^{\infty} u_n(x)$ 定义在集合 $E \subseteq \mathbb{R}$ 上。若存在正数列 $\{M_n\}$ 使得：

1. $|u_n(x)| \leq M_n$ 对所有 $x \in E$ 和所有 $n \in \mathbb{N}$ 成立
2. 数项级数 $\sum_{n=1}^{\infty} M_n$ **收敛**

则函数项级数 $\sum_{n=1}^{\infty} u_n(x)$ 在 $E$ 上**一致收敛**（且绝对收敛）。

---

## 三、证明思路

Weierstrass M-判别法的证明核心是将函数项级数的一致收敛性问题转化为数项级数的收敛性问题：

1. 利用**Cauchy 一致收敛准则**：级数一致收敛当且仅当其部分和序列满足一致 Cauchy 条件
2. 由 $\sum M_n$ 收敛，应用数项级数的 Cauchy 准则
3. 利用不等式 $|u_n(x)| \leq M_n$ 将数项级数的 Cauchy 条件传递到函数项级数

---

## 四、详细证明

**给定**：函数项级数 $\sum_{n=1}^{\infty} u_n(x)$ 在 $E$ 上满足：

- $|u_n(x)| \leq M_n$ 对所有 $x \in E$ 成立
- $\sum_{n=1}^{\infty} M_n$ 收敛

**目标**：证明 $\sum_{n=1}^{\infty} u_n(x)$ 在 $E$ 上一致收敛。

---

### 步骤 1：写出一致收敛的 Cauchy 条件

**Cauchy 一致收敛准则**：函数项级数 $\sum u_n(x)$ 在 $E$ 上一致收敛，当且仅当：
$$\forall \varepsilon > 0, \, \exists N \in \mathbb{N}, \, \forall n > m \geq N, \, \forall x \in E: \left|\sum_{k=m+1}^{n} u_k(x)\right| < \varepsilon$$

---

### 步骤 2：应用数项级数的 Cauchy 准则

由于 $\sum M_n$ 收敛，由数项级数的 Cauchy 准则：
$$\forall \varepsilon > 0, \, \exists N \in \mathbb{N}, \, \forall n > m \geq N: \sum_{k=m+1}^{n} M_k < \varepsilon$$

---

### 步骤 3：估计函数项级数的部分和

对任意 $x \in E$ 和任意 $n > m \geq N$：
$$\left|\sum_{k=m+1}^{n} u_k(x)\right| \leq \sum_{k=m+1}^{n} |u_k(x)| \leq \sum_{k=m+1}^{n} M_k < \varepsilon$$

**关键观察**：

- 第一个不等式：三角不等式
- 第二个不等式：由条件 $|u_k(x)| \leq M_k$
- 第三个不等式：由步骤 2 中的 Cauchy 条件

注意：这里的 $N$ **仅依赖于** $\varepsilon$，**不依赖于** $x$。

---

### 步骤 4：得出结论

由 Cauchy 一致收敛准则，$\sum_{n=1}^{\infty} u_n(x)$ 在 $E$ 上**一致收敛**。

同时，由 $|u_n(x)| \leq M_n$ 和 $\sum M_n$ 收敛，对每个固定的 $x$，级数 $\sum |u_n(x)|$ 由比较判别法收敛，故原级数**绝对收敛**。∎

---

## 五、与 Lean4 形式化的对应

Weierstrass M-判别法在 Mathlib4 中有对应的实现思路：

```lean4
import Mathlib

open Topology Filter Set

-- Weierstrass M-判别法：若 |u_n(x)| ≤ M_n 且 Σ M_n 收敛，则 Σ u_n(x) 一致收敛
theorem weierstrass_M_test {α : Type*} [TopologicalSpace α]
    (u : ℕ → α → ℝ) (M : ℕ → ℝ)
    (hM : ∀ n x, |u n x| ≤ M n)
    (hsum : Summable M) :
    ∃ S : α → ℝ, Tendsto (fun n => fun x => ∑ k in Finset.range n, u k x) atTop (𝓝 S) := by
  -- 在实际 Mathlib 中，一致收敛使用 Tendsto 在一致拓扑下的刻画
  sorry  -- 需要 Mathlib 中关于一致收敛的完整框架
```

### 关键对应点

| 数学概念 | Lean4 对应 |
|---------|-----------|
| 函数项级数 | `fun n x => ∑ k in Finset.range n, u k x` |
| 一致收敛 | `Tendsto ... atTop (𝓝 S)` 在一致拓扑下 |
| 上确界范数 | `⨆ x, |f x|` |
| 级数收敛 | `Summable M` |

---

## 六、典型例题

### 例题 1：证明 $\sum_{n=1}^{\infty} \dfrac{\sin(nx)}{n^2}$ 在 $\mathbb{R}$ 上一致收敛

**证明**：令 $u_n(x) = \dfrac{\sin(nx)}{n^2}$，$M_n = \dfrac{1}{n^2}$。

1. **控制条件**：对所有 $x \in \mathbb{R}$：
   $$|u_n(x)| = \left|\frac{\sin(nx)}{n^2}\right| \leq \frac{1}{n^2} = M_n$$

2. **级数收敛**：$\sum_{n=1}^{\infty} \dfrac{1}{n^2}$ 是 $p = 2 > 1$ 的 $p$-级数，收敛。

由 **Weierstrass M-判别法**，$\sum_{n=1}^{\infty} \dfrac{\sin(nx)}{n^2}$ 在 $\mathbb{R}$ 上一致收敛。∎

**推论**：由于每一项 $u_n(x) = \dfrac{\sin(nx)}{n^2}$ 都连续，且级数一致收敛，因此和函数 $S(x) = \sum_{n=1}^{\infty} \dfrac{\sin(nx)}{n^2}$ 在 $\mathbb{R}$ 上连续。

---

### 例题 2：证明幂级数在其收敛半径内部的任意紧子集上一致收敛

**问题**：设幂级数 $\sum_{n=0}^{\infty} a_n x^n$ 的收敛半径为 $R > 0$。证明对任意 $0 < r < R$，该幂级数在 $[-r, r]$ 上一致收敛。

**证明**：

取 $x_0$ 满足 $r < x_0 < R$。由于幂级数在 $x_0$ 处收敛，数列 $\{a_n x_0^n\}$ 有界，即存在 $M > 0$ 使得 $|a_n x_0^n| \leq M$ 对所有 $n$ 成立。

对 $x \in [-r, r]$：
$$|a_n x^n| \leq |a_n| r^n = |a_n x_0^n| \cdot \left(\frac{r}{x_0}\right)^n \leq M \cdot \left(\frac{r}{x_0}\right)^n$$

令 $M_n = M \cdot \left(\dfrac{r}{x_0}\right)^n$。由于 $0 < \dfrac{r}{x_0} < 1$，几何级数 $\sum M_n$ 收敛。

由 **Weierstrass M-判别法**，幂级数在 $[-r, r]$ 上一致收敛。∎

---

## 七、常见误区分析

### ❌ 误区：混淆点态收敛与一致收敛

**错误陈述**："若 $\sum |u_n(x)| \leq \sum M_n$ 且 $\sum M_n$ 收敛，则 $\sum u_n(x)$ 点态收敛，所以已经够了。"

**纠正**：M-判别法的威力在于它证明的是**一致收敛**，而不仅仅是点态收敛。一致收敛保证了极限运算的交换性：

| 性质 | 点态收敛 | 一致收敛 |
|:---|:---:|:---:|
| 保持连续性 | ❌ 不保证 | ✅ 保证 |
| 逐项积分 | ❌ 不保证 | ✅ 保证 |
| 逐项求导 | ❌ 不保证 | 需要更强条件 |
| 极限与求和交换 | ❌ 不保证 | ✅ 保证 |

**反例**：设 $f_n(x) = x^n - x^{n+1}$ 在 $[0, 1]$ 上。

部分和 $S_N(x) = \sum_{n=0}^{N-1} (x^n - x^{n+1}) = 1 - x^N$（望远镜求和）。

- 点态极限：$S(x) = \begin{cases} 1 & 0 \leq x < 1 \\ 0 & x = 1 \end{cases}$
- 这个级数实际上是点态收敛的，但不一致收敛（因为极限函数不连续，而每项都连续）

这个例子说明，没有一致收敛，连续性和积分等性质都会丢失。

---

## 八、关键洞察

1. **M-判别法是充分非必要条件**：M-判别法是判断一致收敛的**充分条件**，但不是**必要条件。存在一些一致收敛的函数项级数，无法找到满足 M-判别法的控制级数（如某些 Dirichlet 型级数）。**

2. **一致收敛的"三大定理"**：
   - **连续性定理**：若 $u_n$ 连续且 $\sum u_n$ 一致收敛，则和函数连续
   - **逐项积分定理**：若 $u_n$ 连续且 $\sum u_n$ 在 $[a, b]$ 上一致收敛，则 $\int_a^b \sum u_n = \sum \int_a^b u_n$
   - **逐项求导定理**：若 $u_n'$ 连续且 $\sum u_n'$ 一致收敛，则 $\left(\sum u_n\right)' = \sum u_n'$

   Weierstrass M-判别法是验证这些定理条件的最常用工具。

3. **与幂级数理论的联系**：幂级数在其收敛半径内部的任意紧子集上都可以用 M-判别法证明一致收敛。这是幂级数具有优良分析性质（连续性、可逐项积分/求导）的根本原因。

---

*文档版本: 1.0 | 创建日期: 2026-04-17 | 对应课程: MIT 18.100A*
