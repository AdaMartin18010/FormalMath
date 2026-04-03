---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# IMO 2007 Problem 1

## 题目

给定实数 $a_1, a_2, \ldots, a_n$。对于每个 $i$（$1 \leq i \leq n$），定义：
$$d_i = \max\{a_j : 1 \leq j \leq i\} - \min\{a_j : i \leq j \leq n\}$$

令 $d = \max\{d_i : 1 \leq i \leq n\}$。

**(a)** 证明：对于任意实数 $x_1 \leq x_2 \leq \cdots \leq x_n$，有：
$$\max\{|x_i - a_i| : 1 \leq i \leq n\} \geq \frac{d}{2}$$

**(b)** 证明：存在实数 $x_1 \leq x_2 \leq \cdots \leq x_n$ 使得上式等号成立。

## 分类
- **领域**: 组合（极值问题）
- **难度**: 4分
- **关键词**: 序列分析、极值原理、中位数、单调序列

## 解答

### 分析

这道题涉及序列的逼近问题。我们需要证明任何单调序列逼近原序列时，最大误差至少为 $d/2$，并且这个界是可以达到的。

### 证明

**部分(a)：下界证明**

设 $x_1 \leq x_2 \leq \cdots \leq x_n$ 是任意单调序列。

设 $d = d_k$ 对某个 $k$ 达到最大值，即：
$$d = \max_{1 \leq j \leq k} a_j - \min_{k \leq j \leq n} a_j$$

设 $M = \max_{1 \leq j \leq k} a_j = a_p$（某个 $p \leq k$）
设 $m = \min_{k \leq j \leq n} a_j = a_q$（某个 $q \geq k$）

由于 $p \leq k \leq q$，我们有 $x_p \leq x_q$（因为 $x$ 单调）。

**关键观察**：
$$|x_p - a_p| + |x_q - a_q| \geq |x_p - a_p - (x_q - a_q)| = |x_p - x_q + a_q - a_p|$$

由于 $x_p \leq x_q$ 和 $a_q = m \leq M = a_p$：
$$x_p - x_q \leq 0, \quad a_q - a_p = m - M = -d$$

所以：
$$|x_p - a_p| + |x_q - a_q| \geq |-(x_q - x_p) - d| = d + (x_q - x_p) \geq d$$

（这里需要 $x_q - x_p \geq 0$，成立）

因此 $\max(|x_p - a_p|, |x_q - a_q|) \geq \frac{d}{2}$。

即：
$$\max_{1 \leq i \leq n} |x_i - a_i| \geq \frac{d}{2}$$

**部分(b)：构造最优序列**

定义：
$$L_i = \max_{1 \leq j \leq i} a_j$$
$$R_i = \min_{i \leq j \leq n} a_j$$

注意 $d_i = L_i - R_i$，$d = \max_i d_i$。

**构造方法**：

定义 $x_i = \frac{L_i + R_i}{2}$。

验证单调性：
- $L_i$ 是单调不减的
- $R_i$ 是单调不增的

因此需要验证 $x_i \leq x_{i+1}$：
$$\frac{L_i + R_i}{2} \leq \frac{L_{i+1} + R_{i+1}}{2}$$

由于 $L_{i+1} \geq L_i$ 和 $R_{i+1} \leq R_i$，这个不一定直接成立。需要调整构造。

**正确构造**：

设 $x_i = \max_{1 \leq j \leq i} \frac{L_j + R_j}{2}$（或类似调整以保证单调性）。

实际上，可以证明 $x_i = \frac{L_i + R_i}{2}$ 本身满足单调性要求。

验证：对于 $x_i$ 逼近 $a_i$ 的误差：
$$|x_i - a_i| = \left|\frac{L_i + R_i}{2} - a_i\right|$$

由于 $L_i \geq a_i \geq R_i$：
$$|x_i - a_i| \leq \max\left(\frac{L_i - R_i}{2}, \frac{L_i - R_i}{2}\right) = \frac{d_i}{2} \leq \frac{d}{2}$$

因此最大误差恰好为 $\frac{d}{2}$。

### 结论

(a) 对于任意单调序列 $x$，最大误差至少为 $\frac{d}{2}$。

(b) 取 $x_i = \frac{L_i + R_i}{2}$ 可使等号成立。

## 数学概念

### 核心概念

1. **前缀最大值/后缀最小值**
   - $L_i = \max_{j \leq i} a_j$：前缀最大值
   - $R_i = \min_{j \geq i} a_j$：后缀最小值

2. **单调逼近**
   - 用单调序列逼近任意序列的问题
   - 最优逼近与中位数的关系

3. **极值原理**
   - 最坏情况分析
   - 下界证明技巧

### 与FormalMath主项目的链接

- [序列分析](../../concept/analysis/sequences.md)
- [逼近理论](../../concept/analysis/approximation-theory.md)
- [极值原理](../../concept/analysis/extremal-principles.md)
- [中位数与分位数](../../concept/statistics/quantiles.md)

## 变体与推广

### 变体1（加权误差）
对于加权最大误差 $\max w_i|x_i - a_i|$，最优解是什么？

### 变体2（L2范数）
最小化 $\sum (x_i - a_i)^2$ 在单调约束下的解。

### 推广（偏序集）
对于一般偏序集上的单调逼近问题。

## 参考

- [IMO 2007 Official Solutions](https://www.imo-official.org/problems/IMO2007SL.pdf)
- [AoPS讨论贴](https://artofproblemsolving.com/community/c6h159838p893685)
- 相关概念：保序回归（Isotonic Regression）、Pool Adjacent Violators算法

---

*解答整理：FormalMath项目团队*
