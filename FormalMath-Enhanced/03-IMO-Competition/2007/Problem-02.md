---
msc_primary: 00A99
processed_at: '2026-04-03'
title: IMO 2007 Problem 2
---
# IMO 2007 Problem 2

## 题目

考虑五个实数 $x_1, x_2, x_3, x_4, x_5$，满足：
$$\sum_{i=1}^5 x_i = 0 \quad \text{和} \quad \sum_{i=1}^5 x_i^2 = 10$$

求表达式 $\sum_{i=1}^5 x_i^3$ 的最大可能值。

## 分类

- **领域**: 代数（不等式/极值）
- **难度**: 2分
- **关键词**: 约束优化、Lagrange乘数法、对称多项式、极值原理

## 解答

### 分析

这是一个约束优化问题。我们需要在给定两个约束条件下，最大化立方和。

**约束条件**：

- $\sum x_i = 0$（零和）
- $\sum x_i^2 = 10$（固定平方和）

**目标**：最大化 $\sum x_i^3$

### 求解

**方法1：Lagrange乘数法**

设 $f(x) = \sum x_i^3$，约束 $g_1 = \sum x_i = 0$，$g_2 = \sum x_i^2 = 10$。

$$\nabla f = \lambda \nabla g_1 + \mu \nabla g_2$$

对每个 $i$：
$$3x_i^2 = \lambda + 2\mu x_i$$

这意味着每个 $x_i$ 满足二次方程：
$$3t^2 - 2\mu t - \lambda = 0$$

所以 $x_i$ 最多取两个不同的值，设为 $a$ 和 $b$。

**方法2：对称性假设**

设 $k$ 个变量等于 $a$，$5-k$ 个变量等于 $b$。

约束条件：
$$ka + (5-k)b = 0$$
$$ka^2 + (5-k)b^2 = 10$$

由第一式：$b = -\frac{ka}{5-k}$

代入第二式：
$$ka^2 + (5-k) \cdot \frac{k^2a^2}{(5-k)^2} = 10$$

$$ka^2 + \frac{k^2a^2}{5-k} = 10$$

$$ka^2\left(1 + \frac{k}{5-k}\right) = ka^2 \cdot \frac{5}{5-k} = 10$$

$$a^2 = \frac{2(5-k)}{k}$$

目标函数：
$$S = ka^3 + (5-k)b^3 = ka^3 + (5-k)\left(-\frac{ka}{5-k}\right)^3$$

$$= ka^3 - \frac{k^3a^3}{(5-k)^2} = ka^3\left(1 - \frac{k^2}{(5-k)^2}\right)$$

$$= ka^3 \cdot \frac{(5-k)^2 - k^2}{(5-k)^2} = ka^3 \cdot \frac{25 - 10k}{(5-k)^2}$$

$$= \frac{5ka^3(5-2k)}{(5-k)^2}$$

代入 $a^2 = \frac{2(5-k)}{k}$，取 $a > 0$：$a = \sqrt{\frac{2(5-k)}{k}}$

$$S = \frac{5k}{(5-k)^2} \cdot \left(\frac{2(5-k)}{k}\right)^{3/2} \cdot (5-2k)$$

$$= 5(5-2k) \cdot \frac{k}{(5-k)^2} \cdot \frac{(2(5-k))^{3/2}}{k^{3/2}}$$

$$= 5(5-2k) \cdot \frac{2^{3/2}(5-k)^{3/2}}{(5-k)^2 \cdot k^{1/2}}$$

$$= 5(5-2k) \cdot \frac{2\sqrt{2}}{\sqrt{k(5-k)}}$$

对 $k = 1, 2, 3, 4$ 计算：

**k = 1**：$S = 5 \cdot 3 \cdot \frac{2\sqrt{2}}{\sqrt{4}} = 15 \cdot \sqrt{2} = 15\sqrt{2}$

**k = 2**：$S = 5 \cdot 1 \cdot \frac{2\sqrt{2}}{\sqrt{6}} = \frac{10\sqrt{2}}{\sqrt{6}} = \frac{10\sqrt{3}}{3}$

**k = 3**：$S = 5 \cdot (-1) \cdot \frac{2\sqrt{2}}{\sqrt{6}} = -\frac{10\sqrt{3}}{3}$

**k = 4**：$S = 5 \cdot (-3) \cdot \frac{2\sqrt{2}}{\sqrt{4}} = -15\sqrt{2}$

比较正值：$15\sqrt{2} \approx 21.21$，$\frac{10\sqrt{3}}{3} \approx 5.77$

最大值在 $k = 1$ 时取得。

### 验证k=1的解

$k = 1$：$a^2 = \frac{2 \cdot 4}{1} = 8$，$a = 2\sqrt{2}$

$b = -\frac{1 \cdot 2\sqrt{2}}{4} = -\frac{\sqrt{2}}{2}$

验证约束：

- $\sum x_i = 2\sqrt{2} + 4 \cdot (-\frac{\sqrt{2}}{2}) = 2\sqrt{2} - 2\sqrt{2} = 0$ ✓
- $\sum x_i^2 = 8 + 4 \cdot \frac{1}{2} = 8 + 2 = 10$ ✓

目标值：$(2\sqrt{2})^3 + 4 \cdot (-\frac{\sqrt{2}}{2})^3 = 16\sqrt{2} + 4 \cdot (-\frac{\sqrt{2}}{4}) = 16\sqrt{2} - \sqrt{2} = 15\sqrt{2}$

### 结论

最大值为 $\boxed{15\sqrt{2}}$

## 数学概念

### 核心概念

1. **约束优化**
   - Lagrange乘数法
   - 等式约束下的极值

2. **对称多项式**
   - 幂和与基本对称多项式的关系
   - Newton恒等式

3. **极值原理**
   - 在边界/对称点取得极值

### 与FormalMath主项目的链接

- 优化理论
- Lagrange乘数法
- 对称多项式
- Newton恒等式

## 变体与推广

### 变体1（n元情形）

对于 $n$ 个实数，$\sum x_i = 0$，$\sum x_i^2 = S$，求 $\sum x_i^3$ 的最大值。

### 变体2（不同幂次）

在相同约束下，最大化 $\sum x_i^4$ 或更高次幂。

### 推广（一般约束）

对于约束 $\sum x_i = c_1$，$\sum x_i^2 = c_2$，研究 $\sum x_i^k$ 的极值。

## 参考

- [IMO 2007 Official Solutions](https://www.imo-official.org/problems/IMO2007SL.pdf)[需更新]
- [AoPS讨论贴](https://artofproblemsolving.com/community/c6h159839p893686)[需更新]
- 相关技巧：Lagrange乘数法、对称性假设

---

*解答整理：FormalMath项目团队*
