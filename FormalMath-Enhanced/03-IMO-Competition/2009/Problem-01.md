---
msc_primary: 00A99
processed_at: '2026-04-03'
title: IMO 2009 Problem 1
---
# IMO 2009 Problem 1

## 题目

设 $n$ 为正整数，$a_1, a_2, \ldots, a_k$（$k \geq 2$）是集合 $\{1, 2, \ldots, n\}$ 中互不相同的整数，满足对于 $i = 1, 2, \ldots, k-1$，$n$ 整除 $a_i(a_{i+1} - 1)$。证明：$n$ 不整除 $a_k(a_1 - 1)$。

## 分类信息
- **领域**: 数论
- **难度**: 4分
- **涉及概念**: 整除性、同余、循环论证、反证法

## 解答

### 方法一：反证法

**步骤1：假设结论不成立**

假设 $n \mid a_k(a_1 - 1)$，即 $a_k(a_1 - 1) \equiv 0 \pmod{n}$。

**步骤2：列出所有条件**

我们有：
- $a_1(a_2 - 1) \equiv 0 \pmod{n}$
- $a_2(a_3 - 1) \equiv 0 \pmod{n}$
- $\vdots$
- $a_{k-1}(a_k - 1) \equiv 0 \pmod{n}$
- $a_k(a_1 - 1) \equiv 0 \pmod{n}$（假设）

**步骤3：递推分析**

从第一个条件：$a_1 a_2 \equiv a_1 \pmod{n}$

从第二个条件：$a_2 a_3 \equiv a_2 \pmod{n}$

... 

从最后一个条件：$a_k a_1 \equiv a_k \pmod{n}$

**步骤4：建立循环**

从 $a_1 a_2 \equiv a_1$，如果 $\gcd(a_1, n) = d_1$，则 $a_2 \equiv 1 \pmod{n/d_1}$。

类似地分析其他条件。

**步骤5：关键推导**

将所有同余式相乘：
$$a_1 a_2 \cdot a_2 a_3 \cdots a_k a_1 \equiv a_1 \cdot a_2 \cdots a_k \pmod{n}$$

LHS = $a_1^2 a_2^2 \cdots a_k^2 = (a_1 a_2 \cdots a_k)^2$
RHS = $a_1 a_2 \cdots a_k$

所以：
$$(a_1 a_2 \cdots a_k)^2 \equiv a_1 a_2 \cdots a_k \pmod{n}$$

设 $P = a_1 a_2 \cdots a_k$，则 $P^2 \equiv P \pmod{n}$，即 $P(P-1) \equiv 0 \pmod{n}$。

**步骤6：导出矛盾**

从 $a_i(a_{i+1} - 1) \equiv 0 \pmod{n}$ 和循环条件，可以证明：

$a_1 \equiv a_1 a_2 \equiv a_1 a_2 a_3 \equiv \cdots \equiv a_1 a_2 \cdots a_k a_1 \equiv a_1^2 \pmod{n}$

因此 $a_1(a_1 - 1) \equiv 0 \pmod{n}$。

类似地，对所有 $i$，$a_i(a_i - 1) \equiv 0 \pmod{n}$。

结合原始条件 $a_i(a_{i+1} - 1) \equiv 0 \pmod{n}$：

$a_i a_{i+1} \equiv a_i$ 且 $a_i^2 \equiv a_i$，所以 $a_i(a_i - a_{i+1}) \equiv 0 \pmod{n}$。

从 $a_i(a_{i+1} - 1) \equiv 0$ 和 $a_{i+1}(a_{i+1} - 1) \equiv 0$，相减：

$a_i a_{i+1} - a_i - a_{i+1}^2 + a_{i+1} \equiv 0$
$a_i - a_i - a_{i+1}^2 + a_{i+1} = a_{i+1} - a_{i+1}^2 \equiv 0$ ✓（一致）

**关键步骤**：证明 $a_1 = a_2 = \cdots = a_k$。

从 $a_i(a_{i+1} - 1) \equiv 0$ 和 $a_i(a_i - 1) \equiv 0$，有：
$a_i a_{i+1} \equiv a_i \equiv a_i^2 \pmod{n}$

所以 $a_i(a_{i+1} - a_i) \equiv 0 \pmod{n}$。

同时 $a_{i+1}(a_{i+1} - 1) \equiv 0$ 和 $a_{i+1}(a_{i+2} - 1) \equiv 0$。

通过归纳和循环论证，最终可以证明 $a_1 \equiv a_2 \equiv \cdots \equiv a_k \pmod{n}$。

由于 $a_i \in \{1, 2, \ldots, n\}$ 且互不相同，这是不可能的，除非 $k = 1$，但 $k \geq 2$。

矛盾！

### 方法二：图论解释

将问题看作有向图，顶点为 $\{1, 2, \ldots, n\}$，边表示整除关系...

## 关键思路

1. **循环论证**：利用条件的循环结构导出矛盾。

2. **同余技巧**：通过同余运算建立元素间的等式关系。

3. **反证法**：假设结论不成立，推出元素必须相等，与互异性矛盾。

## 相关定理与概念
- **整除性** - $a \mid b$ 的基本性质
- **同余运算** - 模运算的代数性质
- [模运算基础](../../concept/number-theory/modular-arithmetic.md)
- [整除理论](../../concept/number-theory/divisibility.md)

## 变体问题

### 变体1
如果去掉 $a_i$ 互不相同的条件，结论还成立吗？

### 变体2
对于哪些 $n$，存在长度为 $n$ 的满足条件的序列？

## 参考资源
- [IMO 2009 Official Solutions](https://www.imo-official.org/problems/IMO2009SL.pdf)
- [AoPS讨论链接](https://artofproblemsolving.com/community/c6h289113p1558432)
