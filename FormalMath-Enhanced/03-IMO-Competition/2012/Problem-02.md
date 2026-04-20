---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: IMO 2012 Problem 02
---

# IMO 2012 Problem 02

## 题目

设 $a_2, a_3, \ldots, a_n$ 是正实数，满足 $a_2 \cdot a_3 \cdots a_n = 1$。证明：
$$(a_2 + 1)^2 \cdot (a_3 + 1)^3 \cdots (a_n + 1)^n > n^n$$

## 分类信息
- **领域**: 代数（不等式）
- **难度**: 5分
- **涉及概念**: AM-GM不等式、加权不等式

## 解答

### 方法一：逐项AM-GM估计

**关键观察**：对每个因子 $(a_k + 1)^k$（$k = 2, 3, \ldots, n$），我们将 $a_k + 1$ 拆分为 $k$ 个非负项的算术平均。

具体地，对 $k \geq 2$：
$$a_k + 1 = \underbrace{\frac{a_k}{k-1} + \frac{a_k}{k-1} + \cdots + \frac{a_k}{k-1}}_{k-1 \text{ 个}} + 1$$

注意这里有 $k$ 个项（$k-1$ 个 $\frac{a_k}{k-1}$ 和一个 $1$），它们的算术平均为：
$$\frac{(k-1) \cdot \frac{a_k}{k-1} + 1}{k} = \frac{a_k + 1}{k}$$

由AM-GM不等式：
$$a_k + 1 = \sum_{i=1}^{k-1} \frac{a_k}{k-1} + 1 \geq k \cdot \left(\frac{a_k}{k-1}\right)^{\frac{k-1}{k}} \cdot 1^{\frac{1}{k}} = k \cdot \left(\frac{a_k}{k-1}\right)^{\frac{k-1}{k}}$$

因此：
$$(a_k + 1)^k \geq k^k \cdot \left(\frac{a_k}{k-1}\right)^{k-1} = \frac{k^k}{(k-1)^{k-1}} \cdot a_k^{k-1}$$

**乘积估计**：

将所有这些不等式相乘（$k = 2, 3, \ldots, n$）：
$$\prod_{k=2}^n (a_k + 1)^k \geq \prod_{k=2}^n \frac{k^k}{(k-1)^{k-1}} \cdot \prod_{k=2}^n a_k^{k-1}$$

**计算第一个乘积（望远镜积）**：
$$\prod_{k=2}^n \frac{k^k}{(k-1)^{k-1}} = \frac{2^2}{1^1} \cdot \frac{3^3}{2^2} \cdot \frac{4^4}{3^3} \cdots \frac{n^n}{(n-1)^{n-1}} = n^n$$

**计算第二个乘积**：
$$\prod_{k=2}^n a_k^{k-1} = a_2^1 \cdot a_3^2 \cdot a_4^3 \cdots a_n^{n-1}$$

这个乘积看起来不简单。让我们重新思考拆分方式。

**修正的拆分策略**：

对每个 $(a_k + 1)^k$，我们拆分为 $k$ 个相等的项：
$$a_k + 1 = \underbrace{\frac{1}{k} + \frac{1}{k} + \cdots + \frac{1}{k}}_{k \text{ 个}} + a_k$$

不，这不对。正确的拆分是：

$$a_k + 1 = \frac{a_k}{k-1} + \cdots + \frac{a_k}{k-1} + 1$$

然后 $(a_k + 1)^k$ 对应 $k$ 个项的 $k$ 次幂。但AM-GM应用于 $a_k + 1$ 本身（不是 $k$ 次幂）：

$$a_k + 1 \geq k \cdot \left(\frac{a_k}{k-1}\right)^{\frac{k-1}{k}}$$

这给出：
$$(a_k + 1)^k \geq k^k \cdot \frac{a_k^{k-1}}{(k-1)^{k-1}}$$

乘积为：
$$\prod_{k=2}^n (a_k + 1)^k \geq n^n \cdot \prod_{k=2}^n \frac{a_k^{k-1}}{(k-1)^{k-1}}$$

为了利用 $a_2 a_3 \cdots a_n = 1$，我们需要 $\prod a_k^{k-1}$ 与 $\prod a_k$ 相关联。

实际上，令 $b_k = a_k^{k-1}$，则我们需要 $\prod b_k^{1/(k-1)} = \prod a_k = 1$。

但 $\prod_{k=2}^n a_k^{k-1} = a_2^1 a_3^2 \cdots a_n^{n-1}$ 不一定等于1。

**正确的AM-GM拆分**：

对每个 $k$，将 $a_k + 1$ 拆分为：
$$a_k + 1 = \underbrace{\frac{1}{k-1} + \frac{1}{k-1} + \cdots + \frac{1}{k-1}}_{k-1 \text{ 个}} + a_k$$

共 $k$ 个项。由AM-GM：
$$a_k + 1 \geq k \cdot \left(\frac{a_k}{(k-1)^{k-1}}\right)^{1/k} = k \cdot \frac{a_k^{1/k}}{(k-1)^{(k-1)/k}}$$

因此：
$$(a_k + 1)^k \geq k^k \cdot \frac{a_k}{(k-1)^{k-1}}$$

**乘积**：
$$\prod_{k=2}^n (a_k + 1)^k \geq \prod_{k=2}^n \frac{k^k}{(k-1)^{k-1}} \cdot \prod_{k=2}^n a_k = n^n \cdot 1 = n^n$$

由于等号成立要求每个AM-GM的等号条件满足，即对每个 $k$：
$$\frac{1}{k-1} = a_k$$

即 $a_k = \frac{1}{k-1}$。但此时 $a_2 a_3 \cdots a_n = 1 \cdot \frac{1}{2} \cdot \frac{1}{3} \cdots \frac{1}{n-1} = \frac{1}{(n-1)!} \neq 1$（当 $n > 2$）。

因此等号不成立，严格不等式成立：$\prod_{k=2}^n (a_k + 1)^k > n^n$。$\square$

## 关键思路

1. **望远镜积构造**：选择拆分方式使乘积产生望远镜效应，最终得到 $n^n$
2. **AM-GM的精细应用**：将 $a_k + 1$ 拆分为 $k$ 个项（$k-1$ 个 $\frac{1}{k-1}$ 和一个 $a_k$），这是本题的精妙之处
3. **等号不可达性**：验证等号条件与约束条件 $a_2 \cdots a_n = 1$ 矛盾，从而得到严格不等式

## 相关定理与概念
- **AM-GM不等式**：对非负实数 $x_1, \ldots, x_n$，$\frac{x_1 + \cdots + x_n}{n} \geq \sqrt[n]{x_1 \cdots x_n}$
- **望远镜积**：$\prod_{k=2}^n \frac{k^k}{(k-1)^{k-1}} = n^n$
- **加权AM-GM**：带权重的算术-几何平均不等式

## 变体问题

### 变体1
对正实数 $a_1, \ldots, a_n$ 满足 $\prod a_i = 1$，求 $\prod (1 + a_i)^{w_i}$ 的下界（$w_i$ 为权重）。

### 变体2
对正实数 $a, b, c$ 满足 $abc = 1$，证明 $(1+a)^2(1+b)^3(1+c)^4 > 2^2 \cdot 3^3 \cdot 4^4 / (1^1 \cdot 2^2 \cdot 3^3)$。

## 参考资源
- [IMO 2012 Official Solutions](https://www.imo-official.org/problems/IMO2012SL.pdf)
- [AoPS讨论链接](https://artofproblemsolving.com/community/c6h488344)

---

*解答整理：FormalMath项目团队*
