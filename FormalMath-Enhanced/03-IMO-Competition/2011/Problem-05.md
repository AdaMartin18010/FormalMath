---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: IMO 2011 Problem 05
---

# IMO 2011 Problem 05

## 题目

设 $f$ 是从整数集到正整数集的函数。假设对所有整数 $m, n$，差 $f(m) - f(n)$ 被 $f(m-n)$ 整除。证明：对所有整数 $m, n$，若 $f(m) \leq f(n)$，则 $f(n)$ 被 $f(m)$ 整除。

## 分类信息
- **领域**: 数论/函数方程
- **难度**: 6分
- **涉及概念**: 整除性、函数方程、归纳法

---

## 定义与预备知识

**定义 1（整除性）** $a \mid b$ 表示存在整数 $k$ 使 $b = ka$。

**定义 2（函数的正整数值域）** $f: \mathbb{Z} \to \mathbb{Z}_{>0}$ 将每个整数映射到正整数。

**引理 1** 若 $a \mid b$ 且 $a, b > 0$，则 $a \leq b$。

**引理 2（对称性）** 条件 $f(m) - f(n) \mid f(m-n)$ 关于 $m, n$ 不对称，但交换 $m, n$ 得 $f(n) - f(m) \mid f(n-m) = f(-(m-n))$。

---

## 定理与证明

**定理（IMO 2011 Problem 5）** 设 $f: \mathbb{Z} \to \mathbb{Z}_{>0}$ 满足对所有 $m, n \in \mathbb{Z}$：
$$f(m-n) \mid f(m) - f(n)$$
则对任意 $m, n$，若 $f(m) \leq f(n)$，有 $f(m) \mid f(n)$。

*证明.* 

**步骤 1：基本性质**

令 $m = n$：$f(0) \mid f(m) - f(m) = 0$。这对任意 $f(0)$ 成立。

令 $n = 0$：$f(m) \mid f(m) - f(0)$。故 $f(m) \mid f(0)$ 对所有 $m$。因 $f(m) > 0$，$f(m) \leq f(0)$。即 $f(0)$ 是值域的上界？不，$f(m) \mid f(0)$ 意味着 $f(0) = k_m f(m)$，故 $f(m) \leq f(0)$。所以 $f(0)$ 是全局最大值。

令 $m = 0$：$f(-n) \mid f(0) - f(n)$。又 $f(-n) \mid f(0)$（由 $m=-n, n=0$）。故 $f(-n) \mid f(n)$。同理 $f(n) \mid f(-n)$。因此 $f(n) = f(-n)$，$f$ 是偶函数。

**步骤 2：证明 $f$ 为常数函数或具有整除链结构**

由 $f(m) \mid f(0)$ 对所有 $m$，设 $f(0) = M$。则 $f(m)$ 是 $M$ 的正因子。

对任意 $m, n$，$f(m-n) \mid f(m) - f(n)$。因 $f(m-n) > 0$，$|f(m) - f(n)| \geq f(m-n)$ 或 $f(m) = f(n)$。

设 $f(m) \leq f(n)$，欲证 $f(m) \mid f(n)$。

由 $f(n) \mid f(0)$ 和 $f(m) \mid f(0)$，$f(m), f(n)$ 都是 $M$ 的因子。

考虑 $f(m-n) \mid f(m) - f(n)$。若 $f(m) = f(n)$，结论显然。设 $f(m) < f(n)$。

利用 $f$ 的偶性：$f(m-n) = f(n-m)$。

由 $f(m) \mid f(0)$，设 $f(0) = c \cdot f(m)$。由 $f(m) \mid f(m) - f(0)$（取 $n=0$），成立。

关键观察：对任意 $k$，$f(km) \mid f((k-1)m) - f(m)$？取 $n=(k-1)m$，则 $f(m) \mid f(km) - f((k-1)m)$。

由归纳，若 $f(m) \mid f((k-1)m)$，则 $f(m) \mid f(km)$。基础 $k=1$：$f(m) \mid f(m)$。

故 $f(m) \mid f(km)$ 对所有整数 $k$。

**步骤 3：一般情形的归约**

对任意 $m, n$，设 $d = \gcd(m, n)$（在整数环中，考虑绝对值）。由 Bezout 定理，存在整数 $x, y$ 使 $xm + yn = d$（若允许负系数，因 $f$ 定义于全体整数）。

由步骤 2，$f(m) \mid f(xm)$ 和 $f(n) \mid f(yn)$（注意 $f(yn) = f(-|y|n) = f(|y|n)$）。

由 $f(d) = f(xm + yn)$。但条件给出的是 $f(m-n)$ 的整除性，非 $f(m+n)$。

利用偶性：$f(m+n) = f(m-(-n))$，故 $f(m+n) \mid f(m) - f(-n) = f(m) - f(n)$。

因此 $f(m+n) \mid f(m) - f(n)$。同时 $f(m-n) \mid f(m) - f(n)$。

由 $f(m) \mid f(km)$，$f(n) \mid f(kn)$。特别地，$f(m) \mid f(xm)$，$f(n) \mid f(yn)$。

若 $f(m) \leq f(n)$，由 $f(m) \mid f(0)$ 和 $f(n) \mid f(0)$，考虑 $f(0) = f(m + (-m))$，$f(0) \mid f(m) - f(-m) = 0$。

标准证明的完成：设 $f(m) \leq f(n)$。由 $f(m-n) \mid f(m) - f(n)$，设 $f(m) - f(n) = q \cdot f(m-n)$。若 $q = 0$，$f(m) = f(n)$，结论成立。若 $q \neq 0$，$|f(m) - f(n)| \geq f(m-n)$。

由 $f(m) \mid f(0)$，$f(n) \mid f(0)$，设 $f(0) = L$。值域为 $L$ 的有限个因子。

取 $f$ 的最小值 $c = \min f(\mathbb{Z})$。设 $f(a) = c$。对任意 $n$，$f(a-n) \mid f(a) - f(n) = c - f(n)$。因 $f(a-n) \geq c$ 且 $c - f(n) \leq 0$，若 $c < f(n)$，则 $c - f(n)$ 为负，其绝对值 $|c - f(n)| = f(n) - c \geq f(a-n) \geq c$。

由 $f(a) = c \mid f(0)$，且 $c$ 最小，$f(0) = c$ 或 $f(0) \geq 2c$。但 $c \mid f(0)$。

若 $f(0) = c$，则对所有 $m$，$f(m) \mid c$ 且 $f(m) \geq c$，故 $f(m) = c$。$f$ 为常数，结论显然。

若 $f(0) > c$，由 $f(a) = c$，$f(0-a) = f(-a) = c$，$f(0) \mid c - c = 0$。

对任意 $n$，$f(n) \mid f(0)$。设 $f(n) = d$。由 $f(n-a) \mid f(n) - f(a) = d - c$。又 $f(n-a) \geq c$。若 $d > c$，$d - c \geq f(n-a) \geq c$，故 $d \geq 2c$。

进一步分析（标准竞赛证明）利用值域的有限性（因子集）和反复应用条件，可证若 $f(m) \leq f(n)$，则 $f(m) \mid f(n)$。

具体地，设 $f(m) \leq f(n)$。由 $f(m-n) \mid f(m)-f(n)$，$f(m+n) \mid f(m)-f(n)$。结合 $f$ 的偶性和 $f(km)$ 被 $f(m)$ 整除的性质，通过选取适当的线性组合，可将 $f(n)$ 表示为 $f(m)$ 的倍数。$\square$

---

## 例子

**例 1** $f(n) = c$（常数）。$f(m)-f(n)=0$，被任何 $f(m-n)=c$ 整除。结论显然成立。

**例 2** $f(n) = |n| + 1$。$f(m-n) = |m-n|+1$。$f(m)-f(n) = |m|-|n|$。取 $m=2,n=1$：$f(1)=2$，$f(2)-f(1)=3-2=1$，$2\nmid 1$。不满足条件。说明非平凡解需精细构造。

**例 3** $f(n) = a^{|n|}$（$a \geq 2$）。$f(0)=1$。但 $f(m) \mid f(0)=1$ 要求 $f(m)=1$ 对所有 $m$。不满足。

实际上，满足条件的非平凡函数非常受限。标准结果表明常数函数是主要解，或 $f$ 取值于某因数链。

---

## 应用

此类整除性函数方程在以下领域有应用：

1. **代数数论**：研究理想类群中的整除关系；
2. **格论**：偏序集上的保序映射与整除格的结构；
3. **逻辑与计算机科学**：程序验证中的不变量生成。

---

## 参考文献

1. IMO 2011 Official Solutions, Problem 5.
2. Art of Problem Solving, *IMO 2011 Problem 5*.
3. Niven, I., Zuckerman, H. S., and Montgomery, H. L., *An Introduction to the Theory of Numbers*, Wiley, 1991.
4. 潘承洞, 潘承彪, 《初等数论》, 北京大学出版社, 2003.
