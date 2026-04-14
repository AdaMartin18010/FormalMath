---
msc_primary: 00A99
processed_at: 2026-04-15
title: IMO 2024 Problem 2
---
# IMO 2024 Problem 2

## 题目
求所有正整数对 $(a,b)$，使得序列
$$x_n=\gcd(a^n+b,\,b^n+a)\quad(n=1,2,3,\dots)$$
最终为常数列。

## 分类信息
- **领域**: 数论
- **难度**: 5分
- **涉及概念**: 最大公约数、Euler定理、模运算、周期性

## 解答

### 答案
仅有 $(a,b)=(1,1)$。

### 证明
$(1,1)$ 时 $x_n=\gcd(2,2)=2$，显然是常数列。

下设 $(a,b)\neq(1,1)$ 且序列最终为常数。记 $M=ab+1$。

**关键观察**：$\gcd(a,M)=\gcd(b,M)=1$（因为任何同时整除 $a$ 和 $ab+1$ 的数必整除 1）。

取 $n$ 为充分大的 $\varphi(M)$ 的倍数，使得 $x_{n-1}=x_n=x_{n+1}=\dots$。

- **分析 $x_{n-1}$**：
  $$a(a^{n-1}+b)=a^n+ab\equiv1+(-1)\equiv0\pmod M$$
  （因为 $a^n\equiv1\pmod M$）。同理 $b(b^{n-1}+a)\equiv0\pmod M$。故 $M\mid x_{n-1}$。

- **分析 $x_n$**：由于 $x_n=x_{n-1}$，有 $M\mid x_n$。于是
  $$a^n+b\equiv0\pmod M\implies 1+b\equiv0\pmod M,$$
  $$b^n+a\equiv0\pmod M\implies 1+a\equiv0\pmod M.$$
  故 $a\equiv b\equiv-1\pmod M$。

- **分析 $x_{n+1}$**：$M\mid x_{n+1}$，于是
  $$a^{n+1}+b\equiv a+b\equiv0\pmod M.$$
  结合 $a\equiv-1\pmod M$，得 $-1+(-1)\equiv0\pmod M$，即 $M\mid2$。

因此 $ab+1=M\le2$，结合 $a,b\ge1$ 得 $ab=1$，即 $a=b=1$。

## 关键思路与技巧
1. **核心数 $M=ab+1$**：仿照 IMO 2005/4 的技巧，构造具有大公约性质的数
2. **Euler定理**：取 $n$ 为 $\varphi(M)$ 的倍数，使 $a^n\equiv b^n\equiv1\pmod M$
3. **三项连锁**：通过 $x_{n-1},x_n,x_{n+1}$ 逐步导出 $a,b$ 模 $M$ 的值
4. **范围限制**：$M\mid2$ 结合 $M=ab+1$ 直接锁定唯一解

## 参考
- IMO 2024 Official Solutions
- AoPS Community
- Evan Chen''s Solution Notes
