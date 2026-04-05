---
msc_primary: 00A99
processed_at: '2026-04-03'
title: IMO 2018 Problem 6
---
# IMO 2018 Problem 6

## 题目
给定正整数 $n$，设 $a_1, a_2, \ldots, a_n$ 是正整数，满足 $a_1 + a_2 + \cdots + a_n = 2n$。证明：可以选择其中一些数，使得它们的和等于 $n$。

## 分类信息
- **领域**: 组合/数论
- **难度**: 7分
- **涉及概念**: 子集和、鸽巢原理、构造法

## 解答

**证明**：考虑部分和序列 $s_k = a_1 + a_2 + \cdots + a_k$（$k = 0, 1, \ldots, n$）。

若某个 $s_k \equiv 0 \pmod{n}$，则 $s_k = n$（因为 $0 < s_k < 2n$），证毕。

否则，$s_0, s_1, \ldots, s_{n-1}$ 模 $n$ 的余数为 $n$ 个取自 $\{1, 2, \ldots, n-1\}$ 的数。

由鸽巢原理，存在 $i < j$ 使得 $s_j \equiv s_i \pmod{n}$。

则 $a_{i+1} + \cdots + a_j = s_j - s_i \equiv 0 \pmod{n}$。

由于 $0 < s_j - s_i < 2n$，得 $s_j - s_i = n$，证毕。

## 参考
- IMO 2018 Official Solutions
