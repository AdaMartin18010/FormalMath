---
msc_primary: 00A99
processed_at: '2026-04-03'
title: IMO 2018 Problem 5
---
# IMO 2018 Problem 5

## 题目
设 $a_1, a_2, a_3, \ldots$ 是一个无限正整数序列。证明：存在唯一的整数 $n \geq 1$ 使得：
$$a_n < \frac{a_1 + a_2 + \cdots + a_n}{n} \leq a_{n+1}$$

## 分类信息
- **领域**: 代数/不等式
- **难度**: 6分
- **涉及概念**: 平均数、单调性、唯一性证明

## 解答

定义 $S_n = a_1 + a_2 + \cdots + a_n$，$A_n = \frac{S_n}{n}$。

**存在性**：证明不可能对所有 $n$ 都有 $a_n \geq A_n$，也不可能对所有 $n$ 都有 $a_{n+1} \leq A_n$。

**唯一性**：利用 $A_n$ 的单调变化性质，证明两个不同的解会导致矛盾。

## 参考
- IMO 2018 Official Solutions
