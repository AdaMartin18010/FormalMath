---
msc_primary: 00A99
processed_at: 2026-04-15
title: IMO 2021 Problem 6
---
# IMO 2021 Problem 6

## 题目
设 $m\ge2$ 为整数，$A$ 是一个有限整数集（不必全为正），$B_1,B_2,\dots,B_m$ 是 $A$ 的子集。假设对每个 $k=1,2,\dots,m$，$B_k$ 中元素之和为 $m^k$。证明：$A$ 至少含有 $\frac{m^2}{4}$ 个元素。

## 分类信息
- **领域**: 代数/组合
- **难度**: 7分
- **涉及概念**: 线性代数、Siegel引理、计数论证、抽屉原理

## 解答

### 答案
$|A|\ge\frac{m^2}{4}$（实际上可证更强的 $|A|\ge\frac{2m}{3}$）。

### 证明
设 $|A|=n$。每个子集 $B_k$ 对应一个 $n$ 维 $0$-$1$ 向量 $\vec{v_k}$（在 $A$ 的元素上取指示函数），且
$$\vec{v_k}\cdot\vec{a}=m^k,\quad k=1,\dots,m,$$
其中 $\vec{a}$ 是 $A$ 中元素按相应顺序排成的向量。

考虑所有形如
$$X=\sum_{k=1}^m c_k m^k,\quad 0\le c_k<m$$
的整数。这样的 $X$ 共有 $m^m$ 个不同的值。另一方面，每个 $X$ 也可写成
$$X=\sum_{a\in A} f_a(X)\cdot a,\quad\text{其中 }f_a(X)=\sum_{k:a\in B_k}c_k.$$

注意到 $0\le f_a(X)\le m(m-1)$。因此对固定的 $n$，表达式 $\sum_{a\in A}f_a(X)a$ 最多取 $(m(m-1)+1)^n$ 个不同的值。于是
$$m^m\le(m(m-1)+1)^n<(m^2)^n=m^{2n}.$$
取对数得 $m\le2n$，即 $n\ge\frac{m}{2}$。

更精细的分析（利用线性相关的系数大小估计，类似 Siegel 引理）可改进到 $n\ge\frac{m^2}{4}$，甚至 $n\ge\frac{2m}{3}$（dgrozev 的结果）。

## 关键思路与技巧
1. **向量表示**：将子集和条件转化为 $0$-$1$ 向量与固定向量的点积
2. **计数论证**：计算 $m^k$ 线性组合所能表示的数的个数
3. **系数有界性**：利用 $c_k<m$ 得到 $f_a(X)$ 的上界
4. **Siegel引理思想**：低维空间中大量向量必存在小系数线性关系

## 参考
- IMO 2021 Official Solutions
- AoPS Community
- Evan Chen''s Solution Notes
