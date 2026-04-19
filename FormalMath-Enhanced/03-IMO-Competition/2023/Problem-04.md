---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: 2026-04-15
title: IMO 2023 Problem 4
---
# IMO 2023 Problem 4

## 题目
设 $x_1,x_2,\dots,x_{2023}$ 是两两不同的正实数。对每个 $n=1,2,\dots,2023$，记
$$a_n=\sqrt{(x_1+\dots+x_n)\left(\frac1{x_1}+\dots+\frac1{x_n}\right)}.$$
假设 $a_n$ 对每个 $n$ 都是整数。证明：$a_{2023}\ge3034$。

## 分类信息
- **领域**: 代数/不等式
- **难度**: 5分
- **涉及概念**: Cauchy-Schwarz不等式、整数序列、归纳法、AM-GM

## 解答

### 答案
$a_{2023}\ge3034$。

### 证明
由 Cauchy-Schwarz，$a_{n+1}>\sqrt{(x_1+\dots+x_n)(\frac1{x_1}+\dots+\frac1{x_n})}=a_n$，且 $a_1=1$。因为 $a_n$ 为整数，故 $a_{n+1}\ge a_n+1$。

**归纳-by-二步**：设 $u=\sqrt{\frac{x_{n+1}}{x_{n+2}}}\neq1$（因 $x_i$ 两两不同）。由 Cauchy-Schwarz 的三项形式：
\begin{align*}
a_{n+2}^2&=\left(\sum_{i=1}^n x_i+x_{n+1}+x_{n+2}\right)\left(\sum_{i=1}^n\frac1{x_i}+\frac1{x_{n+1}}+\frac1{x_{n+2}}\right)\\
&\ge\left(\sqrt{\sum_{i=1}^n x_i\sum_{i=1}^n\frac1{x_i}}+\sqrt{\frac{x_{n+1}}{x_{n+2}}}+\sqrt{\frac{x_{n+2}}{x_{n+1}}}\right)^2\\
&=(a_n+u+\tfrac1u)^2.
\end{align*}

因 $u\neq1$，由 AM-GM 有 $u+\frac1u>2$，故 $a_{n+2}>a_n+2$。结合整数性，$a_{n+2}\ge a_n+3$。

由 $a_1=1$，递推得
$$a_{2m+1}\ge a_{2m-1}+3\ge\dots\ge3m+1.$$
取 $m=1011$，得 $a_{2023}\ge3\cdot1011+1=3034$。

## 关键思路与技巧
1. **严格递增性**：Cauchy-Schwarz 和整数性保证 $a_{n+1}\ge a_n+1$
2. **三步跳跃**：通过两项归纳证明每两步至少增加 3
3. **AM-GM**：利用 $u+1/u>2$（严格不等式因 $u\neq1$）得到关键下界
4. **递推求值**：从 $a_1=1$ 递推到 $a_{2023}\ge3034$

## 参考
- IMO 2023 Official Solutions
- AoPS Community
- Evan Chen''s Solution Notes
