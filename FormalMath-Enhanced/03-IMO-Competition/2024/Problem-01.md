---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: 2026-04-15
title: IMO 2024 Problem 1
---
# IMO 2024 Problem 1

## 题目
求所有实数 $\alpha$，使得对每个正整数 $n$，整数
$$\lfloor\alpha\rfloor+\lfloor2\alpha\rfloor+\dots+\lfloor n\alpha\rfloor$$
都是 $n$ 的倍数。

## 分类信息
- **领域**: 数论
- **难度**: 4分
- **涉及概念**: 取整函数、等差数列、模运算、小数部分

## 解答

### 答案
$\alpha$ 必须是偶整数。

### 证明
记 $S(n,\alpha)=\sum_{i=1}^n\lfloor i\alpha\rfloor$。

**整数情形**：若 $\alpha$ 为整数，则
$$S(n,\alpha)=\alpha(1+2+\dots+n)=\alpha\cdot\frac{n(n+1)}2.$$
这是 $n$ 的倍数当且仅当 $\frac{\alpha(n+1)}2$ 为整数对所有 $n$ 成立，即 $\alpha$ 为偶数。

**非整数情形**：设 $\alpha$ 不是整数。注意到
$$S(n,\alpha\pm2)=S(n,\alpha)\pm2\cdot\frac{n(n+1)}2\equiv S(n,\alpha)\pmod n,$$
因此条件在 $\alpha$ 上加减 2 不变。不妨设 $-1<\alpha<1$ 且 $\alpha\neq0$。

- 若 $0<\alpha<1$，设 $m\ge2$ 为使 $m\alpha\ge1$ 的最小整数。则
  $$S(m,\alpha)=0+0+\dots+0+1=1\not\equiv0\pmod m.$$
- 若 $-1<\alpha<0$，设 $m\ge2$ 为使 $m\alpha\le-1$ 的最小整数。则
  $$S(m,\alpha)=(-1)+\dots+(-1)+0=-(m-1)\not\equiv0\pmod m.$$

均矛盾。故 $\alpha$ 必为整数，且为偶数。

## 关键思路与技巧
1. **整数情形直接求和**：利用等差数列公式显式计算
2. **周期性简化**：条件在 $\alpha$ 上加减 2 不变，可将范围缩至 $(-1,1)$
3. **最小反例法**：找到使取整函数首次"跳跃"的 $m$
4. **模运算排除**：在 $0<|\alpha|<1$ 时，$S(m,\alpha)$ 恰好为 $\pm1$ 或 $\pm(m-1)$，不被 $m$ 整除

## 参考
- IMO 2024 Official Solutions
- AoPS Community
- Evan Chen''s Solution Notes
