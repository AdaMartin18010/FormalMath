---
msc_primary: 00A99
processed_at: '2026-04-15'
title: IMO 2019 Problem 4
---
# IMO 2019 Problem 4

## 题目
求所有满足
$$k! = (2^n-1)(2^n-2)(2^n-4)\cdots(2^n-2^{n-1})$$
的正整数对 $(k,n)$。

## 分类信息
- **领域**: 数论
- **难度**: 5分
- **涉及概念**: 阶乘、$p$-adic 赋值、Legendre 公式、有限域

## 解答

### 答案
$(k,n) = (1,1)$ 和 $(3,2)$。

### 证明
记右边为 $A_n = \prod_{i=0}^{n-1}(2^n-2^i)$。

**验证小值**：
- $n=1$：$A_1 = 2^1-1 = 1 = 1!$，故 $(k,n)=(1,1)$ 是解。
- $n=2$：$A_2 = (4-1)(4-2) = 3 \cdot 2 = 6 = 3!$，故 $(k,n)=(3,2)$ 是解。

**证明无其他解**：设 $n \ge 3$ 且 $A_n = k!$。

首先计算 $A_n$ 中 2 的幂次：
$$\nu_2(A_n) = \sum_{i=0}^{n-1} \nu_2(2^n-2^i) = \sum_{i=0}^{n-1} i = \frac{n(n-1)}{2}.$$

由 Legendre 公式，$\nu_2(k!) = k - s_2(k) \le k-1$（其中 $s_2(k)$ 为 $k$ 的二进制数字和），故
$$k > \nu_2(k!) = \frac{n(n-1)}{2}.$$

再计算 3 的幂次。对 $t \ge 1$ 有提升指数引理：
$$\nu_3(2^t-1) = \begin{cases} 0 & t \text{ 为奇数} \\ 1+\nu_3(t/2) & t \text{ 为偶数} \end{cases}$$

因此
$$\nu_3(A_n) = \sum_{i=0}^{n-1} \nu_3(2^{n-i}-1) = \left\lfloor\frac{n}{2}\right\rfloor + \left\lfloor\frac{n}{6}\right\rfloor + \left\lfloor\frac{n}{18}\right\rfloor + \cdots < \frac{3n}{4}.$$

而由 Legendre 公式，$\nu_3(k!) \ge \left\lfloor\frac{k}{3}\right\rfloor$。于是
$$\frac{k}{3} \le \nu_3(k!) = \nu_3(A_n) < \frac{3n}{4},$$
即 $k < \frac{9n}{4}$。

结合 $k > \frac{n(n-1)}{2}$，得
$$\frac{n(n-1)}{2} < \frac{9n}{4},$$
即 $n-1 < \frac{9}{2}$，所以 $n \le 5$。

对 $n=3,4,5$ 直接验证：
- $n=3$：$A_3 = 7 \cdot 6 \cdot 4 = 168$，不是阶乘。
- $n=4$：$A_4 = 15 \cdot 14 \cdot 12 \cdot 8 = 20160 = 8! / 2$，不是阶乘。
- $n=5$：$A_5 = 31 \cdot 30 \cdot 28 \cdot 24 \cdot 16 = 9999360$，$10! = 3628800$，$11! = 39916800$，不是阶乘。

故只有 $(1,1)$ 和 $(3,2)$ 两组解。证毕。

## 关键思路与技巧
1. **$p$-adic 估值**：对 2 和 3 分别计算两边的 valuations
2. **Legendre 公式**：建立 $k$ 与 $n$ 的不等式关系
3. **大小估计**：通过估值不等式将 $n$ 限制在小范围内
4. **枚举验证**：对剩余小值直接计算排除

## 参考
- IMO 2019 Official Solutions
- AoPS Community
- Evan Chen's Solution Notes
