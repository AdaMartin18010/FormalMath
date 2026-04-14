---
msc_primary: 00A99
processed_at: 2026-04-15
title: IMO 2022 Problem 5
---
# IMO 2022 Problem 5

## 题目
求所有满足 $a^p=b!+p$ 的正整数三元组 $(a,b,p)$，其中 $p$ 为素数。

## 分类信息
- **领域**: 数论
- **难度**: 6分
- **涉及概念**: 阶乘、$p$-adic估值、Zsigmondy定理、Wilson定理

## 解答

### 答案
仅有 $(a,b,p)=(2,2,2)$ 和 $(3,4,3)$。

### 证明
这两个解可直接验证。下设 $a\ge2$，$p$ 为奇素数（$p=2$ 单独验证得唯一解 $(2,2,2)$）。

**引理1**：$b\le2p-2$，从而 $a<p^2$。
*证明*：若 $b\ge2p$，则 $b!+p\equiv p\pmod{p^2}$，故 $\nu_p(b!+p)=1$，但 $\nu_p(a^p)=p\cdot\nu_p(a)\ge p\ge2$，矛盾。
若 $b=2p-1$，由 Wilson 定理可得矛盾（$p>2$ 时内括号 $\equiv2\pmod p$）。于是 $b\le2p-2$，进而 $a^p\le(2p-2)!+p<p^{2p}$，即 $a<p^2$。*

**引理2**：$a\ge p$，从而 $b\ge p$。
*证明*：若 $a<p$，则 $b!+p=a^p>a!+p$，故 $b>a$。取模 $a$ 得 $0\equiv p\pmod a$，矛盾。*

**引理3**：$a=p$。
*证明*：由引理1、2知 $p\mid b!+p=a^p$，故 $p\mid a$。设 $a=pk$（$k<p$）。则 $k\mid b!$ 但 $k\nmid a^p-p=p(p^{p-1}k^p-1)$ 除非 $k=1$。故 $a=p$。*

**最终验证**：$a=p$ 时方程变为 $p^p-p=b!$。对 $p\ge5$，$p^p-p=p(p^{p-1}-1)$。由 Zsigmondy 定理，$p^{p-1}-1$ 有素因子 $q\equiv1\pmod{p-1}$ 且 $q\neq p$。但 $q\le b\le2p-2$，而满足 $q\equiv1\pmod{p-1}$ 且 $q\le2p-2$ 的素数只有 $q=p$（当 $p-1\mid p-1$）或 $q=2p-1$（若其为素数），均矛盾。故 $p\le3$。

- $p=2$：$2^2-2=2=2!$，$(a,b)=(2,2)$。
- $p=3$：$3^3-3=24=4!$，$(a,b)=(3,4)$。

## 关键思路与技巧
1. **$p$-adic估值与大小估计**：用阶乘的 $p$-adic估值限制 $b$ 的范围
2. **模运算排除**：通过模 $a$ 得到 $a\ge p$
3. **Zsigmondy定理**：对 $p\ge5$ 导出矛盾，将问题归结到小素数
4. **小值枚举**：手动验证 $p=2,3$ 的情况

## 参考
- IMO 2022 Official Solutions
- AoPS Community
- Evan Chen''s Solution Notes
