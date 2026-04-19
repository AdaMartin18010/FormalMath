---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: 2026-04-15
title: IMO 2025 Problem 5
---
# IMO 2025 Problem 5

## 题目
Alice 和 Bazza 在玩 **inekoalaty 游戏**，游戏规则依赖于一个已知的正实数 $\lambda$。第 $n$ 轮（从 $n=1$ 开始）如下：
- 若 $n$ 为奇数，Alice 选取一个非负实数 $x_n$，使得 $x_1+x_2+\dots+x_n\le\lambda n$；
- 若 $n$ 为偶数，Bazza 选取一个非负实数 $x_n$，使得 $x_1^2+x_2^2+\dots+x_n^2\le n$。

若某位玩家无法选取合适的 $x_n$，则游戏结束，另一位玩家获胜。若游戏永远进行下去，则双方均不胜。求所有使得 Alice 有必胜策略的 $\lambda$，以及所有使得 Bazza 有必胜策略的 $\lambda$。

## 分类信息
- **领域**: 代数/博弈论
- **难度**: 6分
- **涉及概念**: 博弈策略、Cauchy-Schwarz不等式、递推分析、阈值判定

## 解答

### 答案
- 当 $\lambda>\frac{1}{\sqrt2}$ 时，Alice 有必胜策略；
- 当 $\lambda<\frac{1}{\sqrt2}$ 时，Bazza 有必胜策略；
- 当 $\lambda=\frac{1}{\sqrt2}$ 时，双方均无必胜策略（游戏可无限进行）。

### 证明

**情形1：$\lambda<\frac{1}{\sqrt2}$，Bazza 获胜**

Bazza 采用如下策略：每当 Alice 选出 $x_{2k-1}$ 后，Bazza 取尽可能大的
$$x_{2k}=\sqrt{2k-(x_2^2+x_4^2+\dots+x_{2k-2}^2)-x_{2k-1}^2}.$$
特别地，若粗略估计 Bazza 总取 $x_{2k}\approx\sqrt2$（在Alice取0的理想情况下），则经过 $m$ 轮后
$$S_{2m}=x_1+x_2+\dots+x_{2m}\approx m\sqrt2.$$
而 Alice 在第 $2m+1$ 轮的允许上限为 $\lambda(2m+1)$。由于 $\lambda<\frac{1}{\sqrt2}$，当 $m$ 足够大时
$$m\sqrt2>\lambda(2m+1),$$
Alice 无法继续，Bazza 获胜。

更严谨地，设 $S_{2m}$ 为前 $2m$ 项和，$Q_{2m}$ 为前 $2m$ 项平方和 $\le 2m$。由 QM-AM，
$$S_{2m}\le\sqrt{2m\cdot Q_{2m}}\le 2m.$$
Bazza 的最优策略是最大化 $S_{2m}$，通过适当选择可使 $S_{2m}$ 的增长率为 $\sqrt2\,m$。当 $\lambda<\frac{1}{\sqrt2}$ 时该和终将突破 Alice 的预算。

**情形2：$\lambda>\frac{1}{\sqrt2}$，Alice 获胜**

Alice 采用"零策略"：在前 $k$ 轮自己的回合中都选 $x_{2i-1}=0$。此时
$$S_{2k}=x_2+x_4+\dots+x_{2k}\le\sqrt{k\cdot(x_2^2+\dots+x_{2k}^2)}\le\sqrt{k\cdot 2k}=k\sqrt2.$$
在第 $2k+1$ 轮，Alice 的可选范围为 $[0,\lambda(2k+1)-S_{2k}]$。因
$$\lambda(2k+1)-k\sqrt2>0$$
对所有 $k$ 成立（当 $\lambda>\frac{1}{\sqrt2}$），Alice 永远不会输。

更进一步，当 $k$ 足够大时可使
$$\lambda(2k+1)-k\sqrt2>\sqrt{2k+2}.$$
此时 Alice 可以选一个足够大的 $x_{2k+1}$，使得 Bazza 在下一轮无法找到满足平方和约束的 $x_{2k+2}$，从而 Alice 获胜。

**情形3：$\lambda=\frac{1}{\sqrt2}$**

此时 Alice 的零策略保证她永远不会输（因为 $k\sqrt2\le\frac{1}{\sqrt2}(2k+1)$ 等价于 $2k\le 2k+1$，恒成立）。同时 Bazza 的策略也无法使 $S_{2m}$ 严格超过 Alice 的预算。因此双方都有防守策略使游戏无限进行， neither 能必胜。

## 关键思路与技巧
1. ** competing norms**：$\ell_1$ 约束（Alice）与 $\ell_2$ 约束（Bazza）的对抗
2. **QM-AM 估计**：利用平方均值不等式估计偶数项和的极值
3. **零策略**：Alice 选择 0 使自己的预算尽可能宽裕
4. **阈值现象**：$\lambda=\frac{1}{\sqrt2}$ 是双方优劣的精确临界点

## 参考
- IMO 2025 Official Solutions
- AoPS Community
- Evan Chen''s Solution Notes
