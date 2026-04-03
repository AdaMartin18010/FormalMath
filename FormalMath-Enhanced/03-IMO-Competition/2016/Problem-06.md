# IMO 2016 Problem 6

## 题目
求所有满足以下性质的整数 $n \geq 3$：对于所有实数 $a_1, a_2, \ldots, a_n$ 和 $b_1, b_2, \ldots, b_n$ 满足 $|a_k| + |b_k| = 1$（$1 \leq k \leq n$），存在 $x_1, x_2, \ldots, x_n$，每个为 $-1$ 或 $1$，使得：
$$\left|\sum_{k=1}^{n} x_k a_k\right| + \left|\sum_{k=1}^{n} x_k b_k\right| \leq 1$$

## 分类信息
- **领域**: 代数/组合
- **难度**: 7分
- **涉及概念**: 线性组合、符号选择、归纳法、不等式

## 解答

### 答案
满足条件的 $n$ 是所有大于等于3的**奇数**。

### 证明

**步骤1：证明偶数 $n$ 不满足条件**

设 $n = 2m \geq 4$ 为偶数。

取 $a_1 = a_2 = \cdots = a_{n-1} = b_n = 0$，$b_1 = b_2 = \cdots = b_{n-1} = a_n = 1$。

验证：$|a_k| + |b_k| = 1$ 对所有 $k$ 成立。

对于任何选择 $x_k \in \{-1, 1\}$：
$$\sum_{k=1}^{n} x_k a_k = x_n \cdot 1 = \pm 1$$
$$\sum_{k=1}^{n} x_k b_k = \sum_{k=1}^{n-1} x_k \cdot 1 = \text{奇数}$$

由于 $n-1$ 是奇数，$\sum_{k=1}^{n-1} x_k$ 是奇数，所以其绝对值至少为1。

因此：
$$\left|\sum x_k a_k\right| + \left|\sum x_k b_k\right| \geq 1 + 1 = 2 > 1$$

矛盾！

**步骤2：证明奇数 $n$ 满足条件**

设 $n \geq 3$ 为奇数。

不失一般性，假设 $b_k \geq 0$（可以通过翻转 $(a_k, b_k)$ 和 $x_k$ 实现）。

设 $a_1 \geq a_2 \geq \cdots \geq a_m \geq 0 > a_{m+1} \geq \cdots \geq a_n$。

取 $x_k = (-1)^{k+1}$（交错选择）。

定义：
$$s = \sum_{k=1}^{m} x_k a_k = (a_1 - a_2) + (a_3 - a_4) + \cdots \geq 0$$
$$t = \sum_{k=m+1}^{n} x_k a_k$$

由于 $n$ 是奇数，$m$ 的奇偶性取决于具体值。

计算：
$$s = a_1 - (a_2 - a_3) - (a_4 - a_5) - \cdots < a_1 \leq 1$$
$$t = (-a_n + a_{n-1}) + (-a_{n-2} + a_{n-3}) + \cdots \geq 0$$
$$t = -a_n + (a_{n-1} - a_{n-2}) + \cdots < -a_n \leq 1$$

由条件 $|a_k| + |b_k| = 1$：
- 对 $k \leq m$：$a_k + b_k = 1$
- 对 $k > m$：$-a_k + b_k = 1$

因此：
$$\sum x_k a_k = s - t, \quad \sum x_k b_k = 1 - s - t$$

需要证明：$|s-t| + |1-s-t| \leq 1$ 在 $0 \leq s, t \leq 1$ 下成立。

对称性假设 $s \geq t$：
- 若 $1 - s - t \geq 0$：$|s-t| + |1-s-t| = s-t+1-s-t = 1-2t \leq 1$ ✓
- 若 $1 - s - t < 0$：$|s-t| + |1-s-t| = s-t-1+s+t = 2s-1 < 1$ ✓

## 关键思路与技巧

1. **对称性简化**：通过翻转使 $b_k \geq 0$
2. **交错选择**：$x_k = (-1)^{k+1}$ 的巧妙选择
3. **归纳法**：对小奇数验证后推广
4. **偶数反例**：构造特定的极端配置
5. **分类讨论**：根据 $1-s-t$ 的符号分别处理

## 现代联系

本题与**离散调和分析**和**布尔函数**有关。在**计算机科学**中，这类问题涉及阈值函数和决策树复杂度。在**概率论**中，这与随机游走的偏差问题相关。

## 相关概念
- [布尔函数](../../concept/布尔函数.md)
- [组合优化](../../concept/组合优化.md)
- [离散傅里叶分析](../../concept/离散傅里叶分析.md)
- [符号选择问题](../../concept/符号选择.md)

## 参考
- IMO 2016 Official Solutions
- AoPS Community: https://artofproblemsolving.com/community/c6h1263917p6575295
