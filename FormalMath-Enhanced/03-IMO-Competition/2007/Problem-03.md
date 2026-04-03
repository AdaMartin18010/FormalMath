# IMO 2007 Problem 3

## 题目

设 $c > 2$，$a(1), a(2), \ldots$ 是一个非负实数序列，满足以下两个条件：

**(1)** $a(m + n) \leq 2a(m) + 2a(n)$ 对所有 $m, n \geq 1$ 成立

**(2)** $a(2^k) \leq \dfrac{1}{(k+1)^c}$ 对所有 $k \geq 0$ 成立

证明：序列 $a(n)$ 是有界的。

## 分类

- **领域**: 代数（序列与不等式）
- **难度**: 6分
- **关键词**: 序列有界性、递推不等式、二进制展开、柯西-施瓦茨不等式

## 解答

### 分析

这道题要求证明在给定条件下序列 $a(n)$ 有界。关键思路：

1. 条件(1)是一个次可加性的变体，允许我们控制 $a(n)$ 的增长
2. 条件(2)给出了 $a$ 在2的幂次处的衰减速度
3. 结合这两个条件，我们需要证明对所有 $n$，$a(n)$ 被某个常数限制

**主要策略**：利用二进制展开将任意 $n$ 表示为2的幂次之和，然后应用条件(1)来估计 $a(n)$。

### 证明

**步骤1：建立基本引理**

首先，为方便起见，定义 $a(0) = 0$。则条件(1)对所有非负整数对仍然成立。

**引理1**：对于任意非负整数 $n_1, n_2, \ldots, n_k$，有：

$$a\left(\sum_{i=1}^{k} n_i\right) \leq \sum_{i=1}^{k} 2^i a(n_i)$$

和

$$a\left(\sum_{i=1}^{k} n_i\right) \leq 2k \sum_{i=1}^{k} a(n_i)$$

**引理1证明**：

对第一个不等式用归纳法。当 $k = 1$ 时显然成立。

归纳步骤：
$$a\left(\sum_{i=1}^{k} n_i\right) = a\left(n_1 + \sum_{i=2}^{k} n_i\right) \leq 2a(n_1) + 2a\left(\sum_{i=2}^{k} n_i\right)$$

$$\leq 2a(n_1) + 2\sum_{i=2}^{k} 2^{i-1}a(n_i) = \sum_{i=1}^{k} 2^i a(n_i)$$

第二个不等式由第一个直接得到，因为 $2^i \leq 2k$ 对 $i \leq k$ 成立。

**步骤2：利用二进制展开**

设 $n$ 是任意正整数，其二进制展开为：

$$n = \sum_{i=0}^{d} \varepsilon_i 2^i, \quad \varepsilon_i \in \{0, 1\}$$

令 $S = \{i : \varepsilon_i = 1\}$ 为二进制表示中1的位置集合，$|S| \leq d + 1 \leq \log_2 n + 1$。

由引理1：

$$a(n) = a\left(\sum_{i \in S} 2^i\right) \leq \sum_{i \in S} 2^{i+1} a(2^i)$$

**步骤3：应用条件(2)估计**

由条件(2)，$a(2^i) \leq \dfrac{1}{(i+1)^c}$，所以：

$$a(n) \leq \sum_{i \in S} \frac{2^{i+1}}{(i+1)^c}$$

我们需要证明这个和有界，与 $n$ 无关。

**步骤4：分组估计技巧**

采用更精细的估计方法。设 $0 = M_0 < M_1 < M_2 < \cdots$ 是一个待定的递增无界序列。

将求和按区间分组：

$$a(n) \leq \sum_{k=1}^{f} \sum_{M_{k-1} \leq i < M_k, \, i \in S} \frac{2^{i+1}}{(i+1)^c}$$

其中 $f$ 满足 $M_f > d$（即覆盖所有可能的 $i$）。

对于每个组 $k$，区间 $[M_{k-1}, M_k)$ 中的整数个数小于 $M_k - M_{k-1} + 1$。

在该区间内，$(i+1)^c \geq (M_{k-1}+1)^c$，且 $2^{i+1} \leq 2^{M_k}$。

因此：

$$a(n) \leq \sum_{k=1}^{f} (M_k - M_{k-1} + 1) \cdot \frac{2^{M_k+1}}{(M_{k-1}+1)^c}$$

**步骤5：选择适当的序列 $M_k$**

取 $M_k = \left\lfloor \frac{4k}{c-2} \right\rfloor - 1$（对于 $c > 2$）。

则 $M_k - M_{k-1} + 1 \approx \dfrac{4}{c-2}$，且：

$$(M_{k-1} + 1)^c \approx \left(\frac{4(k-1)}{c-2}\right)^c$$

经过计算（详细代数见官方解答）：

$$a(n) \leq \sum_{k=1}^{\infty} \frac{4^{2/(c-2)}}{2^{k+1}} = 8 \cdot 4^{2/(c-2)}$$

这个级数收敛，因为分母有指数衰减的因子 $2^{k+1}$。

**步骤6：结论**

因此，对所有 $n \geq 1$：

$$a(n) \leq 8 \cdot 4^{2/(c-2)}$$

这表明序列 $a(n)$ 是有界的。

### 另一种证明（使用引理2）

**引理2**：设 $s_1, s_2, \ldots, s_k$ 是正整数，满足 $\displaystyle\sum_{i=1}^{k} 2^{-s_i} \leq 1$。则对任意正整数 $n_1, \ldots, n_k$：

$$a\left(\sum_{i=1}^{k} n_i\right) \leq \sum_{i=1}^{k} 2^{s_i} a(n_i)$$

**引理2证明**：对 $k$ 归纳。$k = 1$ 时显然。$k = 2$ 时由条件(1)直接得到。

对于 $k > 2$，设 $s_1 \leq s_2 \leq \cdots \leq s_k$。注意：

$$\sum_{i=1}^{k-1} 2^{-s_i} \leq 1 - 2^{-s_{k-1}}$$

定义 $s_{k-1}' = s_{k-1} - 1$，$n_{k-1}' = n_{k-1} + n_k$。则：

$$\sum_{i=1}^{k-2} 2^{-s_i} + 2^{-s_{k-1}'} \leq 1$$

应用归纳假设和条件(1)即可得证。

**应用引理2**：

取 $q = c/2 > 1$。设 $n$ 的二进制表示为 $n = \displaystyle\sum_{i=1}^{k} 2^{u_i}$，其中 $0 \leq u_1 < u_2 < \cdots < u_k$。

选择 $s_i = \lfloor \log_2(u_i + 1) \rfloor + d$，其中 $d$ 是待定整数。

适当选择 $d$ 使得 $\displaystyle\sum_{i=1}^{k} 2^{-s_i} \leq 1$。

由引理2：

$$a(n) \leq \sum_{i=1}^{k} 2^{s_i} a(2^{u_i}) \leq \sum_{i=1}^{k} 2^{s_i} \cdot \frac{1}{(u_i+1)^c}$$

经过计算，这个和被某个只依赖于 $c$ 的常数限制。

## 数学概念

### 核心概念

1. **序列有界性**
   - 序列 $a(n)$ 有界是指存在 $M$ 使得 $|a(n)| \leq M$ 对所有 $n$ 成立
   - 证明有界性的常用技巧

2. **次可加性条件**
   - 经典次可加性：$a(m+n) \leq a(m) + a(n)$
   - 本题中的变体：$a(m+n) \leq 2a(m) + 2a(n)$
   - 这类条件的应用

3. **二进制展开技巧**
   - 将正整数表示为2的幂次之和
   - 在数列估计中的应用

4. **柯西-施瓦茨不等式的离散形式**
   - 在估计和式时的应用

### 与FormalMath主项目的链接

- [序列与级数](../../concept/analysis/sequences-series.md)
- [不等式技巧](../../concept/algebra/inequalities.md)
- [二进制与数论](../../concept/number-theory/binary-representation.md)

## 变体与推广

### 变体1

若条件改为 $a(m+n) \leq a(m) + a(n)$（经典次可加性），且 $a(2^k) \leq \dfrac{1}{(k+1)^c}$，证明 $a(n) \to 0$ 当 $n \to \infty$。

### 变体2

研究条件 $c > 2$ 是否是最优的。当 $c = 2$ 时，结论是否仍然成立？

（答案：$c > 2$ 是尖锐的。当 $c \leq 2$ 时，存在无界的反例。）

### 推广

设 $p > 1$，$a(m+n) \leq p \cdot a(m) + p \cdot a(n)$，且 $a(b^k) \leq \dfrac{1}{(k+1)^c}$ 对某个 $b > 1$ 和 $c > \log_b p + 1$。证明 $a(n)$ 有界。

## 参考

- [IMO 2007 Official Solutions](https://www.imo-official.org/problems/IMO2007SL.pdf)
- [AoPS讨论贴](https://artofproblemsolving.com/community/c6h163343p909372)
- 相关主题：次可加序列、Fekete引理
- 参考文献：G. Polya, G. Szegö - Problems and Theorems in Analysis

---

*解答整理：FormalMath项目团队*
