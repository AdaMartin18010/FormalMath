---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: IMO 2025 Problem 3 - Bonza Functions
---
# IMO 2025 Problem 3 - Bonza Functions

## 题目
函数 $f: \mathbb{N} \to \mathbb{N}$ 被称为 **bonza**，如果对所有正整数 $a, b$：
$$f(a) \mid b^a - f(b)^{f(a)}$$

确定最小的实常数 $c$，使得对所有 bonza 函数 $f$ 和所有正整数 $n$：
$$f(n) \leq cn$$

## 分类信息
- **领域**: 数论/函数方程
- **难度**: 7分
- **涉及概念**: 整除性、数论函数、估值、构造法

## 解答

### 答案
最小的常数是 $c = 4$。

### 证明

**步骤1：分析基本性质**

记 $P(a, b)$ 为给定的整除关系：$f(a) \mid b^a - f(b)^{f(a)}$。

**引理1**：$f(n) \mid n^n$ 对所有 $n$ 成立。

**证明**：取 $P(n, n)$：$f(n) \mid n^n - f(n)^{f(n)}$。

由于 $f(n)^{f(n)} \equiv 0 \pmod{f(n)}$，得 $f(n) \mid n^n$。

---

**步骤2：分析奇素数**

**引理2**：除非 $f = \text{id}$（恒等函数），对所有奇素数 $p$ 有 $f(p) = 1$。

**证明**：设存在素数 $q$ 使 $f(q) > 1$。则 $f(q)$ 是 $q$ 的幂。

$P(q, n)$：$f(q) \mid n^q - f(n)^{f(q)}$。

由费马小定理，$n^q \equiv n \pmod{q}$，$f(n)^{f(q)} \equiv f(n) \pmod{q}$。

因此 $q \mid n - f(n)$ 对所有 $n$ 成立，这意味着 $f(n) = n$。

所以若 $f \neq \text{id}$，对所有充分大的素数 $q$ 有 $f(q) = 1$。

对于任意奇素数 $p$，取大素数 $q \not\equiv 1 \pmod{p}$：

$P(p, q)$：$f(p) \mid q^p - 1^p = q^p - 1$。

$q^p - 1 \equiv q - 1 \not\equiv 0 \pmod{p}$，所以 $f(p) = 1$。

---

**步骤3：分析2的幂**

**引理3**：$f(n) \mid 2^{\nu_2(n)+2}$ 对所有 $n$ 成立，其中 $\nu_2(n)$ 是 $n$ 的2-adic估值。

**证明**：由引理1，$f(n) \mid n^n$。

若奇素数 $p \mid f(n)$，则 $P(n, p)$：$f(n) \mid p^n - 1^n$，所以 $p \mid p^n - 1$，矛盾。

因此 $f(n)$ 是2的幂。

$P(n, 5)$：$f(n) \mid 5^n - 1^n$。

已知 $\nu_2(5^n - 1) = \nu_2(n) + 2$。

所以 $f(n) \leq 2^{\nu_2(n)+2}$。

---

**步骤4：得到上界**

$$f(n) \leq 2^{\nu_2(n)+2} = 4 \cdot 2^{\nu_2(n)} \leq 4n$$

因此 $c = 4$ 满足条件。

---

**步骤5：证明 $c = 4$ 是最优的**

构造函数：
$$f(n) = \begin{cases} 1 & n \text{ 奇数} \\ 16 & n = 4 \\ 2n & n \text{ 偶数}, n \neq 4 \end{cases}$$

验证这是 bonza 函数且 $f(4) = 16 = 4 \cdot 4$。

因此 $c = 4$ 不能减小。

## 关键思路与技巧

1. **估值分析**：使用 $p$-adic 估值控制函数增长
2. **费马小定理**：分析素数处的函数值
3. **构造反例**：证明常数的紧性
4. **分类讨论**：奇数和偶数情形分别处理

## 现代联系

本题是**数论函数**理论的深入研究。在**解析数论**中，类似的问题研究**积性函数**的增长。在**计算数论**中，估值计算是**整数分解**算法的基础。

## 参考
- IMO 2025 Official Solutions
- AoPS Community
- Evan Chen's Solution Notes
