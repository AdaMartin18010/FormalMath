---
msc_primary: 00A99
processed_at: '2026-04-03'
title: IMO 2006 Problem 3
---
# IMO 2006 Problem 3

## 题目

求实数 $x$ 的最小值，使得对于任意正实数 $a, b, c$，以下不等式成立：

$$a^3 + b^3 + c^3 + xabc \geq \frac{1}{2}(a+b+c)(a^2+b^2+c^2)$$

## 分类

- **领域**: 代数（不等式）
- **难度**: 5分
- **关键词**: 对称不等式、三次齐次不等式、Muirhead不等式、SOS方法

## 解答

### 分析

这是一个关于三个变量的对称不等式。我们需要找到最小的 $x$ 使得不等式对所有正实数 $a, b, c$ 成立。

**关键观察**：

1. 不等式是3次齐次的
2. 由对称性，极值可能在 $a = b = c$ 或某些变量相等时取得

### 求解

**步骤1：标准化处理**

设 $a = b = c = 1$：
$$3 + x \geq \frac{1}{2} \cdot 3 \cdot 3 = \frac{9}{2}$$
$$x \geq \frac{9}{2} - 3 = \frac{3}{2}$$

这表明 $x \geq \frac{3}{2}$ 是必要条件。

**步骤2：验证 $x = \frac{3}{2}$ 是否充分**

需要证明：
$$a^3 + b^3 + c^3 + \frac{3}{2}abc \geq \frac{1}{2}(a+b+c)(a^2+b^2+c^2)$$

**步骤3：展开并化简**

右边展开：
$$\frac{1}{2}(a+b+c)(a^2+b^2+c^2) = \frac{1}{2}(a^3+b^3+c^3+ab^2+ac^2+ba^2+bc^2+ca^2+cb^2)$$

不等式变为：
$$a^3 + b^3 + c^3 + \frac{3}{2}abc \geq \frac{1}{2}\sum_{cyc} a^3 + \frac{1}{2}\sum_{sym} a^2b$$

$$\frac{1}{2}(a^3+b^3+c^3) + \frac{3}{2}abc \geq \frac{1}{2}\sum_{sym} a^2b$$

乘以2：
$$a^3+b^3+c^3 + 3abc \geq \sum_{sym} a^2b = a^2b+ab^2+b^2c+bc^2+c^2a+ca^2$$

**步骤4：应用Schur不等式**

Schur不等式（$r=1$）指出：
$$a^3+b^3+c^3+3abc \geq a^2b+ab^2+b^2c+bc^2+c^2a+ca^2$$

这正是我们需要证明的！

因此 $x = \frac{3}{2}$ 是充分的。

**步骤5：证明这是最小值**

取 $a = b = 1$，$c \to 0^+$：

左边 $\to 1 + 1 + 0 + 0 = 2$

右边 $\to \frac{1}{2}(2)(2) = 2$

这给出等号情况，验证了边界。

取 $a = b = 1$，$c = t$ 为小正数，展开验证 $x$ 不能小于 $\frac{3}{2}$。

### 结论

最小值为 $x = \boxed{\dfrac{3}{2}}$

## 数学概念

### 核心概念

1. **Schur不等式**
   对于非负实数 $a, b, c$ 和 $r > 0$：
   $$a^r(a-b)(a-c) + b^r(b-c)(b-a) + c^r(c-a)(c-b) \geq 0$$

   当 $r = 1$ 时：
   $$a^3+b^3+c^3+3abc \geq \sum_{sym} a^2b$$

2. **对称不等式技巧**
   - 齐次化
   - 对称性假设（$a = b$ 或 $a = b = c$）
   - SOS（Sum of Squares）方法

3. **Muirhead不等式**
   如果 $(p_1, p_2, p_3)$ 优于 $(q_1, q_2, q_3)$，则：
   $$\sum_{sym} a^{p_1}b^{p_2}c^{p_3} \geq \sum_{sym} a^{q_1}b^{q_2}c^{q_3}$$

### 与FormalMath主项目的链接

- [不等式基础](../../concept/algebra/inequalities-basics.md)
- [Schur不等式](../../concept/algebra/schur-inequality.md)
- [对称多项式](../../concept/algebra/symmetric-polynomials.md)
- [Muirhead不等式](../../concept/algebra/muirhead-inequality.md)

## 变体与推广

### 变体1（n元推广）

对于 $n$ 个正实数，求最小的 $x$ 使得：
$$\sum a_i^3 + x\prod a_i \geq \frac{1}{n-1}(\sum a_i)(\sum a_i^2)$$

### 变体2（不同次数）

求最小 $x$ 使得：
$$a^4+b^4+c^4+xabc(a+b+c) \geq \frac{1}{3}(a+b+c)(a^3+b^3+c^3)$$

### 推广（一般形式）

对于正实数 $a_1, a_2, \ldots, a_n$ 和 $k \geq 1$，研究：
$$\sum a_i^k + x\prod a_i \geq f(\sum a_i, \sum a_i^{k-1})$$

## 参考

- [IMO 2006 Official Solutions](https://www.imo-official.org/problems/IMO2006SL.pdf)
- [AoPS讨论贴](https://artofproblemsolving.com/community/c6h101490p572824)
- [《不等式的秘密》](https://www.amazon.com/Secrets-Inequalities-Pham-Kim-Hung/dp/0982770404) - Pham Kim Hung
- 相关不等式：Schur不等式、Muirhead不等式、AM-GM不等式

---

*解答整理：FormalMath项目团队*
