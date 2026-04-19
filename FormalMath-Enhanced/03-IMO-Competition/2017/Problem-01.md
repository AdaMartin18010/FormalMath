---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: IMO 2017 Problem 1
---
# IMO 2017 Problem 1

## 题目
对每个整数 $a_0 > 1$，定义序列 $a_0, a_1, a_2, \ldots$：
$$a_{n+1} = \begin{cases} \sqrt{a_n} & \text{如果 } \sqrt{a_n} \text{ 是整数} \\ a_n + 3 & \text{否则} \end{cases}$$

求所有满足以下条件的 $a_0$：存在数 $A$，使得 $a_n = A$ 对无限多个 $n$ 成立。

## 分类信息
- **领域**: 数论/序列
- **难度**: 4分
- **涉及概念**: 递推序列、周期性、模运算、归纳法

## 解答

### 答案
满足条件的 $a_0$ 是所有满足 $a_0 \equiv 0 \pmod{3}$ 的正整数。

### 证明

**引理**：设 $c$ 是任意序列（周期或非周期）中的最小项，则 $c \equiv 2 \pmod{3}$ 或 $c = 3$。

**证明**：显然 $c \neq 1, 4$（否则序列会进入 $1 \to 1$ 或 $4 \to 2 \to 5 \to \cdots$）。

假设 $c \not\equiv 2 \pmod{3}$。由于 $c$ 不是完全平方数（否则会更小），序列中 $c$ 之后的下一个完全平方数是 $(\lfloor\sqrt{c}\rfloor+1)^2$、$(\lfloor\sqrt{c}\rfloor+2)^2$ 或 $(\lfloor\sqrt{c}\rfloor+3)^2$。

由最小性：$c \leq \lfloor\sqrt{c}\rfloor + 3 \leq \sqrt{c} + 3$，这要求 $c \leq 5$。

由于 $c \neq 1, 2, 4, 5$，故 $c = 3$。

---

**情况1：$a_0 \equiv 0 \pmod{3}$**

所有项都 $\equiv 0 \pmod{3}$。由引理，最小项为 $3$。

序列包含循环：$3 \to 6 \to 9 \to 3$。

因此 $A = 3$ 满足条件。

---

**情况2：$a_0 \not\equiv 0 \pmod{3}$**

**子情况2a：$a_0 \equiv 1 \pmod{3}$**

- 若 $a_n$ 是完全平方数，则 $a_n \equiv 0$ 或 $1 \pmod{3}$
- 若 $a_n \equiv 1 \pmod{3}$，则 $\sqrt{a_n} \equiv 1$ 或 $2 \pmod{3}$

如果 $\sqrt{a_n} \equiv 1 \pmod{3}$，序列继续保持 $\equiv 1 \pmod{3}$。
如果 $\sqrt{a_n} \equiv 2 \pmod{3}$，则后续 $+3$ 保持 $\equiv 2 \pmod{3}$。

无论如何，序列永远不会出现 $3$ 的倍数。

由引理，最小项 $c \equiv 2 \pmod{3}$。

由于 $2$ 不是模 $3$ 的二次剩余，$c$ 之后的所有项都 $> c$，序列严格递增（最终），无界。

**子情况2b：$a_0 \equiv 2 \pmod{3}$**

类似分析，序列永远不会进入 $3$ 的倍数，最终严格递增。

因此不存在满足条件的 $A$。

## 关键思路与技巧

1. **模3分析**：序列的行为完全由模3的余数决定
2. **最小元原理**：任何序列都有最小项，其性质决定序列行为
3. **周期检测**：$3 \to 6 \to 9 \to 3$ 是唯一的有界循环
4. **分类讨论**：按模3余数将问题分为三种情况

## 现代联系

本题与**动力系统**中的迭代理论有关。在**数论**中，这类问题称为"$3x+1$问题"的变体。在**计算理论**中，这种递推关系类似于简单的图灵机。

## 相关概念
- 递推序列
- 模运算
- 动力系统
- 周期性

## 参考
- IMO 2017 Official Solutions
- AoPS Community: https://artofproblemsolving.com/community/c6h1480146p8633190[需更新]
- Evan Chen's Solution Notes
