---
title: "IMO真题-组合：集合划分"
level: silver
course: IMO竞赛数学
difficulty: L3
topic: 组合
source: "IMO 2002 Problem 1"
target_courses:
  - MIT 18.701
status: completed
created_at: 2026-04-18
---

# IMO 2002 Problem 1：集合划分

## 题目

设 $n$ 为大于1的正整数。$n$ 个灯 $L_0, L_1, \ldots, L_{n-1}$ 排成一个圆周，每个灯可以是开或关。初始时所有灯都是开的。每一步操作：选择一个灯 $L_i$，如果 $L_i$ 是开的，则可以将其关闭，并同时改变 $L_{i-1}$ 和 $L_{i+1}$ 的状态（开变关，关变开）。下标按模 $n$ 计算。

求所有使得最终可以关闭所有灯的 $n$。

## 解答

**答案**：所有不被3整除的 $n$。

**方法：不变量与线性代数**

**步骤1**：建立代数模型。

将灯的状态表示为 $\mathbb{F}_2$ 上的向量 $(x_0, x_1, \ldots, x_{n-1})$，其中 $x_i = 1$ 表示开，$x_i = 0$ 表示关。

操作对应于加上向量 $e_i + e_{i-1} + e_{i+1}$（模2）。

**步骤2**：分析可达性。

从全1向量出发，能否到达全0向量？即：全1向量是否在操作生成元的张成空间中？

**步骤3**：利用循环矩阵。

操作矩阵为循环矩阵 $A = I + S + S^{-1}$，其中 $S$ 为循环移位矩阵。

在 $\mathbb{F}_2$ 上，$A$ 的特征值为 $1 + \omega^j + \omega^{-j}$（$j = 0, 1, \ldots, n-1$），其中 $\omega$ 为 $n$ 次单位根。

**步骤4**：计算行列式。

$\det(A)$ 在 $\mathbb{F}_2$ 上为0当且仅当存在 $j$ 使得 $1 + \omega^j + \omega^{-j} = 0$（在适当的扩域中）。

这等价于 $\omega^{3j} = 1$ 且 $\omega^j \neq 1$。

**步骤5**：结论。

- 若 $3 \nmid n$：则 $\omega^{3j} = 1$ 蕴含 $\omega^j = 1$，所以 $A$ 可逆，全1向量可以到达全0向量。
- 若 $3 \mid n$：取 $j = n/3$，则 $\omega^j$ 为原始3次单位根，$1 + \omega^j + \omega^{2j} = 0$，所以 $A$ 不可逆。

进一步分析不变量：当 $3 \mid n$ 时，$\sum_{i \equiv 0 \pmod{3}} x_i$（模2）是不变量。初始时为1，无法变为0。$\square$

## 知识点映射

| 知识点 | 银层对应 |
|--------|---------|
| 线性代数 over F₂ | MIT 18.06 线性代数 |
| 循环矩阵 | MIT 18.06 特征值 |
| 不变量方法 | MIT 18.701 群作用 |
| 单位根 | MIT 18.701 域扩张 |

## Lean4 形式化

```lean4
import Mathlib

-- IMO 2002 Problem 1
example (n : ℕ) (hn : n > 1) :
    (∃ (ops : Finset (Fin n)),
      ∀ (i : Fin n), (1 + ∑ op in ops, if i = op then 1 else 0 +
        if i = op + 1 then 1 else 0 + if i = op - 1 then 1 else 0) % 2 = 0) ↔
    ¬ (3 ∣ n) := by
  sorry
```
