---
msc_primary: 00A99
processed_at: '2026-04-15'
title: Catalan 数公式 (Catalan Number Formula)
---
# Catalan 数公式 (Catalan Number Formula)

## Mathlib4 引用

```lean
import Mathlib.Combinatorics.Enumerative.Catalan

namespace CatalanNumber

/-- 第 n 个 Catalan 数的显式公式：C_n = (2n choose n) / (n+1) -/
theorem catalan_eq_centralBinom_div (n : ℕ) :
    catalan n = Nat.centralBinom n / (n + 1) := by
  -- 参见 Mathlib4 Combinatorics.Enumerative.Catalan
  sorry

/-- Catalan 数的递归定义 -/
theorem catalan_succ (n : ℕ) :
    catalan (n + 1) = ∑ i : Fin n.succ, catalan i * catalan (n - i) := by
  -- 参见 Mathlib4 catalan_succ
  sorry

end CatalanNumber
```

## 数学背景

Catalan 数是以比利时数学家 Eugène Charles Catalan 命名的整数序列，是组合数学中最频繁出现的数列之一。该序列由递归关系 $C_{n+1} = \sum_{i=0}^{n} C_i C_{n-i}$ 定义，其显式公式 $C_n = \frac{1}{n+1}\binom{2n}{n}$ 揭示了它与中心二项式系数的深刻联系。Catalan 数计数了 Dyck 路径、合法括号序列、二叉树、凸多边形的三角剖分等众多组合结构，堪称“数学界的瑞士军刀”。

## 直观解释

Catalan 数描述的是一类“从不越界”的组合对象。想象一条从 $(0,0)$ 到 $(n,n)$ 的格点路径，只能向右或向上走，且始终不越过对角线 $y = x$。Catalan 数就是这类路径的总数。这就像在悬崖边行走：虽然终点在眼前，但全程不能失足跌落——这种“受约束的自由”正是 Catalan 结构的核心特征。

## 形式化表述

Catalan 数 $C_n$（$n = 0, 1, 2, \ldots$）有两种等价定义：

**递归定义**：

$$C_0 = 1, \quad C_{n+1} = \sum_{i=0}^{n} C_i C_{n-i}$$

**显式公式（闭形式）**：

$$C_n = \frac{1}{n+1} \binom{2n}{n} = \frac{(2n)!}{(n+1)!\, n!}$$

在 Mathlib4 中，`catalan n` 由递归定义给出，定理 `catalan_eq_centralBinom_div` 证明了其显式公式。

## 证明思路

1. **生成函数法**：设 $C(x) = \sum_{n=0}^{\infty} C_n x^n$，由递归关系得 $C(x) = 1 + x C(x)^2$
2. **解二次方程**：$C(x) = \frac{1 - \sqrt{1-4x}}{2x}$（取在 $x=0$ 处正则的分支）
3. **二项式展开**：对 $\sqrt{1-4x} = (1-4x)^{1/2}$ 使用广义二项式定理
4. **提取系数**：比较 $x^n$ 的系数，利用中心二项式系数的恒等式得到 $C_n = \frac{1}{n+1}\binom{2n}{n}$

核心在于生成函数将复杂的卷积递归转化为可解的代数方程。

## 示例

### 示例 1：前几个 Catalan 数

| $n$ | $C_n$ | 计算 |
|-----|-------|------|
| 0 | 1 | 定义 |
| 1 | 1 | $\frac{1}{2}\binom{2}{1} = 1$ |
| 2 | 2 | $\frac{1}{3}\binom{4}{2} = 2$ |
| 3 | 5 | $\frac{1}{4}\binom{6}{3} = 5$ |
| 4 | 14 | $\frac{1}{5}\binom{8}{4} = 14$ |
| 5 | 42 | $\frac{1}{6}\binom{10}{5} = 42$ |

### 示例 2：合法括号序列

$n = 3$ 时，$C_3 = 5$ 个合法的三对括号序列为：

```
((()))  (()())  (())()  ()(())  ()()()
```

### 示例 3：二叉树计数

$C_n$ 也等于具有 $n$ 个内部节点（或 $n+1$ 个叶节点）的不同满二叉树的个数。$n=3$ 时共有 5 棵这样的二叉树。

## 应用

- **计算机科学**：栈排列、二叉搜索树、表达式解析与语法分析
- **组合几何**：凸多边形的三角剖分、非交叉划分
- **概率论**：随机游走返回原点且始终非负的路径计数
- **统计物理**： voter 模型与某些格点模型的配分函数
- **代数拓扑**：associahedron（Stasheff 多面体）的面数

## 相关概念

- Dyck 路径 (Dyck Path)：不越过对角线的格点路径
- 中心二项式系数 (Central Binomial Coefficient)：$\binom{2n}{n}$
- 生成函数 (Generating Function)：组合序列的解析工具
- Associahedron：组合学与代数拓扑中的重要多面体
- Ballot 问题：Catalan 数的经典概率解释

## 参考

### 教材

- [Stanley. Enumerative Combinatorics, Vol. 2. Cambridge, 1999. Exercise 6.19]
- [Sedgewick & Flajolet. An Introduction to the Analysis of Algorithms. Addison-Wesley, 1996. Chapter 5]

### 历史文献

- [Catalan. Note sur une équation aux différences finies. Journal de Mathématiques Pures et Appliquées, 1838]

### 在线资源

- [Mathlib4 文档 - Catalan][https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Enumerative/Catalan.html]
- [OEIS A000108 - Catalan Numbers][https://oeis.org/A000108]

---

*最后更新：2026-04-15 | 版本：v1.0.0*
