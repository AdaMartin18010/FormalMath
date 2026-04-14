---
msc_primary: 00A99
processed_at: '2026-04-15'
title: Catalan 数公式 (Catalan Number Formula)
---
# Catalan 数公式 (Catalan Number Formula)

## Mathlib4 引用

```lean
import Mathlib.Combinatorics.Enumerative.Catalan\n\nnamespace Combinatorics\n\n/-- Catalan 数的闭式公式：C_n = (1/(n+1)) * C(2n, n) -/\ntheorem catalan_number_formula (n : ℕ) :\n    catalan n = Nat.choose (2 * n) n / (n + 1) := by\n  -- 利用生成函数或反射原理的双射证明\n  sorry\n\nend Combinatorics
```

## 数学背景

Catalan 数是由比利时数学家欧仁·查理·卡塔兰（Eugène Charles Catalan）在19世纪命名的整数序列，但早在18世纪就被欧拉（Euler）和闵明鸽（Ming Antu）等人研究过。第 $n$ 个 Catalan 数 $C_n$ 计数了多种组合结构：有效括号序列、二叉树、不穿越对角线的格路（Dyck 路径）、凸多边形的三角剖分、栈排列等。Catalan 数的闭式公式为：

$$C_n = \frac{1}{n+1} \binom{2n}{n}$$

Catalan 数是组合数学中最基本、出现频率最高的序列之一，在计算机科学（解析表达式、数据结构）、概率论（随机游走）和统计物理中都有广泛应用。

## 直观解释

Catalan 数是一类神奇的计数数。想象你有 $n$ 对括号，你想知道有多少种方式可以将它们排成合法的序列（每个左括号都有一个对应的右括号，且任何时候右括号的数量不超过左括号）。当 $n = 3$ 时，答案是 5：$((()))$, $(()())$, $(())()$, $()(())$, $()()()$。Catalan 数给出了这个答案的通用公式：$C_n = \frac{1}{n+1} \binom{2n}{n}$。这个公式的美妙之处在于，同一个数还同时计数着二叉树的个数、凸多边形的三角剖分数、以及许多其他看似不相关的组合对象。这就是为什么 Catalan 数常被称为组合数学中的"瑞士军刀"。

## 形式化表述

第 $n$ 个 Catalan 数定义为：

$$C_n = \frac{1}{n+1} \binom{2n}{n} = \frac{(2n)!}{(n+1)! \, n!}$$

等价定义：

1. **递推关系**：$C_0 = 1$，$C_{{n+1}} = \sum_{{i=0}}^n C_i C_{{n-i}}$（$n \geq 0$）
2. **生成函数**：$C(x) = \sum_{{n=0}}^\infty C_n x^n = \frac{1 - \sqrt{1 - 4x}}{2x}$
3. **渐近公式**：$C_n \sim \frac{4^n}{n^{3/2} \sqrt{\pi}}$

前几个 Catalan 数：$C_0 = 1, C_1 = 1, C_2 = 2, C_3 = 5, C_4 = 14, C_5 = 42, C_6 = 132, \dots$

计数对象包括：

- $n$ 对括号组成的合法序列数
- $n+1$ 个叶子的满二叉树个数
- 从 $(0,0)$ 到 $(2n,0)$ 的 Dyck 路径数（每步 $(1,1)$ 或 $(1,-1)$，始终不低于 $x$ 轴）
- 凸 $(n+2)$-边形的三角剖分数
- $n$ 个节点的栈可排序排列数

## 证明思路

1. **生成函数法**：设 $C(x) = \sum C_n x^n$。由递推关系 $C_{{n+1}} = \sum C_i C_{{n-i}}$ 得到 $C(x) = 1 + x C(x)^2$。解这个二次方程得 $C(x) = \frac{1 - \sqrt{1-4x}}{2x}$
2. **广义二项式定理**：$(1 - 4x)^{{-1/2}} = \sum \binom{2n}{n} x^n$。对其积分并与 $C(x)$ 比较系数
3. **反射原理（André 反射）**：计算从 $(0,0)$ 到 $(2n,0)$ 的格路总数 $\binom{2n}{n}$，减去至少一次低于 $x$ 轴的坏路径数。利用反射原理，坏路径数 = $\binom{2n}{n+1} = \binom{2n}{n} \frac{n}{n+1}$
4. **得证**：好路径数 = $\binom{2n}{n} - \binom{2n}{n+1} = \frac{1}{n+1} \binom{2n}{n}$

核心洞察在于"坏路径"可以通过对角线反射与另一组路径建立双射。

## 示例

### 示例 1：括号匹配

$C_3 = 5$ 计数了 3 对括号的所有合法序列：$((()))$, $(()())$, $(())()$, $()(())$, $()()()$。

### 示例 2：二叉树

有 $C_3 = 5$ 棵具有 4 个叶子的满二叉树（或 3 个内部节点的二叉树）。

### 示例 3：多边形的三角剖分

凸六边形（6 条边）有 $C_4 = 14$ 种不同的三角剖分方式。这是因为 $n$ 条边的凸多边形的三角剖分数为 $C_{{n-2}}$。

## 应用

- **计算机科学**：解析树、栈操作和表达式求值
- **概率论**：随机游走的首次返回时间和选票问题
- **统计物理**：自回避行走和聚合物模型
- **生物信息学**：RNA 二级结构的计数
- **图论**：平面树的枚举和图的着色

## 相关概念

- Dyck 路径 (Dyck Path)：不穿越对角线的格路
- 生成函数 (Generating Function)：组合序列的编码工具
- 反射原理 (Reflection Principle)：计数问题中的对称技巧
- 二项式系数 (Binomial Coefficient)：组合数 $\binom{n}{k}$
- 满二叉树 (Full Binary Tree)：每个内部节点恰有两个子节点的树

## 参考

### 教材

- [R. P. Stanley. Enumerative Combinatorics, Vol. 2. Cambridge, 1999. Chapter 6]
- [P. Flajolet, R. Sedgewick. Analytic Combinatorics. Cambridge, 2009. Chapter I]

### 在线资源

- [Mathlib4 - Catalan](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Enumerative/Catalan.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*
