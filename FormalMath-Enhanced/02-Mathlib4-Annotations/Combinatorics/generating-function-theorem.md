---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: 生成函数基本定理 (Generating Function Theorem)
---
# 生成函数基本定理 (Generating Function Theorem)

## Mathlib4 引用

```lean
import Mathlib.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown

namespace GeneratingFunction

/-- 普通生成函数 -/
def ordinaryGeneratingFunction {α : Type*} (a : ℕ → α) [Semiring α] : PowerSeries α :=
  PowerSeries.mk fun n => a n

/-- 指数生成函数 -/
def exponentialGeneratingFunction {α : Type*} (a : ℕ → α) [Semiring α] : PowerSeries α :=
  PowerSeries.mk fun n => a n / n.factorial

/-- 生成函数的乘积对应卷积 -/
theorem ogf_product_convolution (a b : ℕ → ℝ) :
    ordinaryGeneratingFunction (fun n => ∑ k in range (n + 1), a k * b (n - k)) =
    ordinaryGeneratingFunction a * ordinaryGeneratingFunction b := by
  -- Cauchy乘积
  sorry

/-- 生成函数的导数 -/
theorem ogf_derivative (a : ℕ → ℝ) :
    PowerSeries.derivative (ordinaryGeneratingFunction a) =
    ordinaryGeneratingFunction (fun n => (n + 1) * a (n + 1)) := by
  -- 形式导数
  sorry

end GeneratingFunction
```

## 数学背景

生成函数是组合数学中最重要的工具之一，由Abraham de Moivre、James Stirling等18世纪数学家开创，并在20世纪由George Pólya、Richard Stanley等人发展为系统理论。它将离散的数列转化为解析函数，使得组合问题可以借助分析工具解决。

## 直观解释

生成函数告诉我们：**一个数列可以"编码"为一个形式幂级数，数列的运算对应级数的运算**。想象数列是一串数字信息，生成函数将其"拉伸"为一条连续的曲线。通过研究这条曲线的性质（零点、极点、渐近行为），我们可以获取数列的深层信息。

## 形式化表述

**普通生成函数（OGF）**：
$$A(x) = \sum_{n=0}^\infty a_n x^n$$

**指数生成函数（EGF）**：
$$\hat{A}(x) = \sum_{n=0}^\infty a_n \frac{x^n}{n!}$$

**运算对应关系**：

- 数列卷积 ↔ 生成函数乘积
- 数列平移 ↔ 乘以 $x$
- 部分和 ↔ 除以 $(1-x)$
- 二项卷积 ↔ 指数生成函数乘积

## 证明思路

1. **形式幂级数环**：证明形式幂级数构成整环
2. **Cauchy乘积**：证明卷积对应乘积
3. **解析性质**：在收敛半径内使用分析工具
4. **组合解释**：每个运算对应组合构造
5. **渐近分析**：通过奇点分析获得渐近公式

## 示例

### 示例 1：Catalan数

$C_n = \frac{1}{n+1}\binom{2n}{n}$，生成函数满足：

$$C(x) = 1 + xC(x)^2 \implies C(x) = \frac{1 - \sqrt{1-4x}}{2x}$$

### 示例 2：Fibonacci数

$F_0 = 0, F_1 = 1, F_n = F_{n-1} + F_{n-2}$

$$F(x) = \frac{x}{1-x-x^2}$$

### 示例 3：Bell数（集合划分）

$B_n$ 计数 $n$ 元集的集合划分数

$$\hat{B}(x) = e^{e^x - 1}$$

## 应用

- **组合计数**：路径计数、树枚举、排列模式
- **递推关系**：求解线性递推
- **概率论**：矩生成函数、概率生成函数
- **数论**：分拆函数、同余关系
- **算法分析**：平均情形复杂度

## 相关概念

- 形式幂级数：代数基础
- 解析组合学： asymptotic方法
- Cauchy积分公式：系数提取
- Laplace变换：连续版本

## 参考

### 教材

- [Wilf. generatingfunctionology. A K Peters, 3rd edition, 2006]
- [Stanley. Enumerative Combinatorics, Vol 1 & 2. Cambridge, 1997/1999]
- [Flajolet & Sedgewick. Analytic Combinatorics. Cambridge, 2009]

### 在线资源

- [Mathlib4 文档 - Power Series][https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/PowerSeries/Basic.html](需更新)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
