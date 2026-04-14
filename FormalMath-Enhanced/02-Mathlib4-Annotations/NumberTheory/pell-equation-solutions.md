---
msc_primary: 00A99
processed_at: '2026-04-15'
title: Pell 方程解 (Pell Equation Solutions)
---
# Pell 方程解 (Pell Equation Solutions)

## Mathlib4 引用

```lean
import Mathlib.NumberTheory.Pell

namespace NumberTheory

variable {d : ℕ} (hd : d > 0) (hnsq : ¬ IsSquare d)

/-- Pell 方程 x² - d y² = 1 总有无穷多组正整数解 -/
theorem pell_infinite_solutions :
    Infinite {(x, y) : ℕ × ℕ | x^2 - d * y^2 = 1} := by
  -- 利用连分数展开找到最小解，再由递推生成无穷解
  sorry

end NumberTheory
```

## 数学背景

Pell 方程是数论中最著名的 Diophantine 方程之一，形如 $x^2 - dy^2 = 1$（其中 $d$ 是非平方正整数）。该方程在古希腊和古印度数学中已有研究，但由英国数学家约翰·佩尔（John Pell）的名字命名则是一个历史误会（实际应归功于费马和布龙克尔）。拉格朗日于1768年首次证明了 Pell 方程总有无穷多组整数解，并给出了利用连分数求基本解的系统方法。Pell 方程在代数数论（尤其是二次域的单位群）、逼近理论和密码学中有重要应用。

## 直观解释

Pell 方程可以看作是在寻找对 $\sqrt{d}$ 的"最佳整数逼近"。方程 $x^2 - dy^2 = 1$ 可以改写为 $(x/y)^2 \approx d$，即 $x/y \approx \sqrt{d}$。Pell 方程的解给出了用有理数 $x/y$ 逼近无理数 $\sqrt{d}$ 的极佳例子。基本解（最小正整数解）就像是一台"生成器"：一旦找到它，就可以通过幂运算生成无穷无尽的更大解。这类似于指数函数的周期性——Pell 方程的解群与实数中的双曲函数有着深刻的类比。

## 形式化表述

设 $d$ 是一个非平方正整数，则 Pell 方程：

$$x^2 - dy^2 = 1$$

有无穷多组正整数解 $(x, y)$。

若 $(x_1, y_1)$ 是基本解（最小的正整数解），则所有解可由递推公式给出：

$$x_n + y_n \sqrt{d} = (x_1 + y_1 \sqrt{d})^n, \quad n = 1, 2, 3, \dots$$

等价地：

$$\begin{pmatrix} x_n \\ y_n \end{pmatrix} = \begin{pmatrix} x_1 & dy_1 \\ y_1 & x_1 \end{pmatrix}^{{n-1}} \begin{pmatrix} x_1 \\ y_1 \end{pmatrix}$$

其中：

- 基本解 $(x_1, y_1)$ 可通过 $\sqrt{d}$ 的连分数展开求得
- $x_n + y_n \sqrt{d}$ 是环 $\mathbb{Z}[\sqrt{d}]$ 中的单位
- 解群同构于无限循环群

## 证明思路

1. **连分数展开**：$\sqrt{d}$ 的连分数展开是周期性的，其收敛分数给出 $\sqrt{d}$ 的最佳有理逼近
2. **基本解存在性**：连分数的某个收敛分数 $p_k/q_k$ 满足 $p_k^2 - dq_k^2 = 1$，这就是基本解
3. **单位群结构**：在环 $\mathbb{Z}[\sqrt{d}]$ 中，范数为 1 的单位构成无限循环群，由基本解生成
4. **无穷解生成**：$(x_1 + y_1 \sqrt{d})^n$ 的展开自动给出新的整数解

核心洞察在于 Pell 方程的解对应于二次域 $\mathbb{Q}(\sqrt{d})$ 中范数为 1 的单位元。

## 示例

### 示例 1：d = 2

方程 $x^2 - 2y^2 = 1$ 的基本解是 $(3, 2)$。生成更多解：
$(3 + 2\sqrt{2})^2 = 17 + 12\sqrt{2}$，得 $(17, 12)$；
$(3 + 2\sqrt{2})^3 = 99 + 70\sqrt{2}$，得 $(99, 70)$。
验证：$99^2 - 2 \times 70^2 = 9801 - 9800 = 1$。

### 示例 2：d = 61

$x^2 - 61y^2 = 1$ 的基本解是 $(1766319049, 226153980)$，这是历史上著名的困难例子，展示了连分数方法找到大解的能力。

### 示例 3：Brahmagupta 恒等式

若 $(x_1, y_1)$ 和 $(x_2, y_2)$ 是 $x^2 - dy^2 = k$ 的解，则通过复合：
$(x_1 x_2 + dy_1 y_2)^2 - d(x_1 y_2 + x_2 y_1)^2 = k^2$。这是生成 Pell 解的早期方法。

## 应用

- **代数数论**：实二次域的单位群结构和类数计算
- **丢番图逼近**：用有理数逼近二次无理数的最佳结果
- **密码学**：基于 Pell 方程的公钥密码系统（Pell 曲线密码学）
- **平方根计算**：古代和近代快速计算平方根的算法
- **组合数学**：某些递归序列（如 Pell 数）的生成和性质

## 相关概念

- 连分数 (Continued Fraction)：表示实数的一种迭代逼近方法
- 基本解 (Fundamental Solution)：Pell 方程的最小正整数解
- 二次域 (Quadratic Field)：形如 $\mathbb{Q}(\sqrt{d})$ 的数域
- 单位群 (Unit Group)：环中乘法可逆元构成的群
- 范数 (Norm)：$N(x + y\sqrt{d}) = x^2 - dy^2$

## 参考

### 教材

- [K. Ireland, M. Rosen. A Classical Introduction to Modern Number Theory. Springer, 1990. Chapter 17]
- [H. Davenport. The Higher Arithmetic. Cambridge, 8th edition, 2008. Chapter 4]

### 在线资源

- [Mathlib4 - Pell](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Pell.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*