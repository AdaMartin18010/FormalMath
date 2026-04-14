---
msc_primary: 00A99
processed_at: '2026-04-15'
title: 中国剩余定理 (Chinese Remainder Theorem)
---
# 中国剩余定理 (Chinese Remainder Theorem)

## Mathlib4 引用

```lean
import Mathlib.NumberTheory.Divisors

namespace NumberTheory

variable {m n : ℕ} (hcoprime : m.Coprime n)

/-- 中国剩余定理：若 m, n 互素，则环同态 Z/(mn)Z → Z/mZ × Z/nZ 是同构 -/
theorem chinese_remainder_theorem :
    (ZMod (m * n)) ≃+* (ZMod m) × (ZMod n) := by
  -- 构造显式逆映射，利用 Bézout 恒等式找到系数
  sorry

end NumberTheory
```

## 数学背景

中国剩余定理是数论中最古老、最著名的定理之一，其起源可追溯至中国古代数学经典《孙子算经》（约公元3-5世纪）。该定理系统地解决了一次同余方程组的求解问题：若模数两两互素，则同余方程组有唯一解（模所有模数之积）。这一定理不仅在数论中具有核心地位，也是抽象代数中环的直积分解、现代密码学（尤其是 RSA 算法）和计算代数的基础。

## 直观解释

中国剩余定理可以用一个生活中的调度问题来理解：假设有三艘船的航线周期分别是 3 天、5 天和 7 天，它们今天同时靠港。问多少天后它们会再次同时靠港？答案是 105 天（即 $3 \times 5 \times 7$）。更一般地，定理告诉我们：如果你知道一艘船在每个周期中的具体停靠日，只要周期互素，就总能找到一个唯一的日期（在 105 天内）符合所有条件。这体现了互素模数下的信息可以完全独立地编码在一个更大的模数中。

## 形式化表述

设 $n_1, n_2, \dots, n_k$ 是两两互素的正整数，$N = n_1 n_2 \cdots n_k$。则对任意整数 $a_1, a_2, \dots, a_k$，同余方程组：

$$\begin{cases} x \equiv a_1 \pmod{n_1} \\ x \equiv a_2 \pmod{n_2} \\ \vdots \\ x \equiv a_k \pmod{n_k} \end{cases}$$

在模 $N$ 下有唯一解。

在环论语言中，若 $m, n$ 互素，则有环同构：

$$\mathbb{Z}/(mn)\mathbb{Z} \cong \mathbb{Z}/m\mathbb{Z} \times \mathbb{Z}/n\mathbb{Z}$$

其中：

- 两两互素意味着对任意 $i \neq j$ 有 $\gcd(n_i, n_j) = 1$
- $N = \prod_{{i=1}}^k n_i$ 是所有模数的乘积

## 证明思路

1. **Bézout 恒等式**：由互素性，存在整数 $s_i, t_i$ 使得 $s_i n_i + t_i (N/n_i) = 1$
2. **构造解**：令 $e_i = t_i (N/n_i)$，则 $e_i \equiv 1 \pmod{n_i}$ 且 $e_i \equiv 0 \pmod{n_j}$（$j \neq i$）
3. **显式公式**：$x = \sum_{{i=1}}^k a_i e_i \pmod{N}$ 是同余方程组的解
4. **唯一性**：若 $x, y$ 都是解，则 $x - y$ 被所有 $n_i$ 整除，故被 $N$ 整除

核心洞察在于互素模数对应的同余条件相互独立，可以分别构造基解再叠加。

## 示例

### 示例 1：孙子问题

《孙子算经》中的经典问题：今有物不知其数，三三数之剩二，五五数之剩三，七七数之剩二。即：
$$x \equiv 2 \pmod{3}, \quad x \equiv 3 \pmod{5}, \quad x \equiv 2 \pmod{7}$$
解得 $x = 23$ 是最小正整数解，通解为 $x \equiv 23 \pmod{105}$。

### 示例 2：大数模运算

计算 $2^{{100}} \pmod{77}$。因 $77 = 7 \times 11$，可分别计算 $2^{{100}} \equiv 2 \pmod{7}$ 和 $2^{{100}} \equiv 1 \pmod{11}$，再用中国剩余定理合并得 $2^{{100}} \equiv 23 \pmod{77}$。

### 示例 3：环同构

$\mathbb{Z}/6\mathbb{Z} \cong \mathbb{Z}/2\mathbb{Z} \times \mathbb{Z}/3\mathbb{Z}$。映射 $x \mapsto (x \bmod 2, x \bmod 3)$ 是双射：0↦(0,0), 1↦(1,1), 2↦(0,2), 3↦(1,0), 4↦(0,1), 5↦(1,2)。

## 应用

- **密码学**：RSA 算法中密钥生成和模运算优化
- **多项式插值**：Lagrange 插值公式的数论类比
- **纠错码**：剩余类编码和冗余校验设计
- **并行计算**：大整数运算的模分解与并行处理
- **抽象代数**：环的直积分解和理想的结构定理

## 相关概念

- 同余方程 (Congruence Equation)：模意义下的等式
- 互素 (Coprime)：最大公约数为 1 的整数对
- Bézout 恒等式：$\gcd(a,b) = 1 \iff \exists s,t : sa + tb = 1$
- 环同构 (Ring Isomorphism)：保持代数结构的双射
- Lagrange 插值：多项式版本的中国剩余定理

## 参考

### 教材

- [K. Ireland, M. Rosen. A Classical Introduction to Modern Number Theory. Springer, 1990. Chapter 2]
- [D. Shanks. Solved and Unsolved Problems in Number Theory. Chelsea, 1985. Chapter 1]

### 在线资源

- [Mathlib4 - ZMod](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/ZMod/Basic.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*