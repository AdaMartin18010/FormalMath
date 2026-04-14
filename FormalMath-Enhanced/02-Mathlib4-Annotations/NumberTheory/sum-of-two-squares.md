---
msc_primary: 00A99
processed_at: '2026-04-15'
title: 两平方和定理 (Sum of Two Squares Theorem)
---
# 两平方和定理 (Sum of Two Squares Theorem)

## Mathlib4 引用

```lean
import Mathlib.NumberTheory.SumTwoSquares

namespace NumberTheory

/-- 费马两平方和定理：奇素数 p 可表示为两平方和当且仅当 p ≡ 1 (mod 4) -/
theorem fermat_sum_of_two_squares {p : ℕ} (hp : Nat.Prime p) (hodd : p ≠ 2) :
    (∃ a b : ℕ, a^2 + b^2 = p) ↔ p ≡ 1 [MOD 4] := by
  -- 必要性由高斯整数环的素因子分解得到，充分性由 Euler 下降法证明
  sorry

end NumberTheory
```

## 数学背景

两平方和定理是数论中最优美的结果之一，通常归功于皮埃尔·德·费马（Pierre de Fermat），虽然他并未留下完整的证明。该定理断言：一个奇素数 $p$ 可以表示为两个整数的平方和（即 $p = a^2 + b^2$）当且仅当 $p \equiv 1 \pmod{4}$。欧拉于1749年首次发表完整证明，后来高斯通过高斯整数环 $\mathbb{Z}[i]$ 的算术提供了更深刻的代数证明。这一定理是代数数论的启蒙性结果，揭示了整数环与虚二次域之间的深刻联系。

## 直观解释

两平方和定理揭示了一个关于素数的奇妙规律。素数按照除以 4 的余数可以分为两类：$4k+1$ 型和 $4k+3$ 型。定理告诉我们，$4k+1$ 型的素数总可以写成两个平方数之和（如 $5 = 1^2 + 2^2$，$13 = 2^2 + 3^2$，$29 = 2^2 + 5^2$），而 $4k+3$ 型的素数则永远不能（如 3, 7, 11, 19）。这背后的原因在于高斯整数环 $\mathbb{Z}[i]$ 中，$4k+1$ 型素数可以进一步分解为 $(a + bi)(a - bi)$，而 $4k+3$ 型素数在这个环中仍然是素数。

## 形式化表述

设 $p$ 是奇素数，则：

$$p = a^2 + b^2 \text{ 对某整数 } a, b \iff p \equiv 1 \pmod{4}$$

更一般地，正整数 $n$ 可表示为两平方和当且仅当在其素因子分解中，所有形如 $4k+3$ 的素因子的指数都是偶数。

在高斯整数环 $\mathbb{Z}[i] = \{a + bi : a, b \in \mathbb{Z}\}$ 中：

- $p \equiv 1 \pmod{4}$ 时，$p$ 在 $\mathbb{Z}[i]$ 中可分解：$p = (a + bi)(a - bi)$
- $p \equiv 3 \pmod{4}$ 时，$p$ 在 $\mathbb{Z}[i]$ 中仍为素数
- $2 = (1 + i)(1 - i) = -i(1 + i)^2$ 是特殊的 ramified 素数

其中：

- $a, b \in \mathbb{Z}$（可以为零，但通常要求非零以得到非平凡表示）

## 证明思路

1. **必要性**：若 $p = a^2 + b^2$，则模 4 下平方数只能是 0 或 1，故 $p \equiv 0, 1, 2 \pmod{4}$。因 $p$ 是奇素数，必有 $p \equiv 1 \pmod{4}$
2. **充分性（Euler 下降法）**：利用威尔逊定理的推论，当 $p \equiv 1 \pmod{4}$ 时，$-1$ 是模 $p$ 的二次剩余，即存在 $x$ 使 $x^2 \equiv -1 \pmod{p}$
3. **无穷下降**：从 $x^2 + 1^2 = kp$ 出发，通过巧妙的代数操作构造出更小的倍数，最终得到 $a^2 + b^2 = p$
4. **高斯整数视角**：$p \equiv 1 \pmod{4}$ 时，$p$ 在 $\mathbb{Z}[i]$ 中分裂为共轭素理想的乘积

核心洞察在于 $\mathbb{Z}[i]$ 是唯一分解整环，其素因子分解揭示了整数的平方和表示。

## 示例

### 示例 1：p = 5

$5 = 1^2 + 2^2$。且 $5 \equiv 1 \pmod{4}$。在高斯整数环中，$5 = (1 + 2i)(1 - 2i)$。

### 示例 2：p = 13

$13 = 2^2 + 3^2$。且 $13 \equiv 1 \pmod{4}$。分解为 $13 = (2 + 3i)(2 - 3i)$。

### 示例 3：一般整数

$65 = 5 \times 13 = (1^2 + 2^2)(2^2 + 3^2)$。利用 Brahmagupta-Fibonacci 恒等式：
$(1^2 + 2^2)(2^2 + 3^2) = (1\cdot2 - 2\cdot3)^2 + (1\cdot3 + 2\cdot2)^2 = (-4)^2 + 7^2 = 16 + 49 = 65$。
同时 $65 = 1^2 + 8^2$，说明表示可能不唯一。

## 应用

- **代数数论**：虚二次域和类域论的启蒙实例
- **高斯整数环**：$\mathbb{Z}[i]$ 的算术和素因子分解理论
- **密码学**：某些基于二次形式的公钥密码协议
- **组合设计**：有限射影平面和区组设计中的参数约束
- **光学与信号处理**：两平方和与相位恢复的数学联系

## 相关概念

- 高斯整数 (Gaussian Integer)：形如 $a + bi$ 的复数，$a, b \in \mathbb{Z}$
- 唯一分解整环 (UFD)：每个元素可唯一分解为素元乘积的环
- 二次剩余 (Quadratic Residue)：模 $p$ 下存在平方根的整数
- Euler 下降法 (Infinite Descent)：费马发明的一种证明技巧
- Brahmagupta-Fibonacci 恒等式：$(a^2+b^2)(c^2+d^2) = (ac-bd)^2 + (ad+bc)^2$

## 参考

### 教材

- [K. Ireland, M. Rosen. A Classical Introduction to Modern Number Theory. Springer, 1990. Chapter 8]
- [D. Cox. Primes of the Form x² + ny². Wiley, 1989. Chapter 1]

### 在线资源

- [Mathlib4 - SumTwoSquares](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/SumTwoSquares.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*