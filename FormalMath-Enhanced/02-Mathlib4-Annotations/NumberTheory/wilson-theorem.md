---
msc_primary: 00A99
processed_at: '2026-04-15'
title: Wilson 定理 (Wilson's Theorem)
---
# Wilson 定理 (Wilson's Theorem)

## Mathlib4 引用

```lean
import Mathlib.NumberTheory.Wilson

namespace NumberTheory

variable {p : ℕ} (hp : Nat.Prime p)

/-- Wilson 定理：p 是素数当且仅当 (p-1)! ≡ -1 (mod p) -/
theorem wilson_theorem :
    (p - 1).factorial ≡ -1 [MOD p] ↔ p.Prime := by
  -- 证明基于配对法：在乘法群中将互为逆元的元素配对
  sorry

end NumberTheory
```

## 数学背景

Wilson 定理由英国数学家约翰·威尔逊（John Wilson）在1770年代猜想，后由拉格朗日（Lagrange）于1771年首次证明。该定理给出了判断一个正整数是否为素数的充要条件：$p$ 是素数当且仅当 $(p-1)! \equiv -1 \pmod{p}$。虽然在实际计算中，对于大数 $p$ 计算 $(p-1)!$ 的代价极高，使得该定理不适合作为素性检验算法，但它在数论中具有重要的理论价值，是理解模乘法群结构和对称性的经典结果。

## 直观解释

Wilson 定理揭示了一个关于素数的惊人规律。想象将数字 $1, 2, \dots, p-1$ 排成一个圆圈。Wilson 定理说：如果 $p$ 是素数，那么这些数字全部相乘后，再除以 $p$，余数总是 $p-1$（即 $-1$ 模 $p$）。证明的关键在于观察：在模 $p$ 下，大多数数字都可以与自己的"乘法逆元"配对相消（比如 2 和 $(p+1)/2$ 在模 $p$ 下互为逆元），只有 1 和 $p-1$ 是自己的逆元。因此乘积中只剩下 $1 \times (p-1) = p-1 \equiv -1 \pmod{p}$。

## 形式化表述

设 $p$ 是正整数，则：

$$(p-1)! \equiv -1 \pmod{p} \iff p \text{ 是素数}$$

等价表述：

- 若 $p$ 是素数，则 $(p-1)! \equiv -1 \pmod{p}$
- 若 $(p-1)! \equiv -1 \pmod{p}$，则 $p$ 是素数

其中：

- $(p-1)! = 1 \times 2 \times \cdots \times (p-1)$ 是阶乘
- $-1 \pmod{p}$ 等价于 $p-1 \pmod{p}$
- 证明的核心在于模 $p$ 乘法群 $\mathbb{F}_p^\times$ 中，每个元素 $a$ 都有唯一的逆元 $a^{{-1}}$，且 $a = a^{{-1}}$ 当且仅当 $a \equiv \pm 1 \pmod{p}$

## 证明思路

1. **逆元配对**：在模素数 $p$ 的乘法群 $\mathbb{F}_p^\times$ 中，将每个元素 $a$ 与其逆元 $a^{{-1}}$ 配对
2. **自逆元识别**：$a = a^{{-1}}$ 当且仅当 $a^2 \equiv 1 \pmod{p}$，即 $a \equiv \pm 1 \pmod{p}$
3. **乘积化简**：除 $1$ 和 $p-1$ 外，所有元素成对相消，故 $(p-1)! \equiv 1 \cdot (p-1) \equiv -1 \pmod{p}$
4. **逆方向**：若 $p$ 是合数，设 $d$ 是 $p$ 的真因子且 $d \leq p-1$，则 $d | (p-1)!$，故 $(p-1)! \not\equiv -1 \pmod{p}$

核心洞察在于素数模下的乘法对称性导致阶乘的精确抵消。

## 示例

### 示例 1：p = 5

$(5-1)! = 24$，$24 \bmod 5 = 4 = -1 \pmod{5}$。验证 Wilson 定理：5 是素数。

### 示例 2：p = 4（合数）

$(4-1)! = 6$，$6 \bmod 4 = 2 \neq -1 \pmod{4}$。因此 4 不是素数，符合定理的逆否命题。

### 示例 3：二次剩余与 Wilson

由 Wilson 定理可推导：对奇素数 $p$，$((p-1)/2)!^2 \equiv (-1)^{{(p+1)/2}} \pmod{p}$。这是研究二次剩余和 Gauss 引理的重要工具。

## 应用

- **素性检验**：理论上判断素数的充要条件（实践中因计算量大而少用）
- **二次剩余理论**：推导二次互反律和 Legendre 符号的性质
- **组合数学**：某些计数问题和排列群的结构分析
- **代数数论**：分圆域和单位根的研究
- **群论教学**：有限乘法群中逆元配对技术的经典范例

## 相关概念

- 阶乘 (Factorial)：前 $n$ 个正整数的乘积
- 模乘法逆元 (Modular Multiplicative Inverse)：满足 $ab \equiv 1 \pmod{p}$ 的整数 $b$
- 素数 (Prime Number)：大于 1 且只有 1 和自身两个正因子的整数
- 有限域 (Finite Field)：$\mathbb{F}_p = \mathbb{Z}/p\mathbb{Z}$，$p$ 为素数
- 二次剩余 (Quadratic Residue)：模 $p$ 下存在平方根的整数

## 参考

### 教材

- [G. H. Hardy, E. M. Wright. An Introduction to the Theory of Numbers. Oxford, 6th edition, 2008. Chapter 6]
- [K. Ireland, M. Rosen. A Classical Introduction to Modern Number Theory. Springer, 1990. Chapter 4]

### 在线资源

- [Mathlib4 - Wilson](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Wilson.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*