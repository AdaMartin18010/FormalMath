---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: 费马小定理 (Fermat's Little Theorem)
---
# 费马小定理 (Fermat's Little Theorem)

## Mathlib4 引用

```lean
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.ZMod.Basic

namespace Nat

variable {p : ℕ} (hp : p.Prime)

/-- 费马小定理 -/
theorem fermatLittleTheorem (a : ℕ) (hpa : ¬p ∣ a) : a ^ (p - 1) ≡ 1 [MOD p] := by
  have h : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.eq_iff_modEq_nat p]
  simpa using ZMod.pow_card_sub_one_eq_one (ZMod.unitOfCoprime _
    (Nat.coprime_iff_gcd_eq_one.mpr (Nat.gcd_eq_right (Nat.dvd_iff_modEq_zero.mp hpa)).symm))

/-- 等价形式：$a^p \equiv a \pmod{p}$ -/
theorem fermatLittleTheorem' (a : ℕ) : a ^ p ≡ a [MOD p] := by
  by_cases h : p ∣ a
  · simp [Nat.dvd_iff_modEq_zero.mp h, Nat.ModEq.zero]
  · have := fermatLittleTheorem hp a h
    rw [← Nat.mul_mod_mul_left, ← pow_succ, tsub_add_cancel_of_le]
    exact Nat.Prime.one_le hp

end Nat
```

## 数学背景

费马小定理是数论中最基本和优美的结果之一，由皮埃尔·德·费马（Pierre de Fermat）于1640年提出。虽然费马没有给出证明，但欧拉在1736年首次证明了这一定理。该定理是初等数论的基石，也是现代密码学（特别是 RSA 算法）的数学基础。

## 直观解释

费马小定理告诉我们：**如果 $p$ 是素数，那么对于不被 $p$ 整除的整数 $a$，$a^{p-1}$ 模 $p$ 等于 1**。可以理解为：在模 $p$ 的乘法群中，任何元素的阶都整除 $p-1$。

想象一个时钟有 $p$ 个小时刻度（$p$ 为素数），从刻度 $a$ 开始，每次前进 $a$ 个刻度。经过 $p-1$ 次跳跃后，你一定会回到刻度 1。

## 形式化表述

设 $p$ 是素数，$a$ 是不被 $p$ 整除的整数，则：

$$a^{p-1} \equiv 1 \pmod{p}$$

等价形式（对任意整数 $a$）：

$$a^p \equiv a \pmod{p}$$

在群论语言中，若 $a \not\equiv 0 \pmod{p}$，则 $a$ 在乘法群 $(\mathbb{Z}/p\mathbb{Z})^\times$ 中的阶整除 $p-1$。

## 证明思路

### 群论证明（欧拉）：

1. **乘法群结构**：$(\mathbb{Z}/p\mathbb{Z})^\times$ 是阶为 $p-1$ 的群
2. **拉格朗日定理**：元素 $a$ 的阶 $d$ 整除群的阶 $p-1$
3. **结论**：$a^{p-1} = (a^d)^{(p-1)/d} \equiv 1^{(p-1)/d} = 1 \pmod{p}$

### 组合证明：

1. **项链计数**：考虑由 $a$ 种颜色的 $p$ 颗珠子组成的项链
2. **旋转等价**：不计旋转的项链数为 $\frac{a^p - a}{p} + a$
3. **整数性**：项链数必为整数，故 $p \mid (a^p - a)$

## 示例

### 示例 1：基本验证

验证 $2^{10} \equiv 1 \pmod{11}$。

$2^5 = 32 \equiv -1 \pmod{11}$

$2^{10} = (2^5)^2 \equiv (-1)^2 = 1 \pmod{11}$

验证成功。

### 示例 2：大数取模

计算 $3^{100} \pmod{7}$。

由费马小定理，$3^6 \equiv 1 \pmod{7}$。

$3^{100} = 3^{6 \cdot 16 + 4} = (3^6)^{16} \cdot 3^4 \equiv 1^{16} \cdot 81 \equiv 81 \equiv 4 \pmod{7}$

### 示例 3：素性测试（费马测试）

检验 $n = 341$ 是否为素数。

$2^{340} \mod 341$：计算得 $2^{10} = 1024 \equiv 1 \pmod{341}$（因为 $341 = 11 \cdot 31$）

$2^{340} = (2^{10})^{34} \equiv 1^{34} = 1 \pmod{341}$

通过费马测试，但 $341 = 11 \cdot 31$ 是合数（卡迈克尔数）。

## 应用

- **RSA 加密**：公钥密码系统的数学基础
- **素性测试**：费马测试和 Miller-Rabin 测试
- **伪随机数生成**：线性同余生成器
- **分圆多项式**：单位根和代数数论
- **组合数学**：项链计数和 Polya 计数理论

## 相关概念

- 欧拉定理 (Euler's Theorem)：费马小定理的推广
- 欧拉函数 (Euler's Totient Function)：计算缩系的元素个数
- 原根 (Primitive Root)：阶恰好为 $p-1$ 的元素
- 卡迈克尔数 (Carmichael Number)：伪素数
- 离散对数 (Discrete Logarithm)：密码学中的困难问题

## 参考

### 教材

- [Hardy & Wright. An Introduction to the Theory of Numbers. Oxford, 6th edition, 2008. Chapter 6]
- [Niven, Zuckerman, Montgomery. An Introduction to the Theory of Numbers. Wiley, 5th edition, 1991. Chapter 2]

### 历史文献

- [Fermat. Letter to Frénicle, 1640]
- [Euler. Theorematum quorundam ad numeros primos spectantium demonstratio. 1736]

### 在线资源

- [Mathlib4 文档 - ZMod][https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/ZMod/Basic.html](需更新)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
