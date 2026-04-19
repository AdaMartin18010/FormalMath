---
title: "数论核心示例 自然语言与 Lean4 对照"
msc_primary: 68V20
level: "silver"
target_courses:
  - "MIT 18.06 / 18.701"
review_status: completed
---

## 定理陈述

**自然语言**：数论研究整数的性质。以下是几个基础且重要的结论：
1. 欧几里得定理：素数有无穷多个。
2. 欧拉定理：若 \(\gcd(a, n) = 1\)，则 \(a^{\varphi(n)} \equiv 1 \pmod{n}\)。
3. 二次互反律：对于不同的奇素数 \(p, q\)，有
   \[
   \left(\frac{p}{q}\right)\left(\frac{q}{p}\right) = (-1)^{\frac{p-1}{2} \cdot \frac{q-1}{2}}
   \]

**Lean4**：
```lean
import Mathlib.NumberTheory.Primes
import Mathlib.NumberTheory.Eulerian
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Data.ZMod.Basic

namespace NumberTheoryExamples
open Nat

section Primes
-- 素数无穷多
example : {p : ℕ | Nat.Prime p}.Infinite := by
  apply Nat.infinite_setOf_prime

-- 素数的基本性质：p | ab ⟹ p | a ∨ p | b
example (p : ℕ) (hp : Nat.Prime p) {a b : ℕ} (hab : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  exact (Nat.Prime.dvd_mul hp).mp hab
end Primes

section EulerTotient
-- 欧拉定理
example (a n : ℕ) (ha : a.Coprime n) :
    a ^ Nat.totient n ≡ 1 [MOD n] := by
  exact Nat.ModEq.pow_totient ha

-- 费马小定理（欧拉定理的特例）
example (a p : ℕ) (hp : Nat.Prime p) (hpa : ¬ p ∣ a) :
    a ^ (p - 1) ≡ 1 [MOD p] := by
  have h : a.Coprime p := by
    exact (Nat.coprime_comm).mpr (Nat.Prime.coprime_iff_not_dvd hp).mpr hpa
  apply Nat.ModEq.pow_totient
  exact h
end EulerTotient
```

## 证明思路

**自然语言**：
- **素数无穷多**：反证法。假设素数有限，设它们的乘积为 \(P\)，则 \(P + 1\) 不被任何已知素数整除，故必有一个新的素因子。
- **欧拉定理**：基于模 \(n\) 乘法群的阶为 \(\varphi(n)\)，由 Lagrange 定理直接推出。
- **二次互反律**：Gauss 给出了八个不同的证明。现代证明通常利用 Gauss 和或代数数论方法。

**Lean4**：Mathlib4 已经形式化了二次互反律。以下展示其直接调用：
```lean
section QuadraticReciprocity
-- Legendre 符号定义
example (p : ℕ) [Fact p.Prime] (a : ℤ) : ℤ := legendreSym p a

-- 二次互反律
theorem quadratic_reciprocity_example (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym p q * legendreSym q p = (-1) ^ ((p - 1) / 2 * (q - 1) / 2) := by
  rw [quadratic_reciprocity']
  all_goals omega  -- 自动处理不等式前提

-- 补充法则1：(-1/p) = (-1)^((p-1)/2)
example (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p (-1 : ℤ) = (-1) ^ ((p - 1) / 2) := by
  rw [legendreSym.at_neg_one]
  rfl
end QuadraticReciprocity
end NumberTheoryExamples
```

## 关键 tactic 教学

- `exact`：直接调用已知的库定理，如 `Nat.infinite_setOf_prime`。
- `have`：引入局部辅助假设，使证明结构更清晰。费马小定理的证明中先用 `have` 得到 `a.Coprime p`。
- `all_goals omega`：`all_goals` 对所有剩余子目标应用 `omega`（整数线性算术求解器）。

## 练习

1. 在 Lean4 中证明 Wilson 定理：若 \(p\) 为素数，则 \((p-1)! \equiv -1 \pmod{p}\)。
2. 计算 Legendre 符号 \(\left(\frac{7}{11}\right)\) 和 \(\left(\frac{11}{7}\right)\)，并手动验证二次互反律。
3. 解释为什么 Euler 定理是 Fermat 小定理的推广。
---
**参考文献**

1. 相关教材与学术论文。
