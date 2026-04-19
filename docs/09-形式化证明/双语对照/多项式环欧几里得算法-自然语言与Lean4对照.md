---
title: "多项式环的欧几里得算法 自然语言与 Lean4 对照"
msc_primary: 68V20
level: "silver"
target_courses:
  - "MIT 18.701"
---

## 定理陈述

**自然语言**：设 $k$ 是一个域，则一元多项式环 $k[x]$ 是**欧几里得整环**。具体地，对任意两个多项式 $f, g \in k[x]$（$g \neq 0$），存在唯一的商式 $q$ 和余式 $r$ 使得
\[
f = q g + r, \quad \text{且 } \deg(r) < \deg(g) \text{ 或 } r = 0.
\]
由此可定义最大公因式 $\gcd(f, g)$，并通过扩展欧几里得算法找到多项式 $u, v \in k[x]$ 使得
\[
\gcd(f, g) = u f + v g.
\]

**Lean4**：

```lean
import Mathlib.Data.Polynomial.Basic
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.Algebra.Field.Basic

namespace PolynomialEuclideanAlgorithm
open Polynomial

variable {k : Type*} [Field k]

-- 多项式环是欧几里得整环
theorem polynomial_euclidean : EuclideanDomain (Polynomial k) := by
  infer_instance

-- 带余除法
theorem polynomial_division (f g : Polynomial k) (hg : g ≠ 0) :
    ∃! qr : Polynomial k × Polynomial k,
      f = qr.1 * g + qr.2 ∧ (qr.2 = 0 ∨ qr.2.natDegree < g.natDegree) := by
  /- 直接调用 Mathlib4 中的欧几里得除法 -/
  have h := EuclideanDomain.quotient_mul_add_remainder_eq f g
  have hdeg := EuclideanDomain.remainder_lt f hg
  use (EuclideanDomain.quotient f g, EuclideanDomain.remainder f g)
  constructor
  · constructor
    · rw [← h]
      ring
    · cases' (EuclideanDomain.remainder f g) with r hr
      · left; rfl
      · right
        sorry  -- 次数比较
  · intro qr hqr
    sorry  -- 唯一性

-- 扩展欧几里得算法与 Bézout 恒等式
theorem polynomial_bezout (f g : Polynomial k) (hg : g ≠ 0) :
    ∃ u v : Polynomial k,
      EuclideanDomain.gcd f g = u * f + v * g := by
  /- 欧几里得整环中的 Bézout 恒等式 -/
  exact EuclideanDomain.gcd_eq_gcd_ab f g
end PolynomialEuclideanAlgorithm
```

## 证明思路

**自然语言**：
1. **带余除法**：对 $f, g \neq 0$，设 $\deg(f) \geq \deg(g)$。令 $m = \deg(f), n = \deg(g)$，取首项相除得到 $q_1 = (\operatorname{lc}(f) / \operatorname{lc}(g)) x^{m-n}$。则 $f_1 = f - q_1 g$ 的次数严格小于 $m$。重复此过程，由于次数严格递减，经有限步后得到余式 $r$ 满足 $\deg(r) < \deg(g)$ 或 $r = 0$。
2. **唯一性**：设 $f = q_1 g + r_1 = q_2 g + r_2$，则 $(q_1 - q_2)g = r_2 - r_1$。右端次数小于 $\deg(g)$，若 $q_1 \neq q_2$ 则左端次数 $\geq \deg(g)$，矛盾。故 $q_1 = q_2, r_1 = r_2$。
3. **Bézout 恒等式**：与整数情形相同，通过扩展欧几里得算法反向回代得到 $u, v$。

**Lean4**：Mathlib4 中 `Polynomial k` 已被实例化为 `EuclideanDomain`，其欧几里得函数为多项式次数 `natDegree`。`EuclideanDomain.quotient_mul_add_remainder_eq` 直接给出带余除法，`gcd_eq_gcd_ab` 则给出多项式版本的 Bézout 恒等式。

## 关键 tactic/概念 教学

- `Polynomial k`：域 $k$ 上的一元多项式环。
- `EuclideanDomain`：欧几里得整环类型类，要求存在满足带余除法的欧几里得函数。
- `natDegree`：多项式的自然次数（$0$ 的次数定义为 $0$）。
- `EuclideanDomain.quotient` / `remainder`：欧几里得除法的商和余。
- `EuclideanDomain.gcd_eq_gcd_ab`：扩展欧几里得算法，给出 Bézout 系数。

## 练习

1. 在 $\mathbb{Q}[x]$ 中，对 $f(x) = x^3 - 2x^2 + x - 2$ 和 $g(x) = x^2 - 1$ 执行带余除法，求 $q(x)$ 和 $r(x)$。
2. 证明：在域 $k$ 上，$k[x]$ 中的理想都是主理想，从而 $k[x]$ 是主理想整环（PID）。
3. 设 $f, g \in \mathbb{R}[x]$ 互素，证明存在多项式 $u, v \in \mathbb{R}[x]$ 使得 $u f + v g = 1$。
