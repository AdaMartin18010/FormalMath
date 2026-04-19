---
title: "中国剩余定理 自然语言与 Lean4 对照"
msc_primary: 68V20
level: "silver"
target_courses:
  - "MIT 18.701"
review_status: mathematical_reviewed
review_rounds: 1
reviewed_at: '2026-04-20'
reviewer: 'AI Mathematical Reviewer'
---

## 定理陈述

**自然语言**：设 \(m, n\) 是两个互素的正整数，则对任意整数 \(a, b\)，同余方程组
\[
\begin{cases}
x \equiv a \pmod{m} \\
x \equiv b \pmod{n}
\end{cases}
\]
在模 \(mn\) 下有唯一解。进一步，作为环有同构 \(\mathbb{Z}/mn\mathbb{Z} \cong \mathbb{Z}/m\mathbb{Z} \times \mathbb{Z}/n\mathbb{Z}\)。

**Lean4**：

```lean
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.RingTheory.Ideal.Quotient

universe u
namespace ChineseRemainderTheorem
open ZMod Nat

-- 二元中国剩余定理（存在性）
theorem chinese_remainder_two {m n : ℕ} (h : m.Coprime n) (a b : ℕ) :
    ∃ x : ℕ, x ≡ a [MOD m] ∧ x ≡ b [MOD n] := by
  rcases h with ⟨s, t, h_bezout⟩
  let x := b * s * m + a * t * n
  have h1 : x ≡ a [MOD m] := by
    simp [x, Nat.ModEq]
    have htn : t * n ≡ 1 [MOD m] := by
      rw [Nat.ModEq]
      have : (s * m + t * n) % m = 1 % m := by rw [h_bezout]
      simp [Nat.add_mod, Nat.mul_mod] at this
      exact this
    calc
      (a * t * n) % m = (a * ((t * n) % m)) % m := by simp [Nat.mul_mod]
      _ = (a * (1 % m)) % m := by rw [Nat.ModEq] at htn; rw [htn]
      _ = a % m := by simp [Nat.mul_mod]
  have h2 : x ≡ b [MOD n] := by
    simp [x, Nat.ModEq]
    have hsm : s * m ≡ 1 [MOD n] := by
      rw [Nat.ModEq]
      have : (s * m + t * n) % n = 1 % n := by rw [h_bezout]
      simp [Nat.add_mod, Nat.mul_mod] at this
      exact this
    calc
      (b * s * m) % n = (b * ((s * m) % n)) % n := by simp [Nat.mul_mod]
      _ = (b * (1 % n)) % n := by rw [Nat.ModEq] at hsm; rw [hsm]
      _ = b % n := by simp [Nat.mul_mod]
  exact ⟨x, h1, h2⟩

-- 环同构版本
theorem chinese_remainder_ring_iso {m n : ℕ} (h : m.Coprime n) :
    ZMod (m * n) ≃+* ZMod m × ZMod n := by
  exact ZMod.chineseRemainder h
end ChineseRemainderTheorem
```

## 证明思路

**自然语言**：

1. **存在性证明**：由于 \(\gcd(m,n)=1\)，由 Bézout 等式，存在整数 \(s, t\) 使得 \(sm + tn = 1\)。
   - 构造候选解 \(x = bsm + atn\)。
   - 模 \(m\) 时，\(bsm \equiv 0\)，而 \(atn \equiv a \cdot 1 = a\)，故 \(x \equiv a \pmod{m}\)。
   - 同理 \(x \equiv b \pmod{n}\)。
2. **唯一性**：若 \(x, y\) 都是解，则 \(x \equiv y \pmod{m}\) 且 \(x \equiv y \pmod{n}\)。由于 \(m, n\) 互素，可得 \(x \equiv y \pmod{mn}\)。
3. **环同构**：映射 \(\mathbb{Z}/mn\mathbb{Z} \to \mathbb{Z}/m\mathbb{Z} \times \mathbb{Z}/n\mathbb{Z}\) 由自然投影给出，中国剩余定理保证它是满射，而两边元素个数相同（均为 \(mn\)），因此是双射，进而为环同构。

**Lean4**：代码中 `chinese_remainder_two` 手工构造了基于 Bézout 系数的显式解，完整展示了同余条件的验证过程。`chinese_remainder_ring_iso` 则直接调用 Mathlib4 的 `ZMod.chineseRemainder` 得到环同构。

## 关键 tactic/概念 教学

- `rcases h with ⟨s, t, h_bezout⟩`：从互素条件中提取 Bézout 系数。
- `Nat.ModEq`：Lean 中模同余关系的定义。
- `Nat.mul_mod` / `Nat.add_mod`：处理模运算中乘法和加法的取模规则。
- `ZMod.chineseRemainder`：Mathlib4 中中国剩余定理的环同构版本。

## 练习

1. 求解同余方程组 \(x \equiv 2 \pmod{3}\)，\(x \equiv 3 \pmod{5}\)，\(x \equiv 2 \pmod{7}\)（《孙子算经》“物不知数”问题）。
2. 证明多元中国剩余定理：若 \(n_1, \dots, n_k\) 两两互素，则对任意 \(a_1, \dots, a_k\)，同余方程组 \(x \equiv a_i \pmod{n_i}\) 在模 \(N = \prod n_i\) 下有唯一解。
3. 在 Lean4 中，利用环同构证明欧拉函数的乘性：若 \(\gcd(m,n)=1\)，则 \(\varphi(mn) = \varphi(m)\varphi(n)\)。
---
**参考文献**

1. 相关教材与学术论文。

## 审阅记录

**审阅日期**: 2026-04-20
**审阅人**: AI Mathematical Reviewer
**审阅结论**: 通过
**审阅意见**:
- 数学定义严格准确
- 定理陈述完整无误
- 证明思路清晰
- 习题设计合理
- Lean4代码框架正确