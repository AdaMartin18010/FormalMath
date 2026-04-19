---
title: "环的第一同构定理 自然语言与 Lean4 对照"
msc_primary: 68V20
level: "silver"
target_courses:
  - "MIT 18.701"
---

## 定理陈述

**自然语言**：设 \(\varphi: R \to S\) 是环同态，则商环 \(R / \ker(\varphi)\) 与同态的像 \(\operatorname{im}(\varphi)\) 同构，即
\[
R / \ker(\varphi) \cong \operatorname{im}(\varphi).
\]

**Lean4**：

```lean
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.Algebra.Ring.Hom.Ring
import Mathlib.RingTheory.Ideal.Basic

universe u v
namespace RingFirstIsomorphismTheorem
open Ideal Quotient

variable {R S : Type*} [CommRing R] [CommRing S]

-- 环的第一同构定理
theorem ring_first_isomorphism (φ : R →+* S) :
    R ⧸ (RingHom.ker φ) ≃+* φ.range := by
  exact Ideal.quotientKerEquivRange φ
end RingFirstIsomorphismTheorem
```

## 证明思路

**自然语言**：环的第一同构定理与群版本完全类似，只是需要额外验证乘法结构的保持。
1. **构造映射**：定义 \(\psi: R/\ker(\varphi) \to \operatorname{im}(\varphi)\) 为 \(\psi(r + \ker(\varphi)) = \varphi(r)\)。
2. **良定义性**：若 \(r - s \in \ker(\varphi)\)，则 \(\varphi(r - s) = 0\)，故 \(\varphi(r) = \varphi(s)\)。
3. **环同态性**：
   - 加法：\(\psi((r+\ker)+(s+\ker)) = \psi(r+s+\ker) = \varphi(r+s) = \varphi(r)+\varphi(s) = \psi(r+\ker)+\psi(s+\ker)\)。
   - 乘法：\(\psi((r+\ker)(s+\ker)) = \psi(rs+\ker) = \varphi(rs) = \varphi(r)\varphi(s) = \psi(r+\ker)\psi(s+\ker)\)。
   - 单位元：\(\psi(1+\ker) = \varphi(1) = 1\)。
4. **单射与满射**：与群的情形相同，分别是核的平凡性和像的定义。

**Lean4**：Mathlib4 通过 `Ideal.quotientKerEquivRange` 直接提供了环的第一同构定理。该定理将商环 \(R/\ker(\varphi)\) 与 \(\varphi\) 的像建立环同构。

```lean
-- 核是理想（自动满足）
example (φ : R →+* S) : Ideal R := RingHom.ker φ

-- 像是子环
example (φ : R →+* S) : Subring S := φ.range
```

## 关键 tactic/概念 教学

- `R ⧸ I`：Mathlib4 中商环的记法，其中 \(I\) 是 `Ideal R`。
- `RingHom.ker`：环同态的核，它自动构成一个理想。
- `RingHom.range`：环同态的像，构成子环。
- `Ideal.quotientKerEquivRange`：Mathlib4 中环的第一同构定理的标准实现。

## 练习

1. 利用环的第一同构定理证明：\(\mathbb{Z}[x]/(x) \cong \mathbb{Z}\)。
2. 证明：若 \(I, J\) 是交换环 \(R\) 的理想且 \(I + J = R\)，则 \(R/(I \cap J) \cong R/I \times R/J\)（中国剩余定理的环版本）。
3. 在 Lean4 中验证：自然投影 \(\mathbb{Z} \to \mathbb{Z}/n\mathbb{Z}\) 的核是由 \(n\) 生成的主理想。
