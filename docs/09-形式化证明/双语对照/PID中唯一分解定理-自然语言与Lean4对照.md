---
title: "PID中唯一分解定理 自然语言与 Lean4 对照"
level: "silver"
target_courses:
  - "MIT 18.701"
---

## 定理陈述

**自然语言**：设 \(R\) 是主理想整环（PID），则 \(R\) 也是唯一分解整环（UFD）。即在 PID 中，每个非零非单位元素都可以唯一地（在相伴和顺序意义下）分解为不可约元的乘积。

**Lean4**：

```lean
import Mathlib.RingTheory.UniqueFactorizationDomain
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.EuclideanDomain

universe u
namespace UniqueFactorizationInPID
open UniqueFactorizationMonoid Irreducible

variable {R : Type u} [CommRing R] [IsDomain R]

-- PID 是 UFD
theorem pid_is_ufd [IsPrincipalIdealRing R] :
    UniqueFactorizationMonoid R := by
  infer_instance

-- 欧几里得整环是 PID，因此也是 UFD
theorem euclidean_is_ufd [EuclideanDomain R] :
    UniqueFactorizationMonoid R := by
  infer_instance

-- 整数环 ℤ 是 UFD
instance : UniqueFactorizationMonoid ℤ := by
  infer_instance
end UniqueFactorizationInPID
```

## 证明思路

**自然语言**：证明 PID 是 UFD 需要验证分解的**存在性**和**唯一性**。

1. **存在性**：
   - 在 PID 中，理想的升链必然稳定（ACC，即诺特性）。假设存在某个元素没有不可约分解，可以构造一个无限严格递增的理想升链，与 ACC 矛盾。因此每个非零非单位元素必有不可约分解。
2. **唯一性**：
   - 在 PID 中，不可约元等价于素元。证明如下：设 \(p\) 是不可约元，且 \(p \mid ab\)。考虑理想 \((p, a)\)，由于 PID 中所有理想都是主理想，存在 \(d\) 使得 \((p, a) = (d)\)。因为 \(d \mid p\) 且 \(p\) 不可约，\(d\) 要么是单位（此时 \((p,a)=R\)，于是 \(1 = px + ay\)，乘以 \(b\) 得 \(b = p(bx) + (ab)y\)，故 \(p \mid b\)），要么与 \(p\) 相伴（此时 \(p \mid a\)）。因此 \(p\) 是素元。
   - 一旦证明了不可约元都是素元，分解的唯一性便可通过标准的归纳法证明：若 \(p_1 \cdots p_n = q_1 \cdots q_m\)，则 \(p_1\) 整除某个 \(q_j\)，由于两者均不可约，它们相伴。消去后继续归纳即可。

**Lean4**：Mathlib4 已经通过类型类推导将 `IsPrincipalIdealRing` 自动实现为 `UniqueFactorizationMonoid` 的实例。`infer_instance` 让 Lean 自动找到这一推导链。欧几里得整环（如 \(\mathbb{Z}\)）通过 `EuclideanDomain → IsPrincipalIdealRing → UniqueFactorizationMonoid` 的实例链，自然也是 UFD。

## 关键 tactic/概念 教学

- `infer_instance`：利用 Lean 的类型类实例解析系统自动查找并应用已注册的代数结构实例。
- `UniqueFactorizationMonoid`（UFD）：Mathlib4 中唯一分解整环的定义，要求存在唯一分解。
- `IsPrincipalIdealRing`（PID）：主理想整环的类型类。
- 在 Mathlib4 中，不可约元与素元的等价性由 `Prime.irreducible` 和 `Irreducible.isPrime`（在 UFD/PID 中）等引理保证。

## 练习

1. 在 Lean4 中验证：多项式环 \(\mathbb{Q}[x]\) 是 UFD。
2. 证明：在主理想整环中，每个非零素理想都是极大理想。
3. 解释为什么 \(\mathbb{Z}[\sqrt{-5}]\) 不是 UFD（提示：考虑 \(6 = 2 \cdot 3 = (1+\sqrt{-5})(1-\sqrt{-5})\)）。
