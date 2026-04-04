/-
# 模论基础定理

## 数学背景

模是线性空间在环上的推广。
若R是环，M是阿贝尔群，R作用在M上满足线性性，
则称M是R-模。

## 基本概念
- 子模、商模
- 模同态
- 直和与直积
- 自由模
- 正合序列

## 重要定理
- 同态基本定理
- 自由模的泛性质
- 直和分解

## Mathlib4对应
- `Mathlib.Algebra.Module.LinearMap`
- `Mathlib.Algebra.Module.Submodule`

-/]

import FormalMath.Mathlib.Algebra.Module.LinearMap
import FormalMath.Mathlib.Algebra.Module.Submodule
import FormalMath.Mathlib.Algebra.Module.Prod
import FormalMath.Mathlib.Algebra.Module.Pi
import FormalMath.Mathlib.Algebra.DirectSum.Module
import FormalMath.Mathlib.LinearAlgebra.FreeModule.Basic
import FormalMath.Mathlib.LinearAlgebra.Exact

namespace ModuleTheory

open Submodule LinearMap DirectSum

variable {R M N P : Type*} [Ring R] [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-
## 模同态基本定理

**第一同构定理**：M/ker(f) ≅ im(f)

证明思路：
1. 构造商模到像的映射：[x] ↦ f(x)
2. 验证这是良定义的：若x - y ∈ ker(f)，则f(x) = f(y)
3. 证明这是线性同构

这是模论中最基本的定理之一，建立了商模与同态像之间的自然同构。
-/
theorem first_isomorphism_theorem 
    (f : M →ₗ[R] N) :
    (M ⧸ LinearMap.ker f) ≃ₗ[R] LinearMap.range f := by
  -- 使用Mathlib中已证明的第一同构定理
  apply LinearMap.quotKerEquivRange

/-
## 子模的对应定理

若N ⊆ M是子模，则M/N的子模与包含N的M的子模一一对应。

证明思路：
1. 正向映射：将M/N的子模P提升为M中包含N的子模
   P ↦ {x ∈ M | [x] ∈ P}
2. 反向映射：将包含N的子模Q投影到M/N
   Q ↦ {[x] | x ∈ Q}
3. 验证这是互逆的双射

这是格论中的重要结果，称为