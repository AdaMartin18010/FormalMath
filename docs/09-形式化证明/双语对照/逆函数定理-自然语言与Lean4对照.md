---
title: "逆函数定理 自然语言与 Lean4 对照"
msc_primary: 68V20
level: "silver"
target_courses:
  - "MIT 18.100A / 18.101"
---

## 定理陈述

**自然语言**：设 \(f : \mathbb{R}^n \to \mathbb{R}^n\) 是 \(C^1\) 函数，\(a \in \mathbb{R}^n\)。若 \(f\) 在 \(a\) 处的 Jacobian 矩阵 \(Df(a)\) 可逆，则存在 \(a\) 的邻域 \(U\) 和 \(f(a)\) 的邻域 \(V\)，使得

1. \(f|_U : U \to V\) 是双射；
2. 逆映射 \(f^{-1} : V \to U\) 可微；
3. \(D(f^{-1})(f(a)) = (Df(a))^{-1}\)。

**Lean4**：

```lean
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.NormedSpace.FiniteDimension

universe u v
namespace InverseFunctionTheorem
open Topology Filter Set Metric

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

-- 逆函数定理：严格 Fréchet 导数可逆时，局部逆存在且可微
theorem inverse_function_theorem {f : E → F} {f' : E ≃L[𝕜] F} {a : E}
    (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    HasStrictFDerivAt (hf.localInverse f f' a) (f'.symm : F →L[𝕜] E) (f a) := by
  exact hf.to_localInverse  -- Mathlib4 的核心结果
```

## 证明思路

**自然语言**：逆函数定理的经典证明基于压缩映射原理（Banach 不动点定理）。核心步骤是：

1. 不妨设 \(a = 0, f(a) = 0, Df(a) = I\)（通过线性变换标准化）。
2. 定义辅助映射 \(g(x) = x - f(x)\)，证明其在足够小的邻域内是压缩映射。
3. 利用压缩映射原理，构造唯一的局部逆。
4. 验证逆映射的导数满足所需的等式。

**Lean4**：Mathlib4 将上述经典证明封装在 `HasStrictFDerivAt.to_localInverse` 中。以下展示如何在 \(\mathbb{R}^n\) 的特殊情形中应用该定理构造局部同胚：

```lean
-- ℝⁿ 上的简化形式：可逆导数 ⇒ 局部双射
theorem inverse_function_rn {n : ℕ} {f : (Fin n → ℝ) → (Fin n → ℝ)} {a : Fin n → ℝ}
    (hf : HasStrictFDerivAt f (fderiv ℝ f a) a)
    (hinv : Invertible (fderiv ℝ f a)) :
    ∃ (U V : Set (Fin n → ℝ)),
    IsOpen U ∧ IsOpen V ∧ a ∈ U ∧ f a ∈ V ∧ Set.BijOn f U V := by
  let f' := fderiv ℝ f a
  have hf' : HasStrictFDerivAt f (f' : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) a := hf
  -- 利用严格导数构造局部同胚
  let e := hf'.toOpenPartialHomeomorph f
    ((LinearEquiv.toContinuousLinearEquiv (hinv.1.toLinearEquiv)) : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
  use e.source, e.target
  constructor <;> [exact e.open_source | constructor <;> [exact e.open_target |
    constructor <;> [exact e.mem_source_self | constructor <;> [exact e.mem_target_self |
      exact e.bijOn]]]]
```

## 关键 tactic 教学

- `exact`：直接应用与目标完全匹配的定理。这里 `exact hf.to_localInverse` 一步到位。
- `constructor <;> [tac1 | tac2 | ...]`：对目标中的多个子目标按顺序应用不同的 tactic，是一种“批量处理”语法。
- `let`：引入局部定义，使证明更清晰。例如 `let f' := fderiv ℝ f a`。

## 练习

1. 说明为什么逆函数定理要求 \(Df(a)\) 可逆，而不仅仅是满秩。
2. 在 Lean4 中写出极坐标变换 \(f(r, \theta) = (r\cos\theta, r\sin\theta)\) 在非原点处的 Jacobian，并验证其可逆性。
3. 解释 `HasStrictFDerivAt` 与普通的 `HasFDerivAt` 在数学上的区别。
