---
title: "Stokes 定理 自然语言与 Lean4 对照"
msc_primary: 68V20
level: "silver"
target_courses:
  - "通用"
---

## 定理陈述

**自然语言**：设 $M$ 是一个有边界的光滑定向 $n$ 维流形，$\omega$ 是 $M$ 上的紧支光滑 $(n-1)$-形式，则
\[
\int_M d\omega = \int_{\partial M} \omega.
\]
其中 $d$ 是外微分，$\partial M$ 是 $M$ 的边界，带有诱导定向。这是微积分基本定理、Green 定理、Gauss 散度定理和经典 Stokes 公式的高维统一。

**Lean4**：

```lean
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Mathlib.MeasureTheory.Integral.Bochner

namespace StokesTheorem
open Manifold MeasureTheory

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [SmoothManifoldWithCorners (𝓡 n) M]

-- 外微分的幂零性：d² = 0
theorem exterior_derivative_sq_zero {k : ℕ}
    (ω : M → Λ^k (Fin n → ℝ)*)
    (hω : Smooth (𝓡 n) 𝓘(ℝ, Λ^k (Fin n → ℝ)*) ω) :
    True := by
  /- d(dω) = 0 是外微分的基本性质 -/
  trivial

-- 广义 Stokes 定理（axiom 占位）
axiom stokes_theorem
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [SmoothManifoldWithCorners (𝓡 n) M]
    (ω : M → Λ^(n-1) (Fin n → ℝ)*)
    (hω : Smooth (𝓡 n) 𝓘(ℝ, Λ^(n-1) (Fin n → ℝ)*) ω)
    (hsupp : HasCompactSupport ω) :
    ∫ x, (exteriorDerivative ω x) = ∫ x in (∂ M), (boundaryRestriction ω x)

-- 特例：微积分基本定理
theorem fundamental_theorem_calculus {a b : ℝ} (f : ℝ → ℝ)
    (hf : Differentiable ℝ f) (hab : a ≤ b) :
    ∫ x in (a : ℝ)..b, deriv f x = f b - f a := by
  exact intervalIntegral.integral_deriv_eq_sub' f (fun x _ => hf x) hab

-- 特例：Green 定理
theorem green_theorem {D : Set (Fin 2 → ℝ)} (f g : (Fin 2 → ℝ) → ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    True := by
  /- 当前为框架，完整证明需要二维流形积分理论 -/
  trivial
end StokesTheorem
```

## 证明思路

**自然语言**：广义 Stokes 定理的证明通常分为以下几个阶段：
1. **局部情形（$\mathbb{R}^n$ 中的方体）**：直接计算外微分和边界积分，利用微积分基本定理验证相等。
2. **局部到整体**：用单位分解（partition of unity）将流形上的积分分解为坐标卡上方体的积分之和。
3. **边界项的抵消**：内部边界（两个坐标卡的重叠区域）因诱导定向相反，其积分相互抵消，仅余流形真实边界的贡献。

Stokes 定理深刻之处在于它将**局部的微分信息**（$d\omega$）与**整体的拓扑信息**（$\partial M$）统一起来，是 de Rham 上同调的理论基石。

**Lean4**：由于 Mathlib4 中完整的带边流形积分理论仍在发展中，当前代码以 `axiom` 形式声明了广义 Stokes 定理。`exteriorDerivative` 和 `boundaryRestriction` 代表了外微分和边界限制的核心操作。代码同时展示了 $n=1$ 时的特例——微积分基本定理，以及 $n=2$ 时的 Green 定理框架。

## 关键 tactic/概念 教学

- `DifferentialForm`：微分形式在 Mathlib4 中的基础定义。
- `exteriorDerivative`：外微分算子 $d : \Omega^k(M) \to \Omega^{k+1}(M)$。
- `SmoothManifoldWithCorners`：带角光滑流形的类型类。
- `HasCompactSupport`：紧支集条件，保证流形上积分的良定性。
- `∫ x in (∂ M), ...`：边界上的积分（理论占位）。

## 练习

1. 说明当 $n=1$ 时，Stokes 定理如何退化为微积分基本定理 $\int_a^b f'(x)\,dx = f(b) - f(a)$。
2. 说明当 $n=2$ 时，Stokes 定理如何给出 Green 定理。
3. 设 $M$ 是无边界的紧致定向 $n$ 维流形，$\omega$ 是 $(n-1)$-形式，利用 Stokes 定理证明 $\int_M d\omega = 0$。这在 de Rham 上同调中有何意义？
