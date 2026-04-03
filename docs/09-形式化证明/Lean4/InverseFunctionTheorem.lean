/-
# 逆函数定理的形式化证明 / Inverse Function Theorem

## 领域
多元微积分 / 非线性分析 (Multivariable Calculus / Nonlinear Analysis)

## Mathlib4对应
- **模块**: `Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv`
- **核心定理**: `HasStrictFDerivAt.to_localInverse`
- **相关定义**:
  - `HasStrictFDerivAt`
  - `OpenPartialHomeomorph`
  - `ContinuousLinearEquiv`

## MSC2020编码
- **Primary**: 26B10
- **Secondary**: 58C20

## 对齐课程
- MIT 18.101 (Analysis and Manifolds)
- Harvard Math 212a (Real Analysis)
- Princeton MAT 425 (Analysis III: Integration Theory and Hilbert Spaces)
- ETH 401-1461-00L (Analysis III)

## 定理陈述
设 f : ℝⁿ → ℝⁿ 是 C¹ 函数，a ∈ ℝⁿ。
若 f 在 a 处的导数 Df(a) 可逆，则存在 a 的邻域 U 和 f(a) 的邻域 V，使得：
1. f|_U : U → V 是双射
2. 逆映射 f⁻¹ : V → U 是可微的
3. D(f⁻¹)(f(a)) = (Df(a))⁻¹

## 数学意义
逆函数定理是微分拓扑和流形理论的基石，保证了局部微分同胚的存在性。

## 历史背景
由Augustin-Louis Cauchy在1829年首次证明（单变量情形），现代多变量的证明归功于Ulisse Dini和 others。
-/

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.NormedSpace.FiniteDimension
import Mathlib.Data.Real.Basic

universe u v

namespace InverseFunctionTheorem

open Topology Filter Set Metric

/-
## 核心概念

### 局部逆 (Local Inverse)
函数 f 在点 a 附近有局部逆，如果存在邻域 U ∋ a 和 V ∋ f(a)，
使得 f : U → V 是双射。

### 严格Fréchet导数的可逆性
若 f 在 a 有严格Fréchet导数 f'，且 f' 是线性同构，
则 f 在 a 附近有局部逆，且逆的导数为 f'⁻¹。
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

-- 逆函数定理：核心形式
theorem inverse_function_theorem {f : E → F} {f' : E ≃L[𝕜] F} {a : E}
    (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    HasStrictFDerivAt (hf.localInverse f f' a) (f'.symm : F →L[𝕜] E) (f a) := by
  /- 使用Mathlib4的逆函数定理 -/
  exact hf.to_localInverse

-- 局部左逆的导数
theorem inverse_function_left {f : E → F} {g : F → E} {f' : E ≃L[𝕜] F} {a : E}
    (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a)
    (hg : ∀ᶠ y in 𝓝 (f a), g (f y) = y)
    (hga : g (f a) = a) :
    HasStrictFDerivAt g (f'.symm : F →L[𝕜] E) (f a) := by
  /- 局部左逆的导数也是 f'⁻¹ -/
  exact hf.to_local_left_inverse hg hga

-- ℝⁿ 上的逆函数定理（简化形式）
theorem inverse_function_rn {n : ℕ} {f : (Fin n → ℝ) → (Fin n → ℝ)} {a : (Fin n → ℝ)}
    (hf : HasStrictFDerivAt f (fderiv ℝ f a) a)
    (hinv : Invertible (fderiv ℝ f a)) :
    ∃ (U V : Set (Fin n → ℝ)),
    IsOpen U ∧ IsOpen V ∧ a ∈ U ∧ f a ∈ V ∧
    Set.BijOn f U V := by
  /- 从严格导数导出局部双射 -/
  let f' := (fderiv ℝ f a)
  have hf' : HasStrictFDerivAt f (f' : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) a := hf
  /- 构造局部同胚 -/
  let e := hf'.toOpenPartialHomeomorph f
    ((LinearEquiv.toContinuousLinearEquiv (hinv.1.toLinearEquiv)) : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
  use e.source, e.target
  constructor
  · exact e.open_source
  constructor
  · exact e.open_target
  constructor
  · exact e.mem_source_self
  constructor
  · exact e.mem_target_self
  · exact e.bijOn

end InverseFunctionTheorem

/-
## 应用示例

### 极坐标变换

f(r, θ) = (r cos θ, r sin θ)
在 (r, θ) ≠ (0, ·) 处Jacobian可逆，故有局部逆（即极坐标）。

### 球坐标变换

f(ρ, φ, θ) = (ρ sin φ cos θ, ρ sin φ sin θ, ρ cos φ)
在适当区域内Jacobian可逆。

## 数学意义

逆函数定理的重要性：

1. **局部微分同胚**: 判断函数何时是局部微分同胚
2. **坐标变换**: 保证局部坐标系的存在性
3. **流形结构**: 是定义流形和图册的基础
4. **优化理论**: 在约束优化和Lagrange乘子法中有应用

## 与隐函数定理的关系

逆函数定理 ⟹ 隐函数定理：
- 给定 F(x, y) = 0，构造函数 G(x, y) = (x, F(x, y))
- 对 G 应用逆函数定理，可导出隐函数定理

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv`: 逆函数定理
- `HasStrictFDerivAt.to_localInverse`: 逆函数的导数
- `HasStrictFDerivAt.toOpenPartialHomeomorph`: 构造局部同胚
- `Mathlib.Analysis.Calculus.FDeriv.Basic`: Fréchet导数
-/
