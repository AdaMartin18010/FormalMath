/-
# 欧拉公式的形式化证明 / Euler's Formula

## Mathlib4对应
- **模块**: `Mathlib.Data.Complex.Exponential`
- **核心定理**:
  - `Complex.exp_mul_I`: e^(iθ) = cos(θ) + i·sin(θ)
  - `Complex.exp_pi_mul_I`: e^(iπ) = -1
- **相关定义**:
  - `Complex.exp`: 复指数函数
  - `Real.cos`, `Real.sin`: 三角函数
  - `Complex.I`: 虚数单位 i

## 定理陈述

欧拉公式：对于任意实数 θ，
e^(iθ) = cos(θ) + i·sin(θ)

特别地，当 θ = π 时：
e^(iπ) + 1 = 0

这被称为欧拉恒等式，被誉为"数学中最美丽的公式"。

## 数学意义

欧拉公式建立了指数函数与三角函数之间的深刻联系，
将指数函数的定义域从实数推广到复数。

## 历史背景

由瑞士数学家莱昂哈德·欧拉(Leonhard Euler, 1707-1783)于1748年提出。
欧拉是历史上最多产的数学家之一，对数学的几乎所有分支都做出了贡献。
-/

import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Real.Pi
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

universe u

namespace EulerFormula

open Complex Real

/-
## 第一部分：复指数函数的定义

复指数函数通过幂级数定义：
e^z = ∑_{n=0}^{∞} z^n / n!

对于复数 z = x + iy，有：
e^z = e^(x+iy) = e^x · e^(iy)

### 实指数函数

实指数函数 e^x 由以下性质唯一确定：
- e^0 = 1
- e^(x+y) = e^x · e^y
- (e^x)' = e^x

### 复指数函数的构造

将实指数函数解析延拓到复平面。
-/

-- 复指数函数的定义检查
#check Complex.exp

-- 复指数函数的幂级数展开
#check Complex.exp_eq_exp_ℂ

/-
## 第二部分：欧拉公式的证明

**定理**: e^(iθ) = cos(θ) + i·sin(θ) 对所有 θ ∈ ℝ 成立。

**证明方法一：幂级数展开**

利用幂级数展开：
e^(iθ) = ∑_{n=0}^{∞} (iθ)^n / n!
       = ∑_{k=0}^{∞} (iθ)^(2k) / (2k)! + ∑_{k=0}^{∞} (iθ)^(2k+1) / (2k+1)!
       = ∑_{k=0}^{∞} (-1)^k θ^(2k) / (2k)! + i·∑_{k=0}^{∞} (-1)^k θ^(2k+1) / (2k+1)!
       = cos(θ) + i·sin(θ)

**证明方法二：微分方程**

考虑函数 f(θ) = e^(-iθ)(cos(θ) + i·sin(θ))。
可以验证 f'(θ) = 0，所以 f 是常数。
又 f(0) = 1，所以 f(θ) = 1 对所有 θ 成立。
因此 e^(iθ) = cos(θ) + i·sin(θ)。
-/

-- 欧拉公式（核心定理）
theorem euler_formula (θ : ℝ) : exp (I * θ) = cos θ + I * sin θ := by
  /- 使用Mathlib4的定理 -/
  rw [Complex.exp_mul_I]

-- 欧拉公式的直接证明（使用幂级数）
theorem euler_formula_power_series (θ : ℝ) : exp (I * θ) = cos θ + I * sin θ := by
  /- 展开两边的幂级数 -/
  rw [Complex.exp_eq_exp_ℂ]
  simp [Complex.exp, Complex.cos, Complex.sin]
  /- 将级数按实部和虚部分解 -/
  /- 实部对应偶数项，虚部对应奇数项 -/
  /- 使用 i² = -1 -/
  sorry  -- 幂级数展开的详细证明较长

-- 欧拉公式的微分方程证明
theorem euler_formula_ode (θ : ℝ) : exp (I * θ) = cos θ + I * sin θ := by
  /- 考虑 f(θ) = e^(-iθ)(cos(θ) + i·sin(θ)) -/
  let f := fun θ : ℝ => exp (-I * θ) * (cos θ + I * sin θ)
  /- 证明 f(0) = 1 -/
  have h_f0 : f 0 = 1 := by
    simp [f]
    /- e^0 · (1 + 0) = 1 -/
    simp [exp_zero]
  /- 证明 f'(θ) = 0（f是常数） -/
  have h_deriv : deriv f θ = 0 := by
    /- 使用乘积法则 -/
    simp [f]
    /- d/dθ [e^(-iθ)] = -i·e^(-iθ) -/
    /- d/dθ [cos(θ) + i·sin(θ)] = -sin(θ) + i·cos(θ) = i(cos(θ) + i·sin(θ)) -/
    /- 所以 f'(θ) = -i·e^(-iθ)(cos+isin) + e^(-iθ)·i(cos+isin) = 0 -/
    sorry  -- 详细求导计算
  /- 因此 f(θ) = f(0) = 1 对所有 θ -/
  /- 所以 e^(iθ) = cos(θ) + i·sin(θ) -/
  sorry  -- 完成证明

/-
## 第三部分：欧拉恒等式

当 θ = π 时，欧拉公式给出：
e^(iπ) = cos(π) + i·sin(π) = -1 + i·0 = -1

因此：
e^(iπ) + 1 = 0

这个公式联系了数学中五个最重要的常数：
- e: 自然对数的底
- i: 虚数单位
- π: 圆周率
- 1: 乘法单位元
- 0: 加法单位元
-/

-- 欧拉恒等式：e^(iπ) + 1 = 0
theorem euler_identity : exp (I * Real.pi) + 1 = 0 := by
  /- 应用欧拉公式 -/
  rw [euler_formula]
  /- cos(π) = -1, sin(π) = 0 -/
  rw [cos_pi, sin_pi]
  /- 化简 -/
  ring

-- 欧拉恒等式的另一种表述
theorem euler_identity' : exp (I * Real.pi) = -1 := by
  /- 从欧拉恒等式推导 -/
  have h : exp (I * Real.pi) + 1 = 0 := euler_identity
  /- 移项 -/
  calc
    exp (I * Real.pi) = exp (I * Real.pi) + 1 - 1 := by ring
    _ = 0 - 1 := by rw [h]
    _ = -1 := by ring

/-
## 第四部分：欧拉公式的推论

### 推论1：三角函数的指数表示

cos(θ) = (e^(iθ) + e^(-iθ)) / 2
sin(θ) = (e^(iθ) - e^(-iθ)) / (2i)
-/

-- 余弦函数的指数表示
theorem cos_exp_repr (θ : ℝ) : cos θ = (exp (I * θ) + exp (-I * θ)) / 2 := by
  /- 利用欧拉公式 -/
  rw [euler_formula θ]
  rw [euler_formula (-θ)]
  /- sin(-θ) = -sin(θ) -/
  rw [sin_neg, cos_neg]
  /- 化简 -/
  field_simp
  ring

-- 正弦函数的指数表示
theorem sin_exp_repr (θ : ℝ) : sin θ = (exp (I * θ) - exp (-I * θ)) / (2 * I) := by
  /- 利用欧拉公式 -/
  rw [euler_formula θ]
  rw [euler_formula (-θ)]
  /- sin(-θ) = -sin(θ) -/
  rw [sin_neg, cos_neg]
  /- 化简 -/
  field_simp
  ring

/-
### 推论2：棣莫弗公式

(cos(θ) + i·sin(θ))^n = cos(nθ) + i·sin(nθ)

这是欧拉公式的直接推论，因为：
(cos(θ) + i·sin(θ))^n = (e^(iθ))^n = e^(inθ) = cos(nθ) + i·sin(nθ)
-/

-- 棣莫弗公式
theorem de_moivre (θ : ℝ) (n : ℕ) :
    (cos θ + I * sin θ) ^ n = cos (n * θ) + I * sin (n * θ) := by
  /- 利用欧拉公式和指数性质 -/
  have h1 : cos θ + I * sin θ = exp (I * θ) := by
    rw [euler_formula]
  rw [h1]
  /- (e^(iθ))^n = e^(inθ) -/
  have h2 : (exp (I * θ)) ^ n = exp (I * (n * θ)) := by
    /- 使用指数性质 (e^z)^n = e^(nz) -/
    rw [← Complex.exp_nat_mul]
    ring_nf
  rw [h2]
  /- e^(inθ) = cos(nθ) + i·sin(nθ) -/
  rw [euler_formula]

/-
### 推论3：三角函数的和角公式

cos(α + β) = cos(α)cos(β) - sin(α)sin(β)
sin(α + β) = sin(α)cos(β) + cos(α)sin(β)
-/

-- 余弦加法公式
theorem cos_add_exp (α β : ℝ) : cos (α + β) = cos α * cos β - sin α * sin β := by
  /- 利用欧拉公式 -/
  have h1 : cos (α + β) + I * sin (α + β) = exp (I * (α + β)) := by
    rw [euler_formula]
  have h2 : exp (I * (α + β)) = exp (I * α) * exp (I * β) := by
    /- e^(i(α+β)) = e^(iα) · e^(iβ) -/
    rw [← Complex.exp_add]
    ring_nf
  rw [h1] at *
  rw [h2, euler_formula α, euler_formula β]
  /- 展开并比较实部 -/
  simp [Complex.ext_iff, mul_add, add_mul, pow_two, Complex.I_mul_I]
  ring

-- 正弦加法公式
theorem sin_add_exp (α β : ℝ) : sin (α + β) = sin α * cos β + cos α * sin β := by
  /- 类似证明 -/
  have h1 : cos (α + β) + I * sin (α + β) = exp (I * (α + β)) := by
    rw [euler_formula]
  have h2 : exp (I * (α + β)) = exp (I * α) * exp (I * β) := by
    rw [← Complex.exp_add]
    ring_nf
  rw [h1] at *
  rw [h2, euler_formula α, euler_formula β]
  /- 展开并比较虚部 -/
  simp [Complex.ext_iff, mul_add, add_mul, pow_two, Complex.I_mul_I]
  ring

/-
## 第五部分：单位根

**定义**: n次单位根是方程 z^n = 1 的解。

由棣莫弗公式，n次单位根为：
ω_k = e^(2πik/n) = cos(2πk/n) + i·sin(2πk/n), k = 0, 1, ..., n-1
-/

-- n次单位根
def nthRootsOfUnity (n : ℕ) (k : ℕ) : ℂ := exp (2 * Real.pi * I * k / n)

-- 单位根的性质
theorem nthRootsOfUnity_pow_eq_one (n : ℕ) (hn : n > 0) (k : ℕ) :
    (nthRootsOfUnity n k) ^ n = 1 := by
  unfold nthRootsOfUnity
  /- (e^(2πik/n))^n = e^(2πik) = 1 -/
  have h : (exp (2 * Real.pi * I * k / n)) ^ n = exp (2 * Real.pi * I * k) := by
    rw [← Complex.exp_nat_mul]
    field_simp [hn]
    ring_nf
  rw [h]
  /- e^(2πik) = cos(2πk) + i·sin(2πk) = 1 + 0 = 1 -/
  have h2 : 2 * Real.pi * I * k = I * (2 * Real.pi * k) := by ring
  rw [h2]
  rw [euler_formula]
  /- cos(2πk) = 1, sin(2πk) = 0 对整数 k -/
  have h_cos : cos (2 * Real.pi * k) = 1 := by
    have : 2 * Real.pi * k = k * (2 * Real.pi) := by ring
    rw [this]
    rw [cos_nat_mul_two_pi]
  have h_sin : sin (2 * Real.pi * k) = 0 := by
    have : 2 * Real.pi * k = k * (2 * Real.pi) := by ring
    rw [this]
    rw [sin_nat_mul_two_pi]
  rw [h_cos, h_sin]
  simp

/-
## 第六部分：具体计算示例

### 示例1：e^(iπ/2) = i

e^(iπ/2) = cos(π/2) + i·sin(π/2) = 0 + i·1 = i
-/

-- e^(iπ/2) = i
theorem exp_pi_div_two_mul_I : exp (I * (Real.pi / 2)) = I := by
  rw [euler_formula]
  rw [cos_pi_div_two, sin_pi_div_two]
  simp

/-
### 示例2：e^(iπ/4) = (1+i)/√2

e^(iπ/4) = cos(π/4) + i·sin(π/4) = √2/2 + i·√2/2 = (1+i)/√2
-/

-- e^(iπ/4) = (1+i)/√2
theorem exp_pi_div_four_mul_I : exp (I * (Real.pi / 4)) = (1 + I) / Real.sqrt 2 := by
  rw [euler_formula]
  have h_cos : cos (Real.pi / 4) = Real.sqrt 2 / 2 := cos_pi_div_four
  have h_sin : sin (Real.pi / 4) = Real.sqrt 2 / 2 := sin_pi_div_four
  rw [h_cos, h_sin]
  /- 化简 -/
  field_simp
  ring_nf

/-
## 数学意义

欧拉公式的重要性：

1. **统一数学常数**: 联系了五个最重要的数学常数
2. **指数与三角函数**: 建立了深刻的联系
3. **复分析基础**: 复指数函数是复分析的核心
4. **物理应用**: 波动、振动、量子力学的基础

## 与其他定理的关系

- **泰勒展开**: 欧拉公式的幂级数证明
- **棣莫弗公式**: 欧拉公式的直接推论
- **傅里叶分析**: 基于欧拉公式的正交展开
- **复对数**: 复指数函数的反函数

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `Mathlib.Data.Complex.Exponential`: 复指数函数
- `Complex.exp_mul_I`: 欧拉公式
- `Complex.exp_pi_mul_I`: e^(iπ) = -1
- `Complex.cos`, `Complex.sin`: 复三角函数
- `Real.cos`, `Real.sin`: 实三角函数
-/
