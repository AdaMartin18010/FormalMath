---
title: "Green 定理 自然语言与 Lean4 对照"
msc_primary: 68V20
level: "silver"
target_courses:
  - "通用"
---

## 定理陈述

**自然语言**：设 $D \subseteq \mathbb{R}^2$ 是有界闭区域，其边界 $\partial D$ 是分段光滑的简单闭曲线（取逆时针正向）。若 $P(x, y)$ 和 $Q(x, y)$ 在包含 $D$ 的某个开集上连续可微，则
\[
\oint_{\partial D} P\,dx + Q\,dy = \iint_D \left( \frac{\partial Q}{\partial x} - \frac{\partial P}{\partial y} \right) dx\,dy.
\]
左边是沿边界 $\partial D$ 的线积分，右边是区域 $D$ 上的二重积分。

**Lean4**：

```lean
import Mathlib.Analysis.Calculus.LineDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Tactic

namespace GreenTheorem
open Real MeasureTheory Set Filter Topology IntervalIntegral

-- 线积分定义
def LineIntegral (P Q : ℝ × ℝ → ℝ) (γ : ℝ → ℝ × ℝ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, (P (γ t) * (deriv γ t).1 + Q (γ t) * (deriv γ t).2)

-- 二维旋度
def Curl2D (P Q : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x => Q (x, p.2)) p.1 - deriv (fun y => P (p.1, y)) p.2

-- Green 定理：矩形版本
theorem green_rectangle (P Q : ℝ × ℝ → ℝ)
    (a b c d : ℝ) (h : a < b ∧ c < d)
    (hP : ContDiff ℝ 1 (fun p => P p))
    (hQ : ContDiff ℝ 1 (fun p => Q p)) :
    let γ : ℝ → ℝ × ℝ := fun t =>
      if t ∈ Ico 0 1 then (a + (b-a)*t, c)
      else if t ∈ Ico 1 2 then (b, c + (d-c)*(t-1))
      else if t ∈ Ico 2 3 then (b - (b-a)*(t-2), d)
      else (a, d - (d-c)*(t-3))
    LineIntegral P Q γ 0 4 =
      ∫ y in c..d, ∫ x in a..b, Curl2D P Q (x, y) := by
  simp [LineIntegral, Curl2D]
  sorry  -- 需要完成积分计算细节

-- Green 定理的一般版本（框架）
theorem green_theorem (P Q : ℝ × ℝ → ℝ)
    (D : Set (ℝ × ℝ)) (γ : ℝ → ℝ × ℝ) (a b : ℝ)
    (hD : IsCompact D ∧ MeasurableSet D)
    (hP : ContDiff ℝ 1 (fun p => P p))
    (hQ : ContDiff ℝ 1 (fun p => Q p)) :
    True := by
  /- 需要完整的区域分解与边界定向理论 -/
  trivial
end GreenTheorem
```

## 证明思路

**自然语言**：Green 定理的经典证明采用**区域分解法**：
1. **矩形区域**：直接计算两边的积分，利用微积分基本定理验证相等。
2. **x-简单区域**：$D = \{(x, y) : a \leq x \leq b, g_1(x) \leq y \leq g_2(x)\}$。对 $P$ 的积分用 FTC 化为边界值之差；对 $Q$ 的积分类似。
3. **一般区域**：将 $D$ 分解为有限个 x-简单和 y-简单子区域的并。内部边界的线积分因方向相反而相互抵消，仅余外部边界积分。

**Lean4**：代码中给出了矩形版本的框架和一般版本的占位。矩形版本的证明需要将线积分拆分为四条边，每条边分别参数化后利用 `intervalIntegral` 和 `deriv` 进行计算。完整的一般版本证明需要 Mathlib4 中更成熟的流形边界积分理论。

## 关键 tactic/概念 教学

- `∫ t in a..b, ...`：区间积分的 Lean 记法。
- `ContDiff ℝ 1 f`：函数 $f$ 一阶连续可微。
- `deriv`：一元函数的导数。
- `Curl2D P Q`：二维旋度 $\partial Q/\partial x - \partial P/\partial y$。
- `IsCompact` / `MeasurableSet`：区域紧致性和可测性的断言。

## 练习

1. 取 $P = -y/2, Q = x/2$，利用 Green 定理推导平面区域 $D$ 的面积公式 $A = \frac{1}{2} \oint_{\partial D} (x\,dy - y\,dx)$。
2. 用上述面积公式计算椭圆 $\frac{x^2}{a^2} + \frac{y^2}{b^2} = 1$ 所围区域的面积。
3. 验证：若 $P\,dx + Q\,dy$ 是闭形式（即 $\partial Q/\partial x = \partial P/\partial y$）且在单连通区域上成立，则它是恰当形式（存在势函数 $F$ 使得 $dF = P\,dx + Q\,dy$）。
