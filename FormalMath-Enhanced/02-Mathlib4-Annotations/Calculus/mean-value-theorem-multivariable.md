# 多变量中值定理 (Multivariable Mean Value Theorem)

## Mathlib4 引用

```lean
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Basic

namespace MultivariableMeanValue

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- 多变量中值定理 -/
theorem mean_value_theorem (f : E → F) (x y : E)
    (hf : DifferentiableOn ℝ f (segment ℝ x y)) :
    ∃ z ∈ segment ℝ x y, ‖f y - f x‖ ≤ ‖fderiv ℝ f z‖ * ‖y - x‖ := by
  -- 利用单变量中值定理和链式法则
  sorry

/-- 增量估计 -/
theorem increment_estimate (f : E → F) (x y : E) (M : ℝ)
    (hf : DifferentiableOn ℝ f (segment ℝ x y))
    (hM : ∀ z ∈ segment ℝ x y, ‖fderiv ℝ f z‖ ≤ M) :
    ‖f y - f x‖ ≤ M * ‖y - x‖ := by
  -- 直接应用中值定理
  sorry

/-- 等式形式（实值函数）-/
theorem mean_value_theorem_equality (f : E → ℝ) (x y : E)
    (hf : DifferentiableOn ℝ f (segment ℝ x y)) :
    ∃ z ∈ segment ℝ x y, f y - f x = fderiv ℝ f z (y - x) := by
  -- 实值函数可以得到等式
  sorry

end MultivariableMeanValue
```

## 数学背景

多变量中值定理是单变量微分学中值定理向高维空间的推广。虽然严格等式形式在向量值函数中不再成立（因为无法保证各分量的中值点是同一点），但存在不等式形式的中值估计。这一定理由Augustin-Louis Cauchy和后来的数学家发展完善，是多元微分学的基础工具。

## 直观解释

多变量中值定理告诉我们：**函数值的变化量可以被导数的大小控制**。想象在山坡上行走：你从一个点到另一个点的海拔变化，不会超过最大坡度的某个倍数乘以行走距离。这与单变量的"平均变化率等于某点瞬时变化率"有相似之处，但在高维中只能得到不等式估计。

## 形式化表述

设 $f: \mathbb{R}^n \to \mathbb{R}^m$ 在连接 $x$ 和 $y$ 的线段上可微，则：

**不等式形式**：
$$\|f(y) - f(x)\| \leq \sup_{z \in [x,y]} \|Df(z)\| \cdot \|y - x\|$$

**实值函数的等式形式**（$f: \mathbb{R}^n \to \mathbb{R}$）：
$$f(y) - f(x) = Df(z) \cdot (y - x)$$

对某个 $z$ 在线段 $[x,y]$ 上成立。

## 证明思路

1. **参数化线段**：定义 $g(t) = f(x + t(y-x))$，$t \in [0,1]$
2. **单变量中值定理**：对 $g$ 应用中值定理
3. **链式法则**：$g'(t) = Df(x + t(y-x))(y-x)$
4. **范数估计**：$\|g(1) - g(0)\| \leq \sup \|g'(t)\|$
5. **算子范数性质**：$\|Df(z)(y-x)\| \leq \|Df(z)\| \cdot \|y-x\|$

## 示例

### 示例 1：Lipschitz估计

若 $\|Df(x)\| \leq L$ 对所有 $x$ 成立，则 $f$ 是 $L$-Lipschitz的：

$$\|f(y) - f(x)\| \leq L \|y - x\|$$

### 示例 2：常值函数判定

若 $Df(x) = 0$ 在连通开集上处处成立，则 $f$ 是常值函数。

## 应用

- **Lipschitz连续性判定**：由导数有界推出函数Lipschitz
- **误差估计**：数值方法的截断误差分析
- **逆函数定理证明**：局部可逆性的关键引理
- **凸优化**：梯度下降法的收敛性分析

## 相关概念

- [单变量中值定理](./mean-value-theorem.md)：一维版本
- [Taylor定理](./taylor-theorem.md)：中值定理的高阶推广
- [Lipschitz连续性](./lipschitz-continuity.md)：函数光滑性度量
- [Gateaux导数](./gateaux-derivative.md)：方向导数概念

## 参考

### 教材

- [Rudin. Principles of Mathematical Analysis. McGraw-Hill, 3rd edition, 1976. Chapter 9]
- [Hubbard & Hubbard. Vector Calculus. Matrix Editions, 2015. Chapter 2]

### 在线资源

- [Mathlib4 文档 - Mean Value](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/MeanValue.html)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
