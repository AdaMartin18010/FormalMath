# 逆函数定理 (Inverse Function Theorem)

## Mathlib4 引用

```lean
import Mathlib.Analysis.Calculus.Inverse
import Mathlib.Analysis.Calculus.FDeriv.Basic

namespace InverseFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- 逆函数定理 -/
theorem inverse_function_theorem (f : E → F) (x₀ : E)
    (hf : ContDiff ℝ 1 f) (hinv : IsInvertible (fderiv ℝ f x₀)) :
    ∃ s ∈ nhds x₀, ∃ t ∈ nhds (f x₀),
      (∀ x ∈ s, f x ∈ t) ∧
      (∀ y ∈ t, ∃! x ∈ s, f x = y) ∧
      ContDiffOn ℝ 1 (invFunOn f s) t := by
  -- 利用Banach不动点定理构造逆函数
  sorry

/-- 逆函数的导数 -/
theorem inverse_derivative (f : E → F) (g : F → E) (x₀ : E) (y₀ : F)
    (hf : ContDiff ℝ 1 f) (hg : g ∘ f = id) (hfy : f x₀ = y₀)
    (hinv : IsInvertible (fderiv ℝ f x₀)) :
    fderiv ℝ g y₀ = (fderiv ℝ f x₀)⁻¹ := by
  -- 链式法则直接推导
  sorry

end InverseFunction
```

## 数学背景

逆函数定理是现代分析学的核心结果之一，其历史可追溯到柯西和维尔斯特拉斯关于隐函数的工作。该定理严格表述了"导数可逆则函数局部可逆"这一直观想法，是微分几何中流形理论和微分同胚概念的基础。

## 直观解释

逆函数定理告诉我们：**如果函数在某点的导数（线性近似）是可逆的，那么函数在该点附近也是可逆的**。就像用放大镜观察光滑曲线：如果局部看起来是"一对一"的（导数非零），那么在小范围内确实是"一对一"的。

## 形式化表述

设 $f: \mathbb{R}^n \to \mathbb{R}^n$ 是 $C^1$ 函数，$a \in \mathbb{R}^n$。若导数矩阵 $Df(a)$ 可逆，则：

1. 存在 $a$ 的邻域 $U$ 和 $f(a)$ 的邻域 $V$
2. $f: U \to V$ 是双射
3. 逆函数 $f^{-1}: V \to U$ 也是 $C^1$ 的
4. $D(f^{-1})(f(a)) = (Df(a))^{-1}$

## 证明思路

1. **归一化**：设 $a = 0$, $f(0) = 0$, $Df(0) = I$
2. **构造压缩映射**：定义 $\phi_y(x) = x - f(x) + y$
3. **Banach不动点定理**：证明 $\phi_y$ 是压缩映射
4. **隐函数存在**：不动点给出逆函数
5. **可微性证明**：利用线性逼近估计误差

## 示例

### 示例 1：极坐标变换

$f(r, \theta) = (r\cos\theta, r\sin\theta)$

雅可比行列式：$J = r$，当 $r > 0$ 时可逆

逆函数给出 $(x, y) \mapsto (\sqrt{x^2+y^2}, \arctan(y/x))$

### 示例 2：复指数函数

$f(z) = e^z$，导数 $f'(z) = e^z \neq 0$

局部可逆，但全局不可逆（周期性）。逆函数是多值的对数。

## 应用

- **微分几何**：坐标变换、流形结构
- **优化理论**：灵敏度分析
- **动力系统**：Poincaré映射
- **控制理论**：系统可观测性

## 相关概念

- [隐函数定理](./implicit-function-theorem.md)：密切相关的结果
- [微分同胚 (Diffeomorphism)](./diffeomorphism.md)：光滑可逆映射
- [雅可比行列式](./jacobian-determinant.md)：体积变换因子
- [秩定理 (Rank Theorem)](./rank-theorem.md)：更一般的定理

## 参考

### 教材

- [Spivak. Calculus on Manifolds. Benjamin, 1965. Chapter 2]
- [Hubbard & Hubbard. Vector Calculus, Linear Algebra, and Differential Forms. Matrix Editions, 2015. Chapter 2]

### 在线资源

- [Mathlib4 文档 - Inverse Function](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/Inverse.html)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
