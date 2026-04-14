---
msc_primary: 00A99
processed_at: '2026-04-15'
title: Taylor 定理 (Taylor's Theorem)
---
# Taylor 定理 (Taylor's Theorem)

## Mathlib4 引用

```lean
import Mathlib.Analysis.Calculus.Taylor

namespace TaylorTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E} {x₀ x : ℝ} {n : ℕ}

/-- Taylor 定理：带 Lagrange 余项的 Taylor 展开 -/
theorem taylor_mean_remainder_lagrange
    (hf : ContDiffOn ℝ n f (uIcc x₀ x))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (uIcc x₀ x)) (uIoo x₀ x)) :
    ∃ x' ∈ uIoo x₀ x, f x - taylorWithinEval f n (uIcc x₀ x) x₀ x =
      iteratedDerivWithin (n + 1) f (uIcc x₀ x) x' * (x - x₀)^(n + 1) / (n + 1)! := by
  -- Mathlib4 中已完整证明
  sorry

end TaylorTheorem
```

## 数学背景

Taylor 定理由英国数学家布鲁克·泰勒（Brook Taylor）于1715年首次发表。该定理建立了光滑函数与其多项式逼近之间的精确关系，是微积分和分析学的核心工具。通过 Taylor 展开，复杂函数可在局部用多项式近似，为数值计算、物理建模和工程应用提供了坚实基础。Maclaurin 展开是 Taylor 展开在零点处的特例。

## 直观解释

Taylor 定理告诉我们：**一个足够光滑的函数在某点附近的行为，完全由其在该点的各阶导数决定**。这就像用一架多焦距相机拍摄物体：一阶导数给出倾斜程度（线性近似），二阶导数描述弯曲程度（二次修正），更高阶导数则捕捉更精细的特征。余项则量化了截断多项式逼近的误差。

## 形式化表述

设函数 $f$ 在包含 $x_0$ 的某个区间内有 $n+1$ 阶导数，则对该区间内任意 $x$，存在 $	heta 	o (0, 1)$ 使得：

$$f(x) = \sum_{k=0}^{n} \frac{f^{(k)}(x_0)}{k!}(x - x_0)^k + \frac{f^{(n+1)}(x_0 + \theta(x - x_0))}{(n+1)!}(x - x_0)^{n+1}$$

其中：

- 前 $n+1$ 项为 $n$ 阶 Taylor 多项式
- 最后一项为 Lagrange 余项

## 证明思路

1. **构造辅助函数**：定义余项函数 $R(t) = f(x) - P_n(t)$，其中 $P_n$ 为 $n$ 阶 Taylor 多项式
2. **重复应用 Rolle 定理/Cauchy 中值定理**：对 $R(t)$ 及其各阶导数逐次应用中值定理
3. **控制高阶导数**：通过 $n+1$ 阶导数在某内点的取值表达余项
4. **结论**：得到带显式余项的 Taylor 公式

核心在于反复应用中值定理将误差项与某内点的高阶导数联系起来。

## 示例

### 示例 1：指数函数的 Maclaurin 展开

$e^x = \sum_{k=0}^{n} \frac{x^k}{k!} + \frac{e^{\theta x}}{(n+1)!}x^{n+1}$，其中 $0 < \theta < 1$。

对 $x = 1$：$e \approx \sum_{k=0}^{n} \frac{1}{k!}$，余项趋于 0，故 $e = \sum_{k=0}^{\infty} \frac{1}{k!}$。

### 示例 2：正弦函数的展开

$\sin x = x - \frac{x^3}{3!} + \frac{x^5}{5!} - \cdots + (-1)^n \frac{x^{2n+1}}{(2n+1)!} + R_{2n+3}(x)$

由于 $|\sin^{(k)}(\xi)| \leq 1$，余项 $|R| \leq \frac{|x|^{2n+3}}{(2n+3)!} \to 0$。

### 示例 3：估计 $\ln(1.1)$

$\ln(1+x) = x - \frac{x^2}{2} + \frac{x^3}{3} - \cdots$

取 $x = 0.1$，一阶近似：$\ln(1.1) \approx 0.1$；二阶近似：$\ln(1.1) \approx 0.1 - 0.005 = 0.095$。实际值约 $0.09531$。

## 应用

- **数值分析**：构造插值公式、误差估计与数值积分
- **物理学**：小振动近似、微扰理论与场论展开
- **优化理论**：Hessian 矩阵与极值点的二阶条件
- **概率论**：特征函数与矩生成函数的展开
- **计算机图形学**：曲线曲面建模与动画插值

## 相关概念

- Maclaurin 展开 (Maclaurin Series)：在 $x_0 = 0$ 处的 Taylor 展开
- 幂级数 (Power Series)：Taylor 级数的无限和形式
- 解析函数 (Analytic Function)：可由收敛幂级数表示的函数
- 中值定理 (Mean Value Theorem)：Taylor 定理 $n=0$ 的特例
- Landau 符号 (Big-O / Little-o)：描述余项的渐近行为

## 参考

### 教材

- [Rudin. Principles of Mathematical Analysis. McGraw-Hill, 3rd edition, 1976. Chapter 5]
- [Apostol. Calculus. Wiley, 2nd edition, 1967. Chapter 7]

### 历史文献

- [Taylor. Methodus Incrementorum Directa et Inversa. 1715]

### 在线资源

- [Mathlib4 文档 - Taylor][https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/Taylor.html]

---

*最后更新：2026-04-15 | 版本：v1.0.0*
