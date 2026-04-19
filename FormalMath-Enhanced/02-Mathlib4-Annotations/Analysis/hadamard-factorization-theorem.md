---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: Hadamard 因子分解定理 (Hadamard Factorization Theorem)
---
# Hadamard 因子分解定理 (Hadamard Factorization Theorem)

## Mathlib4 引用

```lean
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace ComplexAnalysis

variable {f : ℂ → ℂ} (hf : Differentiable ℂ f)

/-- Hadamard 因子分解定理：有限阶整函数可表示为指数与 Weierstrass 初等因子的乘积 -/
theorem hadamard_factorization {p : ℕ} (horder : ∀ ε > 0, ∃ R, ∀ |z| > R, ‖f z‖ ≤ Real.exp (|z|^(p+ε))) :
    ∃ (a : ℂ) (n : ℕ) (g : ℂ → ℂ),
      Differentiable ℂ g ∧ ∀ z, f z = Real.exp (a + g z) * z^n *
        ∏' k, (E (degreeForWeierstrass f) (z / zeroOf f k)) := by
  -- 利用 Jensen 公式和有限阶条件控制零点的分布，然后构造因子分解
  sorry

end ComplexAnalysis
```

## 数学背景

Hadamard 因子分解定理是复分析中关于整函数结构的深刻结果，由法国数学家雅克·阿达马（Jacques Hadamard）于1893年证明。该定理断言：任何有限阶的整函数都可以唯一地表示为一个多项式、一个指数函数和 Weierstrass 初等因子的乘积。这一定理是整函数理论的里程碑，阿达马本人正是利用这一定理给出了素数定理的第一个完整证明。

## 直观解释

Hadamard 因子分解定理为整函数提供了一个类似于整数的素因子分解。在整数中，任何正整数都可以唯一分解为素数的乘积。对于整函数，素因子就是它的零点——每个零点对应一个 Weierstrass 初等因子。Hadamard 定理告诉我们：如果一个整函数的增长不会太快（有限阶），那么它的结构就完全由其零点和额外的指数多项式决定。

## 形式化表述

设 $f$ 是一个有限阶 $\rho$ 的整函数，$\{a_n\}$ 是 $f$ 的非零零点序列（计重数），则 $f$ 可以表示为：

$$f(z) = z^m e^{{Q(z)}} \prod_{{n=1}}^\infty E_p\left(\frac{z}{a_n}\right)$$

其中：

- $m$ 是 $f$ 在 $z = 0$ 处的零点阶数
- $Q(z)$ 是一个次数不超过 $p$ 的多项式
- $p = \lfloor \rho \rfloor$（阶的整数部分）
- $E_p(u) = (1 - u) \exp\left(u + \frac{u^2}{2} + \cdots + \frac{u^p}{p}\right)$ 是 Weierstrass 初等因子
- 无穷乘积在紧集上一致收敛

有限阶的定义：存在 $\rho \geq 0$ 使得对所有 $\varepsilon > 0$，$|f(z)| \leq \exp(|z|^{{\rho + \varepsilon}})$ 对充分大的 $|z|$ 成立。

## 证明思路

1. **Jensen 公式**：将 $f$ 的零点分布与其对数增长的平均值联系起来
2. **零点计数**：有限阶条件限制了零点的密度
3. **Weierstrass 乘积**：构造以 $\{a_n\}$ 为零点的 Weierstrass 乘积 $P(z)$
4. **剩余因子**：证明 $f(z)/P(z)$ 是无零点的有限阶整函数，故可写成 $e^{{Q(z)}}$ 的形式

核心洞察在于有限阶条件同时控制了零点的分布和无零点部分的指数增长。

## 示例

### 示例 1：正弦函数

$\sin(\pi z)$ 是阶为 1 的整函数，其 Hadamard 分解为：
$$\sin(\pi z) = \pi z \prod_{{n \neq 0}} \left(1 - \frac{z}{n}\right) e^{{z/n}}$$
这是 Euler 著名的正弦乘积公式的严格形式。

### 示例 2：Gamma 函数的倒数

$1/\Gamma(z)$ 是阶为 1 的整函数，其 Hadamard 分解给出了 Weierstrass 的 Gamma 函数定义。

### 示例 3：Riemann ξ 函数

Hadamard 本人利用该定理证明了 Riemann ξ 函数的因子分解，这是证明素数定理的关键步骤。

## 应用

- **解析数论**：素数定理和 Riemann 假设的研究
- **算子理论**：整函数与线性算子谱理论的联系
- **微分方程**：整函数解的零点分布和增长性分析
- **信号处理**：带限函数和采样定理的复分析基础
- **统计力学**：配分函数的解析结构和相变理论

## 相关概念

- 整函数 (Entire Function)：在整个复平面上全纯的函数
- Weierstrass 初等因子 (Weierstrass Primary Factor)：构造整函数零点的标准积木
- 有限阶 (Finite Order)：增长受 $|z|^\rho$ 控制的整函数
- Jensen 公式 (Jensen's Formula)：全纯函数零点与增长的关系
- Riemann ξ 函数 (Riemann Xi Function)：Hadamard 定理的经典应用

## 参考

### 教材

- [E. Stein, R. Shakarchi. Complex Analysis. Princeton, 2003. Chapter 5]
- [A. I. Markushevich. Theory of Functions of a Complex Variable. Chelsea, 1985. Chapter 7]

### 在线资源

- [Mathlib4 - Complex Log](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Complex/Log.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*
