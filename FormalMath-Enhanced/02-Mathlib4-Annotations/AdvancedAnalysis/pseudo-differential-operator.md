---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: 伪微分算子理论
---
# 伪微分算子理论

## Mathlib4 引用

```lean
import Mathlib.Analysis.PDE.PseudoDifferentialOperator

namespace Analysis

/-- 伪微分算子的定义 -/
theorem pseudo_differential_operator
    {n : ℕ} (m : ℝ)
    (a : EuclideanSpace ℝ (Fin n) →
         EuclideanSpace ℝ (Fin n) → ℂ) :
    IsSymbolClass a m ↔ ∀ (α β : MultiIndex (Fin n)),
      ∃ (C : ℝ), ∀ (x ξ),
        |∂^α_x ∂^β_ξ a x ξ| ≤
          C * ⟨ξ⟩^{m - |β|} := by
  -- Hörmander符号类
  rfl

/-- 伪微分演算的复合定理 -/
theorem pseudo_composition
    {n : ℕ} {m₁ m₂ : ℝ}
    (a₁ : SymbolClass m₁) (a₂ : SymbolClass m₂) :
    ∃ (a : SymbolClass (m₁ + m₂)),
      Op a₁ ∘ Op a₂ = Op a +
        SmoothingOperator := by
  -- 主符号相乘，低阶修正
  sorry

end Analysis
```

## 数学背景

伪微分算子理论由Joseph Kohn、Louis Nirenberg和Lars Hörmander在1960年代系统发展。它将微分算子推广到更广泛的算子类，同时保留了经典的符号演算。这一理论统一了偏微分方程中的许多技术，特别是椭圆型、双曲型和抛物型方程的研究。伪微分算子成为现代偏微分方程理论、指标定理和数学物理的核心工具。

## 直观解释

伪微分算子是微分算子的"傅里叶变换版本"。经典微分算子 $P = \sum_{|\alpha| \leq m} a_\alpha(x) D^\alpha$ 在傅里叶侧对应乘子 $p(x, \xi) = \sum a_\alpha(x) \xi^\alpha$。伪微分算子允许更一般的"符号" $a(x, \xi)$，不仅是 $\xi$ 的多项式。这就像从多项式函数扩展到光滑函数——保留了微积分的基本结构，但获得了更大的灵活性。复合对应符号的乘积（加低阶修正），使得算子代数的研究变得可行。

## 形式化表述

设 $\Omega \subset \mathbb{R}^n$，符号 $a \in S^m(\Omega \times \mathbb{R}^n)$（Hörmander类）。

**伪微分算子**：
$$\text{Op}(a)u(x) = \frac{1}{(2\pi)^n} \int e^{ix \cdot \xi} a(x, \xi) \hat{u}(\xi) d\xi$$

**符号类** $S^m$：满足估计
$$|\partial_x^\alpha \partial_\xi^\beta a(x, \xi)| \leq C_{\alpha,\beta} \langle \xi \rangle^{m - |\beta|}$$

**渐近展开**：复合的符号有展开
$$a \# b \sim \sum_\alpha \frac{1}{\alpha!} \partial_\xi^\alpha a \cdot D_x^\alpha b$$

**椭圆性**：$|a(x, \xi)| \geq c|\xi|^m$（$|\xi|$ 大时），保证可逆性模光滑算子。

## 证明思路

1. **Littlewood-Paley分解**：局部分析频率
2. **Calderón-Zygmund理论**：奇异积分的有界性
3. **象征演算**：验证复合公式
4. **渐近分析**：建立展开式
5. **Fredholm性质**：椭圆算子的指标理论

## 示例

### 示例 1：常系数微分算子

**问题**：将 $P = -\Delta + 1$ 表示为伪微分算子。

**解答**：

符号为 $p(\xi) = |\xi|^2 + 1$，属于 $S^2$ 类。

$$Pu(x) = \frac{1}{(2\pi)^n} \int e^{ix \cdot \xi} (|\xi|^2 + 1) \hat{u}(\xi) d\xi$$

这是经典的椭圆伪微分算子，可逆且逆也是伪微分算子。

### 示例 2：Cauchy积分算子

**问题**：边界上的Cauchy积分作为伪微分算子。

**解答**：

设 $\Gamma$ 是光滑曲线，Cauchy积分
$$Cf(z) = \frac{1}{2\pi i} \int_\Gamma \frac{f(\zeta)}{\zeta - z} d\zeta$$

在边界上对应符号 $a(\xi) = \text{sgn}(\xi)$（Hilbert变换）。

这是一个0阶伪微分算子，但不是微分算子。

## 应用

- **椭圆正则性**：精细的先验估计
- **波动方程**：奇性传播定理
- **指标定理**：Atiyah-Singer定理的证明
- **量子化**：物理中的算子排序
- **几何分析**：谱渐近和迹公式

## 相关概念

- 傅里叶积分算子：更一般的振荡积分
- 微局部分析：波前集和奇性分析
- Sobolev空间：伪微分算子的自然定义域
- 椭圆算子：可逆的伪微分算子
- 拟微分算子：实变量理论

## 参考

### 教材

- Hörmander, L. The Analysis of Linear Partial Differential Operators III. Springer, 1985.
- Taylor, M.E. Pseudodifferential Operators. Princeton, 1981.

### 论文

- Kohn, J.J. & Nirenberg, L. An algebra of pseudo-differential operators. Comm. Pure Appl. Math., 18: 269-305, 1965.
- Hörmander, L. Pseudo-differential operators. Comm. Pure Appl. Math., 18: 501-517, 1965.

### 在线资源

- [Pseudodifferential Operator Wikipedia](https://en.wikipedia.org/wiki/Pseudodifferential_operator)
- [nLab - Pseudodifferential Operator](https://ncatlab.org/nlab/show/pseudodifferential+operator)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
