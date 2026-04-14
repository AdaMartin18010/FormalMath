---
msc_primary: 00A99
processed_at: '2026-04-03'
title: 隐函数定理 (Implicit Function Theorem)
---
# 隐函数定理 (Implicit Function Theorem)

## Mathlib4 引用

```lean
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.FDeriv.Basic

namespace Analysis

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- 隐函数定理 -/
theorem implicitFunctionTheorem (f : E × F → G) (p₀ : E × F)
    (hf : ContDiff ℝ 1 f) (h₀ : f p₀ = 0)
    (hinv : IsInvertible (fderiv ℝ (fun y => f (p₀.1, y)) p₀.2)) :
    ∃ g : E → F, ContDiff ℝ 1 g ∧
      ∀ x, f (x, g x) = 0 ∧ g p₀.1 = p₀.2 := by
  -- 隐函数存在且连续可微
  sorry

end Analysis
```

## 数学背景

隐函数定理是多变量微积分的核心结果，由奥古斯丁-路易·柯西和后来的让-加斯东·达布等人发展。该定理解决了从方程 $F(x, y) = 0$ 中"解出" $y$ 作为 $x$ 的函数的问题，即使显式求解困难或不可能。这是流形理论和微分几何的基石，也是优化理论和经济学中比较静态分析的基础。

## 直观解释

隐函数定理告诉我们：**如果方程 $F(x, y) = 0$ 在某点处关于 $y$ 的"变化率"不为零，那么在该点附近，$y$ 可以表示为 $x$ 的函数**。想象曲面 $F(x, y) = 0$ 与水平面的交线，如果在某点处曲面不垂直于 $x$ 轴，那么该点附近交线可以看作函数图像 $y = g(x)$。

数学上，条件 $\frac{\partial F}{\partial y} \neq 0$（或更一般地，雅可比矩阵可逆）保证局部可以"解开"隐式关系。

## 形式化表述

设 $F: \mathbb{R}^{n+m} \to \mathbb{R}^m$ 是 $C^1$ 函数，$F(a, b) = 0$。若雅可比矩阵 $\frac{\partial F}{\partial y}(a, b)$ 可逆，则存在 $a$ 的邻域 $U$ 和唯一的 $C^1$ 函数 $g: U \to \mathbb{R}^m$ 使得：

- $g(a) = b$
- 对所有 $x \in U$，$F(x, g(x)) = 0$

此外，$g$ 的导数为：
$$Dg(x) = -\left(\frac{\partial F}{\partial y}\right)^{-1} \frac{\partial F}{\partial x}$$

## 证明思路

1. **构造辅助映射**：定义 $G(x, y) = (x, F(x, y))$
2. **逆函数定理**：证明 $DG(a, b)$ 可逆，应用逆函数定理
3. **提取隐函数**：从 $G^{-1}$ 的第二分量得到 $g$
4. **验证性质**：验证 $g$ 满足所有要求

核心在于将隐函数问题转化为显式的逆函数问题。

## 示例

### 示例 1：单位圆

考虑 $F(x, y) = x^2 + y^2 - 1 = 0$（单位圆）。

在点 $(0, 1)$：$\frac{\partial F}{\partial y} = 2y = 2 \neq 0$

隐函数存在：$y = \sqrt{1 - x^2}$（上半圆）

导数：$\frac{dy}{dx} = -\frac{F_x}{F_y} = -\frac{2x}{2y} = -\frac{x}{y}$

在点 $(1, 0)$：$\frac{\partial F}{\partial y} = 0$，隐函数定理不适用（确实，此处无法将 $y$ 表示为 $x$ 的函数）。

### 示例 2：经济均衡

设 $F(p, w) = D(p) - S(p, w) = 0$（需求等于供给）。

若 $\frac{\partial F}{\partial p} = D'(p) - S_p(p, w) \neq 0$，则存在价格函数 $p = g(w)$。

比较静态：$\frac{dp}{dw} = -\frac{-S_w}{D' - S_p} = \frac{S_w}{D' - S_p}$

可以分析外生冲击 $w$ 如何影响均衡价格 $p$。

### 示例 3：约束优化

在约束 $g(x, y) = 0$ 下最大化 $f(x, y)$。

拉格朗日条件给出：$\nabla f = \lambda \nabla g$

隐函数定理保证约束集是流形，可以使用拉格朗日乘子法。

## 应用

- **微分几何**：证明水平集是流形
- **经济学**：比较静态分析、一般均衡理论
- **优化理论**：约束优化的二阶条件
- **动力系统**：中心流形定理
- **控制理论**：系统线性化和反馈设计

## 相关概念

- 逆函数定理 (Inverse Function Theorem)：局部可逆性条件
- 秩定理 (Rank Theorem)：一般形式的隐函数定理
- 子流形 (Submanifold)：隐函数定义的曲面
- 拉格朗日乘子 (Lagrange Multipliers)：约束优化的工具
- 比较静态 (Comparative Statics)：经济学分析工具

## 参考

### 教材

- [Rudin. Principles of Mathematical Analysis. McGraw-Hill, 3rd edition, 1976. Chapter 9]
- [Spivak. Calculus on Manifolds. Benjamin, 1965. Chapter 2]

### 历史文献

- [Cauchy. Cours d'Analyse de l'École Royale Polytechnique. 1821]

### 在线资源

- [Mathlib4 文档 - Implicit][https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/Implicit.html](需更新)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
