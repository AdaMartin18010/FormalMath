---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: 换元定理 (Change of Variables Theorem)
---
# 换元定理 (Change of Variables Theorem)

## Mathlib4 引用

```lean
import Mathlib.MeasureTheory.Integral.SetIntegral

namespace MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]

/-- 积分的换元定理：在微分同胚下，积分可按 Jacobian 行列式变换 -/
theorem integral_change_of_variables {f : E → F} {g : E → F}
    (hf : Measurable f) (hg : ContDiff ℝ 1 g) (hG : ∀ x, Invertible (fderiv ℝ g x))
    (s : Set E) (hs : MeasurableSet s) :
    ∫ x in g '' s, f x = ∫ x in s, f (g x) * |det (fderiv ℝ g x)| := by
  -- 利用 Radon-Nikodym 导数和可微映射下的测度变换证明
  sorry

end MeasureTheory
```

## 数学背景

积分的换元定理（也称为变量替换公式）是数学分析中的核心结果之一，它将一维黎曼积分中的 u-替换推广到高维 Lebesgue 积分。该定理断言：在一个光滑的可逆变换（微分同胚）下，函数的积分可以通过变换的 Jacobian 行列式的绝对值来进行调整。

## 直观解释

换元定理解释了为什么当我们在不同的坐标系中计算积分时，需要乘以一个体积膨胀因子。想象你要计算一块橡皮泥的质量。如果你把橡皮泥拉伸或压缩，那么在新坐标系中，每个小方块可能不再是单位体积。Jacobian 行列式的绝对值就精确地量化了这种局部体积的变化。

## 形式化表述

设 $U \subseteq \mathbb{R}^n$ 是开集，$\varphi: U \to \mathbb{R}^n$ 是 $C^1$ 微分同胚，$f$ 是 $\varphi(U)$ 上的可积函数，则：

$$\int_{{\varphi(U)}} f(y) \, dy = \int_U f(\varphi(x)) \cdot |\det D\varphi(x)| \, dx$$

其中 $D\varphi(x)$ 是 $\varphi$ 在 $x$ 处的 Jacobian 矩阵。

一维特例（$n = 1$）：若 $\varphi: [a, b] \to [\varphi(a), \varphi(b)]$ 是单调可微函数，则：

$$\int_{{\varphi(a)}}^{{\varphi(b)}} f(y) \, dy = \int_a^b f(\varphi(x)) \varphi'(x) \, dx$$

## 证明思路

1. **简单函数逼近**：首先对指示函数证明公式，此时换元定理等价于可微映射下的体积变换公式
2. **线性情形**：若 $\varphi$ 是线性变换，则公式可由 Lebesgue 测度的平移不变性和伸缩性质直接得到
3. **局部线性化**：对一般 $C^1$ 映射，在每个点附近用切映射近似，误差在极限下消失
4. **控制收敛**：利用简单函数的逼近和控制收敛定理，将结果推广到一般可积函数

核心洞察在于可微映射在无穷小尺度上近似为线性映射，而线性映射的体积变换由行列式给出。

## 示例

### 示例 1：极坐标

在 $\mathbb{R}^2$ 中取 $x = r\cos\theta$, $y = r\sin\theta$，Jacobian 行列式为 $r$。因此重积分变为 $\iint f(r\cos\theta, r\sin\theta) \cdot r \, dr \, d\theta$。

### 示例 2：球坐标

在 $\mathbb{R}^3$ 中，球坐标的 Jacobian 行列式为 $r^2 \sin\phi$。

### 示例 3：概率密度变换

设随机变量 $Y = \varphi(X)$，其中 $\varphi$ 可逆可微。则 $Y$ 的密度为 $f_Y(y) = f_X(\varphi^{{-1}}(y)) \cdot |\det D\varphi^{{-1}}(y)|$。

## 应用

- **多元微积分**：重积分的极坐标、柱坐标和球坐标计算
- **概率论**：随机变量变换后的概率密度函数推导
- **微分几何**：流形上的积分和体积形式的变换
- **物理学**：广义坐标系中的守恒量和作用量计算
- **统计学**：最大似然估计中的参数变换和 Fisher 信息矩阵

## 相关概念

- Jacobian 行列式 (Jacobian Determinant)：坐标变换下的局部体积缩放因子
- 微分同胚 (Diffeomorphism)：光滑可逆且逆也光滑的映射
- Lebesgue 测度 (Lebesgue Measure)：$\mathbb{R}^n$ 上的标准体积测度
- 可测函数 (Measurable Function)：可以进行 Lebesgue 积分的函数
- 控制收敛定理 (Dominated Convergence Theorem)：交换积分与极限的工具

## 参考

### 教材

- [W. Rudin. Real and Complex Analysis. McGraw-Hill, 3rd edition, 1987. Chapter 7]
- [T. Tao. An Introduction to Measure Theory. AMS, 2011. Chapter 1]

### 在线资源

- [Mathlib4 - Set Integral](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/SetIntegral.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*
