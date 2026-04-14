---
msc_primary: 00A99
processed_at: '2026-04-15'
title: Morera 定理 (Morera's Theorem)
---
# Morera 定理 (Morera's Theorem)

## Mathlib4 引用

```lean
import Mathlib.MeasureTheory.Integral.CircleIntegral

namespace ComplexAnalysis

/-- Morera 定理：若连续函数沿任意三角形围道的积分为零，则函数全纯 -/
theorem morera_theorem {f : ℂ → ℂ} (hf : Continuous f)
    (h : ∀ (a b c : ℂ), contourIntegral (trianglePath a b c) f = 0) :
    Differentiable ℂ f := by
  -- 构造原函数，利用 Newton-Leibniz 公式证明复可微
  sorry

end ComplexAnalysis
```

## 数学背景

Morera 定理是复分析中关于全纯函数判定的重要结果，由意大利数学家吉诺·莫雷拉（Gino Morera）于1886年证明。该定理可以看作是 Cauchy 积分定理的逆定理：Cauchy 定理断言全纯函数沿任何闭曲线的积分为零，而 Morera 定理则断言：如果一个连续函数沿任意三角形的积分为零，那么这个函数必定是全纯的。

## 直观解释

Morera 定理提供了一个判断函数是否全纯的实用标准。Cauchy 积分定理告诉我们：如果一个函数是复可微的（全纯的），那么它沿任何闭曲线的积分都为零。Morera 定理则将这个箭头反过来：如果你怀疑一个函数是否全纯，只需要检查它沿所有小三角形的积分是否都为零。如果这些积分都为零，那么这个函数就必定是全纯的。

## 形式化表述

设 $f$ 是定义在复平面上区域 $D$ 内的连续函数。若对 $D$ 内任意三角形 $\Delta$，有：

$$\oint_{{\partial \Delta}} f(z) \, dz = 0$$

则 $f$ 在 $D$ 内是全纯的（即复可微的）。

等价表述：

1. 若 $f$ 连续且沿任意闭折线的积分为零，则 $f$ 全纯
2. 若 $f$ 连续且局部存在原函数，则 $f$ 全纯

其中：

- 区域 $D$ 是指连通开集
- $\partial \Delta$ 表示三角形 $\Delta$ 的边界（正向定向）
- 该定理是 Cauchy-Goursat 定理的逆命题

## 证明思路

1. **构造原函数**：固定基点 $z_0 \in D$，定义 $F(z) = \int_{{\gamma_z}} f(\zeta) d\zeta$
2. **路径无关性**：由假设，沿三角形的积分为零，故 $F(z)$ 的值不依赖于路径的选择
3. **Newton-Leibniz 公式**：证明 $\frac{F(z+h) - F(z)}{h} \to f(z)$（当 $h \to 0$）
4. **全纯性结论**：$F' = f$，故 $F$ 全纯，从而 $f$（作为全纯函数的导数）也全纯

核心洞察在于局部积分条件蕴含了原函数的存在性，进而推出复可微性。

## 示例

### 示例 1：Weierstrass 收敛定理

设 $\{f_n\}$ 是一列全纯函数，在紧集上一致收敛到 $f$。由 Morera 定理，$f$ 沿任意三角形的积分是各 $f_n$ 积分极限，故为零，因此 $f$ 全纯。

### 示例 2：热核的解析延拓

考虑由积分定义的 Gamma 函数。利用 Morera 定理可以证明其在右半平面的全纯性。

### 示例 3：幂级数求和

设 $f(z) = \sum a_n z^n$ 的收敛半径为 $R > 0$。由于幂级数在收敛圆盘内可以逐项积分，由 Morera 定理知 $f$ 在收敛圆盘内全纯。

## 应用

- **复分析**：全纯函数的等价刻画和判定准则
- **偏微分方程**：调和函数的解析性和正则性理论
- **概率论**：特征函数的解析延拓和矩生成函数
- **数学物理**：散射理论和解析 S-矩阵的研究
- **算子理论**：全纯泛函演算和谱理论

## 相关概念

- Cauchy 积分定理 (Cauchy's Integral Theorem)：Morera 定理的正命题
- 全纯函数 (Holomorphic Function)：复可微函数
- 原函数 (Primitive/Antiderivative)：导数等于给定函数的函数
- Weierstrass 收敛定理：全纯函数一致极限的全纯性
- 星形区域 (Star-Shaped Domain)：存在一点使得区域内任意点都可通过直线段连接

## 参考

### 教材

- [L. Ahlfors. Complex Analysis. McGraw-Hill, 3rd edition, 1979. Chapter 4]
- [E. Stein, R. Shakarchi. Complex Analysis. Princeton, 2003. Chapter 2]

### 在线资源

- [Mathlib4 - Circle Integral](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/CircleIntegral.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*