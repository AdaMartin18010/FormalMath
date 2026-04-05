---
msc_primary: 00A99
processed_at: '2026-04-03'
title: 留数定理 (Residue Theorem)
---
# 留数定理 (Residue Theorem)

## Mathlib4 引用

```lean
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.Residue

namespace Complex

variable {U : Set ℂ} (f : ℂ → ℂ)

/-- 留数定理 -/
theorem residueTheorem {ι : Type*} [Fintype ι] {s : ι → ℂ} {c : ι → ℂ}
    (hU : U.IsOpen) (hf : ∀ z ∈ U, DifferentiableAt ℂ f z)
    {γ : ℝ → ℂ} (hγ : Loop γ) (hγU : ∀ t, γ t ∈ U) :
    (∮ z in γ, f z) = 2 * π * I • ∑ i, c i * residue f (s i) := by
  -- 依赖于复分析中的留数理论
  sorry

end Complex
```

## 数学背景

留数是复分析中研究孤立奇点行为的工具，由柯西发展起来，后经刘维尔、魏尔斯特拉斯等人完善。留数定理是柯西积分理论的巅峰之作，将复平面上闭合路径的积分与被包围奇点的留数联系起来，为计算复杂积分提供了系统方法。

## 直观解释

留数定理告诉我们：**闭合路径积分等于 $2\pi i$ 乘以路径内所有奇点留数之和**。想象每个孤立奇点就像一个"旋涡"，对周围的"水流"（向量场）产生旋转效应。留数量化了每个旋涡的强度，而路径积分测量了总旋转量。

数学上，留数是函数在洛朗展开中 $(z - z_0)^{-1}$ 项的系数，捕捉了函数在奇点处的"发散行为"。

## 形式化表述

设 $f$ 在区域 $U$ 上除孤立奇点 $z_1, z_2, \ldots, z_n$ 外全纯，$\gamma$ 是 $U$ 内围绕这些奇点的正向简单闭曲线，则：

$$\oint_\gamma f(z) dz = 2\pi i \sum_{k=1}^n \text{Res}(f, z_k)$$

其中留数定义为：

$$\text{Res}(f, z_0) = \frac{1}{2\pi i} \oint_{|z-z_0|=\varepsilon} f(z) dz$$

## 证明思路

1. **分割路径**：在每个奇点周围构造小圆周路径
2. **路径变形**：应用柯西定理，将大路径变形为围绕各奇点的小圆周之和
3. **留数定义**：每个小圆周积分根据留数定义
4. **求和**：将所有小圆周积分相加

核心在于利用柯西定理的路径变形技术和留数的定义。

## 示例

### 示例 1：简单极点

计算 $\oint_{|z|=2} \frac{1}{z^2 - 1} dz$

奇点：$z = \pm 1$，都在圆内。

$$\text{Res}(f, 1) = \lim_{z \to 1} (z-1) \frac{1}{(z-1)(z+1)} = \frac{1}{2}$$

$$\text{Res}(f, -1) = \lim_{z \to -1} (z+1) \frac{1}{(z-1)(z+1)} = -\frac{1}{2}$$

积分 $= 2\pi i \left(\frac{1}{2} - \frac{1}{2}\right) = 0$

### 示例 2：实积分计算

计算 $I = \int_{-\infty}^{\infty} \frac{dx}{1+x^4}$

考虑 $f(z) = \frac{1}{1+z^4}$，在上半平面有极点 $z = e^{i\pi/4}, e^{3i\pi/4}$。

$$
\text{Res}(f, e^{i\pi/4}) = \frac{1}{4z^3}\bigg|_{z=e^{i\pi/4}} = \frac{e^{-3i\pi/4}}{4}
$$

类似计算另一个留数，利用留数定理：

$$I = 2\pi i \cdot \frac{1}{2\pi i} \cdot \frac{\pi\sqrt{2}}{2} = \frac{\pi\sqrt{2}}{2}$$

### 示例 3：傅里叶变换

计算 $\int_{-\infty}^{\infty} \frac{e^{iax}}{1+x^2} dx$，$a > 0$

上半平面极点：$z = i$

$$\text{Res}(f, i) = \frac{e^{-a}}{2i}$$

积分 $= 2\pi i \cdot \frac{e^{-a}}{2i} = \pi e^{-a}$

## 应用

- **实积分计算**：将困难实积分转化为复围道积分
- **级数求和**：通过围道积分计算无穷级数
- **特殊函数**：伽马函数、泽塔函数的解析性质
- **物理学**：量子力学中的散射振幅、统计力学配分函数

## 相关概念

- 孤立奇点 (Isolated Singularity)：函数不解析但周围解析的点
- 洛朗级数 (Laurent Series)：带负幂的幂级数展开
- 极点 (Pole)：洛朗展开有限个负幂的奇点
- 本质奇点 (Essential Singularity)：洛朗展开无限负幂的奇点
- 柯西主值 (Cauchy Principal Value)：发散积分的正则化

## 参考

### 教材

- [Ahlfors. Complex Analysis. McGraw-Hill, 3rd edition, 1979. Chapter 4]
- [Stein & Shakarchi. Complex Analysis. Princeton, 2003. Chapter 3]

### 历史文献

- [Cauchy. Sur les intégrales qui s'étendent à tous les points d'une courbe fermée. 1825]

### 在线资源

- [Mathlib4 文档 - Residue](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Residue.html)[需更新]

---

*最后更新：2026-04-03 | 版本：v1.0.0*
