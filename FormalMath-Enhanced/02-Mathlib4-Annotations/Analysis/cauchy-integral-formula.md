# 柯西积分公式 (Cauchy's Integral Formula)

## Mathlib4 引用

```lean
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.CauchyIntegral

namespace Complex

variable {U : Set ℂ} (f : ℂ → ℂ) (z₀ : ℂ)

/-- 柯西积分公式 -/
theorem cauchyIntegralFormula {r : ℝ} (hr : 0 < r) (hU : U.IsOpen)
    (hf : DifferentiableOn ℂ f U) (hz : closedBall z₀ r ⊆ U) :
    (2 * π * I)⁻¹ • ∮ z in C(z₀, r), f z / (z - z₀) = f z₀ := by
  simpa using integral_sub_inv_of_differentiable_on_off_countable
    countable_empty hf (by simpa) (by simpa) (by simpa) (by simpa)

end Complex
```

## 数学背景

柯西积分公式由法国数学家奥古斯丁-路易·柯西（Augustin-Louis Cauchy）于1831年提出，是复分析的基石。该公式揭示了全纯函数值与其边界值之间的深刻联系，展示了复分析与实分析的显著差异。这一发现开启了复变函数理论的现代发展。

## 直观解释

柯西积分公式告诉我们：**全纯函数在区域内部的值完全由其在边界上的值决定**。想象一个平静的池塘，水面的波纹（边界值）完全决定了水下每一点的振动状态（内部值）。

公式中的核心思想是：点 $z_0$ 处的函数值可以表示为边界上函数值的加权平均，权重由 $(z - z_0)^{-1}$ 决定。这反映了复平面上全纯函数的"刚性"——局部信息决定整体行为。

## 形式化表述

设 $f$ 在区域 $U$ 上全纯，$\gamma$ 是 $U$ 内围绕 $z_0$ 的简单闭曲线，则：

$$f(z_0) = \frac{1}{2\pi i} \oint_\gamma \frac{f(z)}{z - z_0} dz$$

更一般地，对 $n$ 阶导数：

$$f^{(n)}(z_0) = \frac{n!}{2\pi i} \oint_\gamma \frac{f(z)}{(z - z_0)^{n+1}} dz$$

## 证明思路

1. **构造辅助函数**：考虑 $g(z) = \frac{f(z) - f(z_0)}{z - z_0}$
2. **可去奇点**：证明 $g(z)$ 在 $z_0$ 处有可去奇点
3. **柯西定理应用**：应用柯西积分定理，沿小圆收缩
4. **极限计算**：计算 $\oint \frac{1}{z - z_0} dz = 2\pi i$

关键在于利用全纯性证明辅助函数无奇点，从而可以连续延拓。

## 示例

### 示例 1：计算圆周积分

计算 $\oint_{|z|=2} \frac{e^z}{z-1} dz$

$f(z) = e^z$ 全纯，$z_0 = 1$ 在圆内。

由柯西积分公式：
$$\oint_{|z|=2} \frac{e^z}{z-1} dz = 2\pi i \cdot e^1 = 2\pi i e$$

### 示例 2：高阶导数公式

计算 $\oint_{|z|=1} \frac{\cos z}{z^3} dz$

这里 $f(z) = \cos z$，$z_0 = 0$，$n = 2$。

$f''(z) = -\cos z$，$f''(0) = -1$

$$\oint_{|z|=1} \frac{\cos z}{z^3} dz = \frac{2\pi i}{2!} \cdot f''(0) = -\pi i$$

### 示例 3：证明刘维尔定理

设 $f$ 是有界整函数，$|f(z)| \leq M$。

对任意 $z_0$ 和半径 $R$：
$$|f'(z_0)| = \left|\frac{1}{2\pi i} \oint_{|z-z_0|=R} \frac{f(z)}{(z-z_0)^2} dz\right| \leq \frac{M}{R}$$

令 $R \to \infty$，得 $f'(z_0) = 0$，故 $f$ 为常数。

## 应用

- **留数计算**：复积分的系统性计算方法
- **级数展开**：洛朗级数和泰勒级数的理论基础
- **实积分计算**：通过围道积分计算实变积分
- **物理学**：电磁学中的势理论和流体力学

## 相关概念

- [全纯函数 (Holomorphic Function)](./holomorphic-function.md)：复可微函数
- [柯西积分定理 (Cauchy's Integral Theorem)](./cauchy-integral-theorem.md)：闭路积分为零
- [留数定理 (Residue Theorem)](./residue-theorem.md)：极点处留数的应用
- [刘维尔定理 (Liouville's Theorem)](./liouville-theorem.md)：有界整函数必为常数
- [最大模原理 (Maximum Modulus Principle)](./maximum-modulus-principle.md)：全纯函数的模在内部无极大值

## 参考

### 教材

- [Ahlfors. Complex Analysis. McGraw-Hill, 3rd edition, 1979. Chapter 4]
- [Stein & Shakarchi. Complex Analysis. Princeton, 2003. Chapter 2]

### 历史文献

- [Cauchy. Mémoire sur les intégrales définies. 1814]

### 在线资源

- [Mathlib4 文档 - CauchyIntegral](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/CauchyIntegral.html)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
