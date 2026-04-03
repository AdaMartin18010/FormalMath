# 微分中值定理 (Mean Value Theorem)

## Mathlib4 引用

```lean
import Mathlib.Calculus.MeanValue

namespace Real

/-- 拉格朗日中值定理 -/
theorem exists_deriv_eq_slope (f : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hf' : DifferentiableOn ℝ f (Ioo a b)) :
    ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) := by
  apply exists_ratio_hasDerivAt_eq_ratio_slope f
  · apply continuousOn_id
  · apply continuousOn_const
  · exact hf
  · exact fun x hx => (hf' x hx).hasDerivAt (Ioo_mem_nhds hx)
  · exact hab

end Real
```

## 数学背景

微分中值定理是微积分基本定理之一，由约瑟夫·拉格朗日（Joseph-Louis Lagrange）于1797年正式发表。该定理建立了函数在区间上的平均变化率与某点瞬时变化率之间的精确联系，是连接微分学与积分学的桥梁，也是泰勒展开和级数理论的基石。

## 直观解释

微分中值定理告诉我们：**在一条光滑曲线上，至少存在一点使得该点的切线与连接端点的割线平行**。想象汽车在高速公路上行驶，如果平均速度是 60 km/h，那么必定存在某个时刻瞬时速度正好是 60 km/h。

数学上，割线斜率 $\frac{f(b) - f(a)}{b - a}$ 表示平均变化率，而定理保证存在点 $c$ 使得 $f'(c)$ 等于这个平均值。

## 形式化表述

设函数 $f$ 在闭区间 $[a, b]$ 上连续，在开区间 $(a, b)$ 上可导，则存在 $c \in (a, b)$ 使得：

$$f'(c) = \frac{f(b) - f(a)}{b - a}$$

等价表述（罗尔定理形式）：若 $f(a) = f(b)$，则存在 $c \in (a, b)$ 使 $f'(c) = 0$。

## 证明思路

1. **构造辅助函数**：设 $g(x) = f(x) - f(a) - \frac{f(b) - f(a)}{b - a}(x - a)$
2. **验证条件**：$g(a) = g(b) = 0$，$g$ 满足罗尔定理条件
3. **应用罗尔定理**：存在 $c \in (a, b)$ 使 $g'(c) = 0$
4. **结论**：$g'(c) = f'(c) - \frac{f(b) - f(a)}{b - a} = 0$

核心在于通过辅助函数将问题转化为罗尔定理。

## 示例

### 示例 1：验证定理

设 $f(x) = x^2$，在 $[0, 2]$ 上。

平均变化率：$\frac{f(2) - f(0)}{2 - 0} = \frac{4 - 0}{2} = 2$

$f'(x) = 2x$，令 $f'(c) = 2$，得 $c = 1 \in (0, 2)$。

验证：$f'(1) = 2$，等于平均变化率。

### 示例 2：估计误差

估计 $\sqrt{101}$，已知 $\sqrt{100} = 10$。

对 $f(x) = \sqrt{x}$ 在 $[100, 101]$ 应用中值定理：

$$\frac{\sqrt{101} - 10}{1} = \frac{1}{2\sqrt{c}}$$

其中 $100 < c < 101$，故 $10 < \sqrt{c} < \sqrt{101} < 10.05$

$$\frac{1}{2 \cdot 10.05} < \sqrt{101} - 10 < \frac{1}{2 \cdot 10}$$

$$10.04975 < \sqrt{101} < 10.05$$

### 示例 3：证明不等式

证明：$\ln(1 + x) < x$ 对 $x > 0$。

对 $f(t) = \ln(1 + t)$ 在 $[0, x]$ 应用中值定理：

$$\frac{\ln(1 + x) - 0}{x - 0} = \frac{1}{1 + c}$$

其中 $0 < c < x$，故 $\frac{1}{1 + c} < 1$

因此 $\ln(1 + x) = \frac{x}{1 + c} < x$。

## 应用

- **函数单调性**：导数符号判断单调性
- **泰勒展开**：拉格朗日余项的推导
- **误差估计**：数值方法的误差分析
- **洛必达法则**：不定式极限的计算
- **优化理论**：极值点的必要条件

## 相关概念

- [罗尔定理 (Rolle's Theorem)](./rolle-theorem.md)：端点值相等的中值定理特例
- [柯西中值定理 (Cauchy Mean Value Theorem)](./cauchy-mean-value-theorem.md)：两个函数版本的中值定理
- [泰勒定理 (Taylor's Theorem)](./taylor-theorem.md)：高阶中值定理
- [达布定理 (Darboux's Theorem)](./darboux-theorem.md)：导数的介值性质
- [利普希茨连续性 (Lipschitz Continuity)](./lipschitz-continuity.md)：由导数有界性导出

## 参考

### 教材

- [Rudin. Principles of Mathematical Analysis. McGraw-Hill, 3rd edition, 1976. Chapter 5]
- [Apostol. Calculus. Wiley, 2nd edition, 1967. Chapter 4]

### 历史文献

- [Lagrange. Théorie des fonctions analytiques. 1797]

### 在线资源

- [Mathlib4 文档 - MeanValue](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Calculus/MeanValue.html)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
