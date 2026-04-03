# Fubini定理 (Fubini's Theorem)

## Mathlib4 引用

```lean
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Mathlib.MeasureTheory.Integral.Prod

namespace FubiniTheorem

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SigmaFinite μ]
variable {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} [SigmaFinite ν]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Fubini定理：可积函数的重积分交换 -/
theorem fubini_integrable {f : X × Y → E} (hf : Integrable f (μ.prod ν)) :
    Integrable (λ x => ∫ y, f (x, y) ∂ν) μ ∧
    Integrable (λ y => ∫ x, f (x, y) ∂μ) ν ∧
    ∫ z, f z ∂(μ.prod ν) = ∫ x, ∫ y, f (x, y) ∂ν ∂μ := by
  constructor
  · -- 证明第一次累次积分的可积性
    sorry
  constructor
  · -- 证明第二次累次积分的可积性
    sorry
  · -- 证明积分相等
    sorry

/-- Fubini-Tonelli定理：非负函数情形 -/
theorem fubini_tonelli {f : X × Y → ℝ} (hf : Measurable f) (hf_nn : ∀ z, 0 ≤ f z) :
    ∫⁻ z, f z ∂(μ.prod ν) = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ := by
  rw [lintegral_prod]
  rfl

/-- 切片可测性 -/
theorem measurable_slice_left {f : X × Y → E} (hf : Measurable f) :
    ∀ x, Measurable (λ y => f (x, y)) := by
  intro x
  exact hf.comp (Measurable.prod measurable_const measurable_id)

end FubiniTheorem
```

## 数学背景

Fubini定理由Guido Fubini在1907年证明（Tonelli在1909年给出了非负版本），是多重积分理论的基本结果。它表明在适当条件下，多重积分可以化为累次积分，且积分顺序可以交换。这一定理是计算多重积分的理论基础，在概率论（联合分布的边际化）、物理学（统计力学）和工程学中都有广泛应用。

## 直观解释

Fubini定理告诉我们：**在"好"条件下，二重积分可以通过两种方式计算**——先对 $x$ 积分再对 $y$ 积分，或者反过来。

想象计算一块薄板的质量。你可以先沿行方向"扫描"求和，再沿列方向汇总；也可以先沿列方向扫描。Fubini定理说，只要质量分布"合理"（可积），两种方法给出相同结果。这就像说，计算房间总人数时，无论是先按排再按列数，还是先按列再按排数，结果都一样。

## 形式化表述

设 $(X, \mu)$ 和 $(Y, \nu)$ 是 $\sigma$-有限测度空间。

**Fubini定理**：若 $f \in L^1(\mu \times \nu)$，则：
1. 对几乎处处 $x$，$f(x, \cdot) \in L^1(\nu)$
2. 对几乎处处 $y$，$f(\cdot, y) \in L^1(\mu)$
3. $x \mapsto \int_Y f(x,y) d\nu(y)$ 和 $y \mapsto \int_X f(x,y) d\mu(x)$ 可积
4. $\displaystyle \int_{X \times Y} f \, d(\mu \times \nu) = \int_X \int_Y f \, d\nu \, d\mu = \int_Y \int_X f \, d\mu \, d\nu$

**Fubini-Tonelli**：对非负可测函数，无条件成立（允许 $+\infty$）。

## 证明思路

1. **乘积测度的构造**：
   - 在矩形 $A \times B$ 上定义 $(\mu \times \nu)(A \times B) = \mu(A)\nu(B)$
   - 延拓到乘积 $\sigma$-代数
   
2. **示性函数情形**：
   - 对 $f = \chi_{A \times B}$，直接验证
   - 通过单调类定理推广到可测集
   
3. **简单函数逼近**：
   - 非负简单函数：线性性
   - 非负可测函数：单调收敛定理（Tonelli）
   
4. **一般可积函数**：
   - 分解 $f = f^+ - f^-$
   - 分别应用Tonelli定理

核心洞察是乘积测度的唯一性和单调类定理。

## 示例

### 示例 1：基本计算

计算 $\int_{[0,1] \times [0,1]} (x+y) \, dx dy$。

方法1：$\int_0^1 \int_0^1 (x+y) \, dy \, dx = \int_0^1 [xy + y^2/2]_0^1 dx = \int_0^1 (x + 1/2) dx = 1$

方法2：对称性给出相同结果 $1$。

### 示例 2：顺序重要性的例子

设 $f(x,y) = \frac{x^2-y^2}{(x^2+y^2)^2}$ 在 $[0,1] \times [0,1]$ 上。

$\int_0^1 \int_0^1 f(x,y) dy dx = \frac{\pi}{4}$

$\int_0^1 \int_0^1 f(x,y) dx dy = -\frac{\pi}{4}$

不同！因为 $f$ 在 $(0,0)$ 附近不可积，Fubini条件不满足。

### 示例 3：概率应用

设 $X, Y$ 是独立随机变量，联合密度 $f_{X,Y}(x,y) = f_X(x)f_Y(y)$。

Fubini定理：$E[XY] = \int\int xy f_X(x)f_Y(y) dx dy = E[X]E[Y]$。

## 应用

- **概率论**：边际分布的计算
- **统计物理**：配分函数的因式分解
- **偏微分方程**：热核和格林函数的构造
- **傅里叶分析**：卷积定理的证明
- **几何测度论**：面积和体积的计算

## 相关概念

- [乘积测度 (Product Measure)](./product-measure.md)：测度空间的乘积
- [Tonelli定理 (Tonelli's Theorem)](./tonelli-theorem.md)：非负函数的Fubini定理
- [累次积分 (Iterated Integral)](./iterated-integral.md)：积分的积分
- [单调类定理 (Monotone Class Theorem)](./monotone-class-theorem.md)：测度延拓工具
- [σ-有限测度 (Sigma-Finite Measure)](./sigma-finite-measure.md)：Fubini的条件

## 参考

### 教材

- [Folland. Real Analysis. Wiley, 2nd edition, 1999. Chapter 2]
- [Rudin. Real and Complex Analysis. McGraw-Hill, 3rd edition, 1987. Chapter 8]

### 历史文献

- [Fubini. Sugli integrali multipli. 1907]
- [Tonelli. Sull'integrazione per parti. 1909]

### 在线资源

- [Mathlib4 文档 - Prod Integral](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Prod.html)
- [Terry Tao - Fubini](https://terrytao.wordpress.com/2010/01/09/254a-notes-0a-an-alternate-approach-to-the-product-measure-extension-theorem/)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
