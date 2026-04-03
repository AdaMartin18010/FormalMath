# 类数公式 (Class Number Formula)

## Mathlib4 引用

```lean
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.ZetaFunction

namespace ClassNumberFormula

variable {K : Type*} [Field K] [NumberField K]

/-- 解析类数公式 -/
theorem analytic_class_number_formula :
    Tendsto (fun s => (s - 1) * DedekindZeta K s) (𝓝 1) (𝓝 (2^r₁ * (2π)^r₂ * Regulator K * ClassNumber K / (TorsionOrder K * Real.sqrt |discriminant K|))) := by
  -- Dedekind zeta在s=1处的留数
  sorry

/-- Dirichlet类数公式（二次域）-/
theorem dirichlet_class_number_formula {d : ℤ} (hd : d < 0) (hd2 : d ≠ -1) (hd3 : d ≠ -3) [IsQuadraticField ℚ(√d)] :
    ClassNumber ℚ(√d) = w * √|d| / (2π) * L(1, χ_d) := by
  -- 虚二次域的特殊形式
  sorry

end ClassNumberFormula
```

## 数学背景

解析类数公式由Richard Dedekind在19世纪后期建立，对二次域由Dirichlet更早证明。该公式将数域的类数（理想类群的阶）与Dedekind zeta函数在 $s=1$ 处的留数联系起来，是代数数论中最深刻的结果之一。类数公式连接了算术（类数、单位群）与解析（zeta函数、L函数）两个世界，是Iwasawa理论和Birch-Swinnerton-Dyer猜想等现代数论研究的模板。

## 直观解释

类数公式告诉我们：**数域的"理想结构复杂度"可以用特殊的L函数值来计算**。

想象数域的整数环，元素可能有多种不同的素因子分解方式（类数 $> 1$）。类数公式说，这种"分解复杂性"可以通过一个解析函数（Dedekind zeta函数）在特定点的值来测量。这就像说，一个数论对象的内部结构可以通过一个看似不相关的分析对象来读取。

## 形式化表述

设 $K$ 是数域，$h_K$ 是类数，$R_K$ 是调节子，$w_K$ 是单位根个数。

**解析类数公式**：
$$\lim_{s \to 1} (s-1)\zeta_K(s) = \frac{2^{r_1}(2\pi)^{r_2} R_K h_K}{w_K \sqrt{|D_K|}}$$

其中：
- $r_1, r_2$：实嵌入和复嵌入对数
- $D_K$：判别式
- $\zeta_K(s) = \sum_{I \subseteq \mathcal{O}_K} N(I)^{-s}$（Dedekind zeta函数）

## 证明思路

1. **理想计数**：
   - 数理想按范数计数
   - 几何方法：Minkowski理论
   
2. **Zeta函数分解**：
   - $\zeta_K(s) = \sum_{[I] \in Cl_K} \zeta_{[I]}(s)$
   - 按理想类分解
   
3. **Epstein zeta函数**：
   - 每个理想类的zeta可解析延拓
   - $s=1$ 处的极点分析
   
4. **留数计算**：
   - 几何平均得到体积项
   - 调节子来自对数单位格

核心洞察是理想分布的几何与分析的联系。

## 示例

### 示例 1：有理数域

$K = \mathbb{Q}$：$h = 1$，$R = 1$（无真单位），$w = 2$。

$\lim_{s \to 1} (s-1)\zeta(s) = 1$（与公式一致）。

### 示例 2：高斯整数

$K = \mathbb{Q}(i)$：$h = 1$，$w = 4$。

$\zeta_{\mathbb{Q}(i)}(s) = \zeta(s)L(s, \chi_{-4})$。

### 示例 3：实二次域

$K = \mathbb{Q}(\sqrt{5})$：$h = 1$，调节子 $R = \log \frac{1+\sqrt{5}}{2}$。

公式给出基本单位与zeta值的关系。

## 应用

- **类数计算**：虚二次域的类数表
- **Iwasawa理论**：p进L函数
- **Stark猜想**：单位与L函数值
- **BSD猜想**：椭圆曲线的类比
- **Gross-Zagier公式**：Heegner点与导数

## 相关概念

- [Dedekind Zeta函数 (Dedekind Zeta Function)](./dedekind-zeta-function.md)：数域的zeta函数
- [调节子 (Regulator)](./regulator.md)：对数单位的行列式
- [理想类群 (Ideal Class Group)](./ideal-class-group.md)：理想模主理想
- [Minkowski理论 (Minkowski Theory)](./minkowski-theory.md)：格的几何
- [L函数 (L-function)](./l-function.md)：Dirichlet特征的特征和

## 参考

### 教材

- [Neukirch. Algebraic Number Theory. Springer, 1999. Chapter 7]
- [Washington. Introduction to Cyclotomic Fields. Springer, 1982. Chapter 4]

### 在线资源

- [Mathlib4 文档 - ClassNumber](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/NumberField/ClassNumber.html)
- [Wikipedia - Class Number Formula](https://en.wikipedia.org/wiki/Class_number_formula)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
