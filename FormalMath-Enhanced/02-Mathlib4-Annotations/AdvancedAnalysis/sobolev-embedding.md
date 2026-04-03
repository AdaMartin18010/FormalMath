---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# Sobolev嵌入定理

## Mathlib4 引用

```lean
import Mathlib.Analysis.SobolevSpace

namespace Analysis

/-- Sobolev嵌入定理 -/
theorem sobolev_embedding 
    {n : ℕ} {p : ℝ} (hp : 1 ≤ p) {k : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    (s : ℕ) (hs : s > n / p) :
    ∃ (C : ℝ), ∀ (u : SobolevSpace k p Ω),
      ‖u‖_{C^s} ≤ C * ‖u‖_{W^{k,p}} := by
  -- Sobolev函数连续嵌入到Hölder空间
  sorry

/-- Rellich-Kondrachov紧嵌入 -/
theorem rellich_kondrachov 
    {n : ℕ} {p : ℝ} (hp : 1 ≤ p) {k : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin n))} 
    (hΩ : IsOpen Ω) (hΩ_compact : IsCompact (closure Ω))
    (q : ℝ) (hq : 1 ≤ q) (hqp : q < p) :
    IsCompact (SobolevSpace k p Ω →ₗ[ℝ] LpSpace q Ω) := by
  -- 有界区域上Sobolev嵌入是紧算子
  sorry

end Analysis
```

## 数学背景

Sobolev嵌入定理由Sergei Sobolev在1930年代证明，是偏微分方程理论和泛函分析中的核心结果。它建立了Sobolev空间（带有弱导数的L^p空间）与连续函数空间或Hölder空间之间的关系。这一定理使得我们可以在更"好"的函数空间中求解PDE，并研究解的正则性。Sobolev嵌入是椭圆型偏微分方程理论的基础工具。

## 直观解释

Sobolev嵌入定理告诉我们：如果函数在平均意义下有"足够多"的导数（在Sobolev空间中），那么它实际上是经典意义下的光滑函数。这就像如果一个人有足够的"技能点"（弱导数），那么他的"实际表现"（连续性和光滑性）也会很好。定理的关键是维数、可积性和光滑性之间的精确关系——在n维空间中，需要k > n/p个导数才能保证连续性。

## 形式化表述

设 $\Omega \subset \mathbb{R}^n$ 是开区域，$k \in \mathbb{N}$，$1 \leq p \leq \infty$。

**Sobolev嵌入**：若 $k > n/p$，则
$$W^{k,p}(\Omega) \hookrightarrow C^{0,\alpha}(\Omega)$$
其中 $\alpha = k - n/p$（若 $k - n/p < 1$）或 $\alpha = 1$（否则）。

**Morrey嵌入**：若 $k - n/p = m + \sigma$（$m \in \mathbb{N}$，$0 < \sigma \leq 1$），则
$$W^{k,p}(\Omega) \hookrightarrow C^{m,\sigma}(\Omega)$$

**紧嵌入**（Rellich-Kondrachov）：若 $\Omega$ 有界且边界足够好，则嵌入是紧算子。

## 证明思路

1. **Gagliardo-Nirenberg不等式**：控制低阶导数
2. **Morrey不等式**：从弱可积性到连续性
3. **延拓定理**：将函数延拓到全空间
4. **紧性论证**：Arzelà-Ascoli定理应用

## 示例

### 示例 1：一维情形

**问题**：设 $n=1$，$p=2$，证明 $H^1(\mathbb{R}) \subseteq C^0(\mathbb{R})$。

**解答**：

对 $u \in H^1(\mathbb{R})$，由基本定理：
$$u(x) = u(y) + \int_y^x u'(t) dt$$

用Cauchy-Schwarz：
$$|u(x) - u(y)| \leq \|u'\|_{L^2} |x - y|^{1/2}$$

因此 $u$ 是1/2-Hölder连续的。

### 示例 2：二维Dirichlet问题

**问题**：设 $\Omega \subset \mathbb{R}^2$，证明 $H^2(\Omega) \subseteq C^0(\Omega)$。

**解答**：

$n=2$，$p=2$，$k=2$，满足 $k > n/p$（即 $2 > 1$）。

由Sobolev嵌入，$H^2(\Omega) \subseteq C^{0,\alpha}(\Omega)$ 对任意 $\alpha < 1$。

## 应用

- **椭圆型PDE**：弱解的正则性理论
- **变分法**：极小元的正则性
- **几何分析**：极小曲面的正则性
- **流体力学**：Navier-Stokes方程
- **量子力学**：Schrödinger算子的谱理论

## 相关概念

- [椭圆正则性](./elliptic-regularity.md)：PDE解的光滑性
- [Sobolev空间](./sobolev-space.md)：函数空间理论
- [Hölder空间](./holder-space.md)：目标嵌入空间
- [紧算子](./compact-operator.md)：紧嵌入的意义
- [分布理论](./distribution-theory.md)：弱导数的基础

## 参考

### 教材

- Adams, R.A. & Fournier, J.J.F. Sobolev Spaces. Academic Press, 2003.
- Evans, L.C. Partial Differential Equations. AMS, 2010. Chapter 5

### 论文

- Sobolev, S.L. On a theorem of functional analysis. Mat. Sb., 4: 471-497, 1938.
- Rellich, F. Ein Satz über mittlere Konvergenz. Math. Ann., 107: 607-611, 1930.

### 在线资源

- [Sobolev Inequality Wikipedia](https://en.wikipedia.org/wiki/Sobolev_inequality)
- [Sobolev Embedding Theorem nLab](https://ncatlab.org/nlab/show/Sobolev+embedding+theorem)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
