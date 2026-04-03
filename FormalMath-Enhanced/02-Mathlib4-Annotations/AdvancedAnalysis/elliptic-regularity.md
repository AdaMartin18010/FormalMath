# 椭圆正则性定理

## Mathlib4 引用

```lean
import Mathlib.Analysis.PDE.EllipticRegularity

namespace Analysis

/-- 椭圆正则性定理 -/
theorem elliptic_regularity 
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω)
    {L : PartialDifferentialOperator ℝ Ω}
    (hL : L.IsUniformlyElliptic)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : DistributionSolution L u = f)
    (hf : f ∈ C^∞ Ω) :
    u ∈ C^∞ Ω := by
  -- 椭圆方程的光滑解必为光滑函数
  sorry

/-- 先验估计 -/
theorem a_priori_estimate 
    {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) (hΩ_bdd : IsBounded Ω)
    {L : PartialDifferentialOperator ℝ Ω}
    (hL : L.IsUniformlyElliptic)
    {k : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : IsSolution L u) :
    ∃ (C : ℝ), ‖u‖_{C^{k+2}} ≤ C * (‖Lu‖_{C^k} + ‖u‖_{C^0}) := by
  -- Schauder估计
  sorry

end Analysis
```

## 数学背景

椭圆正则性理论是偏微分方程中最深刻的结果之一，由Bernstein、Schauder、Hopf、Morrey和Nirenberg等人在20世纪上半叶发展。该理论表明：椭圆型偏微分方程的解自动继承方程系数的正则性。这意味着即使我们从非常弱的解概念（如分布解）出发，解实际上也是非常光滑的。这一结果在几何分析、数学物理和变分法中具有根本性意义。

## 直观解释

椭圆正则性定理解释了椭圆型方程的"内在光滑性"。想象一个弹性膜（由椭圆方程描述）——即使边界条件有轻微不规则，膜本身内部也会非常光滑。这是因为椭圆算子"扩散"信息：任何局部的不规则都会被算子的"平均化"效应平滑掉。相比之下，双曲方程（如波动方程）允许奇性传播，抛物方程则介于两者之间。

## 形式化表述

设 $L$ 是 $\Omega \subset \mathbb{R}^n$ 上的一致椭圆算子：
$$Lu = -\sum_{i,j} a_{ij}(x) \partial_i \partial_j u + \sum_i b_i(x) \partial_i u + c(x)u$$
其中 $a_{ij}$ 一致正定。

**内部正则性**：若 $Lu = f$ 在 $\Omega$ 中，且 $f \in C^{k,\alpha}_{\text{loc}}(\Omega)$，$a_{ij}, b_i, c \in C^{k,\alpha}(\Omega)$，则 $u \in C^{k+2,\alpha}_{\text{loc}}(\Omega)$。

**全局正则性**：若边界 $\partial \Omega \in C^{k+2,\alpha}$，边界条件适当，则 $u \in C^{k+2,\alpha}(\bar{\Omega})$。

**Schauder估计**：$\|u\|_{C^{k+2,\alpha}} \leq C(\|Lu\|_{C^{k,\alpha}} + \|u\|_{C^0})$

## 证明思路

1. **Caccioppoli不等式**：控制局部能量
2. **Campanato空间**：刻画Hölder连续性
3. **凝固系数法**：将变系数问题转化为常系数
4. **Schauder估计**：建立先验估计
5. ** bootstrap论证**：迭代提高正则性

## 示例

### 示例 1：Poisson方程

**问题**：设 $-\Delta u = f$ 在 $\Omega$ 中，$f \in C^{\infty}(\Omega)$，证明 $u \in C^{\infty}(\Omega)$。

**解答**：

Laplace算子是一致椭圆的（系数为恒等矩阵）。

由椭圆正则性，$u$ 在每个紧子集上无限可微。

这解释了为什么调和函数自动是实解析的。

### 示例 2：极小曲面方程

**问题**：描述非参数极小曲面方程的正则性。

**解答**：

方程：$\text{div}\left(\frac{\nabla u}{\sqrt{1 + |\nabla u|^2}}\right) = 0$

这是拟线性椭圆方程。Bernstein定理：在 $\mathbb{R}^2$ 上，任何整体解都是线性的（即极小曲面是平面）。

## 应用

- **极小曲面**：Plateau问题的正则性
- **Yamabe问题**：共形几何中的PDE
- **几何流**：Ricci流、平均曲率流
- **数学物理**：稳态问题的光滑解
- **控制理论**：椭圆型最优控制

## 相关概念

- [Sobolev嵌入](./sobolev-embedding.md)：正则性理论的函数空间
- [Schauder估计](./schauder-estimate.md)：先验估计技术
- [Harnack不等式](./harnack-inequality.md)：椭圆方程的性质
- [极大值原理](./maximum-principle.md)：椭圆方程的工具
- [分布解](./distribution-solution.md)：弱解概念

## 参考

### 教材

- Gilbarg, D. & Trudinger, N.S. Elliptic Partial Differential Equations of Second Order. Springer, 2001.
- Chen, Y.Z. & Wu, L.C. Second Order Elliptic Equations and Elliptic Systems. AMS, 1998.

### 论文

- Schauder, J. Über lineare elliptische Differentialgleichungen zweiter Ordnung. Math. Z., 38: 257-282, 1934.
- De Giorgi, E. Sulla differenziabilità e l'analiticità delle estremali degli integrali multipli regolari. Mem. Accad. Sci. Torino, 3: 25-43, 1957.

### 在线资源

- [Elliptic Regularity Wikipedia](https://en.wikipedia.org/wiki/Elliptic_regularity)
- [Schauder Estimates nLab](https://ncatlab.org/nlab/show/Schauder+estimate)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
