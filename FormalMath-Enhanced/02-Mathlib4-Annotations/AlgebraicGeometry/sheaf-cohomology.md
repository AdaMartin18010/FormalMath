---
msc_primary: 00A99
processed_at: '2026-04-03'
title: 层上同调
---
# 层上同调

## Mathlib4 引用

```lean
import Mathlib.AlgebraicGeometry.SheafCohomology

namespace AlgebraicGeometry

/-- 层上同调的定义 -/
theorem sheaf_cohomology_def
    {X : Type*} [TopologicalSpace X]
    {𝓞 : SheafOfRings X}
    {ℱ : SheafOfModules 𝓞}
    (n : ℕ) :
    H^n X ℱ = R^n Γ(X, -) ℱ := by
  -- 层上同调是整体截面函子的导出函子
  rfl

/-- 层上同调的长正合列 -/
theorem cohomology_long_exact
    {X : Type*} [TopologicalSpace X]
    {𝓞 : SheafOfRings X}
    {ℱ 𝒢 ℋ : SheafOfModules 𝓞}
    (f : ℱ ⟶ 𝒢) (g : 𝒢 ⟶ ℋ)
    (h : ShortExact f g) (n : ℕ) :
    ExactSequence (
      H^n X ℱ → H^n X 𝒢 → H^n X ℋ →
      H^{n+1} X ℱ) := by
  -- 导出函子保持短正合列的长正合列
  apply right_derived_exact

end AlgebraicGeometry
```

## 数学背景

层上同调理论由Jean Leray在1945年左右发明，由Henri Cartan和Alexander Grothendieck在1950年代发展完善。这一理论是代数几何的核心工具，将拓扑上同调的概念推广到层的框架中。层上同调统一了代数拓扑中的奇异上同调、代数几何中的 coherent 层上同调、以及复几何中的Dolbeault上同调。Grothendieck用层上同调证明了Serre对偶、Riemann-Roch定理和Weil猜想。

## 直观解释

层上同调度量了"局部到整体"的障碍。想象一个层 $\mathcal{F}$ 在空间 $X$ 上"传播"数据。如果 $X$ 可以被开集 $\{U_i\}$ 覆盖，在每个 $U_i$ 上有"好的"数据（截面），我们希望将这些局部数据"粘合"成整体数据。层上同调群 $H^n(X, \mathcal{F})$ 度量了这种粘合过程的$n$阶障碍。$H^0$ 是已成功粘合的整体截面，$H^1$ 度量了粘合的"冲突"，更高阶的上同调则度量更复杂的相互作用。

## 形式化表述

设 $(X, \mathcal{O}_X)$ 是环化空间，$\mathcal{F}$ 是 $\mathcal{O}_X$-模层。

**定义**：$H^n(X, \mathcal{F}) = R^n\Gamma(X, \mathcal{F})$

其中 $\Gamma(X, -)$ 是整体截面函子，$R^n$ 是其右导出函子。

**Čech上同调**：对开覆盖 $\mathcal{U} = \{U_i\}$，
$$\check{H}^n(\mathcal{U}, \mathcal{F}) = H^n(\check{C}^\bullet(\mathcal{U}, \mathcal{F}))$$
在适当条件下与导出函子定义一致。

**局部上同调**：对闭子集 $Z \subseteq X$，
$$H_Z^n(X, \mathcal{F}) = \varinjlim_{U \supset Z} H^n(U, \mathcal{F})$$

## 证明思路

1. **内射分解**：构造 $\mathcal{F} \to \mathcal{I}^\bullet$
2. **整体截面**：应用 $\Gamma(X, -)$ 得到复形
3. **上同调计算**：取复形的上同调
4. **Čech计算**：用开覆盖逼近
5. **比较定理**：验证不同定义等价

## 示例

### 示例 1：仿射概形的层上同调

**问题**：证明仿射概形上 quasi-coherent 层的上同调消失。

**解答**：

**Serre定理**：设 $X = \text{Spec}(A)$ 是仿射概形，$\mathcal{F} = \widetilde{M}$ 是 quasi-coherent 层。

则 $H^n(X, \mathcal{F}) = 0$ 对所有 $n > 0$。

这推广了仿射代数几何中的基本结果。

### 示例 2：复流形的Dolbeault上同调

**问题**：层上同调与Dolbeault理论的关系。

**解答**：

对复流形 $X$：
$$H^q(X, \Omega_X^p) = H^{p,q}_{\bar{\partial}}(X)$$

其中 $\Omega_X^p$ 是全纯 $p$-形式层。

这是Dolbeault定理，将层上同调与微分形式联系起来。

## 应用

- **Riemann-Roch定理**：曲线上的Euler示性数
- **Serre对偶**：层上同调的对称性
- **Kodaira消失定理**：正线丛的上同调
- **étale上同调**：Weil猜想的证明
- **形变理论**：Kodaira-Spencer理论

## 相关概念

- 导出函子：层上同调的理论基础
- Čech上同调：计算方法
- 局部上同调：支撑在闭子集的上同调
- [Serre对偶](./serre-duality.md)：层上同调的对偶性
- Hilbert多项式：射影概形的Euler示性数

## 参考

### 教材

- Hartshorne, R. Algebraic Geometry. Springer, 1977. Chapter 3
- Godement, R. Topologie Algébrique et Théorie des Faisceaux. Hermann, 1958.

### 论文

- Serre, J-P. Faisceaux algébriques cohérents. Ann. of Math., 61: 197-278, 1955.
- Grothendieck, A. Sur quelques points d'algèbre homologique. Tôhoku Math. J., 9: 119-221, 1957.

### 在线资源

- [Sheaf Cohomology Wikipedia](https://en.wikipedia.org/wiki/Sheaf_cohomology)
- [Stacks Project - Cohomology of Sheaves](https://stacks.math.columbia.edu/tag/01E2)[需更新]

---

*最后更新：2026-04-03 | 版本：v1.0.0*
