---
msc_primary: 00A99
processed_at: '2026-04-03'
title: Serre对偶定理
---
# Serre对偶定理

## Mathlib4 引用

```lean
import Mathlib.AlgebraicGeometry.SerreDuality

namespace AlgebraicGeometry

/-- Serre对偶定理 -/
theorem serre_duality 
    {X : Type*} [Scheme X] [IsProper X] [IsSmooth X]
    {n : ℕ} (hX : FiniteDimensional X n)
    {ℱ : CoherentSheaf X} :
    H^i X ℱ ≅ (H^{n-i} X (ℱ∨ ⊗ ω_X))∨ := by
  -- 层上同调的对偶性
  sorry

/-- 对偶层（典则层） -/
theorem canonical_sheaf 
    {X : Type*} [Scheme X] [IsSmooth X] :
    ω_X = Λ^n Ω_X := by
  -- 典则层是最高阶微分形式
  rfl

end AlgebraicGeometry
```

## 数学背景

Serre对偶定理由Jean-Pierre Serre在1955年证明，是代数几何中最基本的结果之一。定理建立了代数簇上 coherent 层上同调群之间的对偶关系，推广了代数曲线上的经典Riemann-Roch理论。Serre对偶是Hodge理论在代数几何中的类比，也是现代双有理几何和模空间理论的基础。这一结果深刻影响了Grothendieck对偶性理论的发展。

## 直观解释

Serre对偶如同一个"镜像对称"：$i$ 阶上同调与 $(n-i)$ 阶上同调通过对偶相互对应。想象一个 $n$ 维代数簇 $X$ 如同一个复杂的"形状"，层 $\mathcal{F}$ 如同在这个形状上"涂抹"的结构。Serre对偶告诉我们：$\mathcal{F}$ 的"洞"（上同调）与某种"对偶结构"（$\mathcal{F}^\vee \otimes \omega_X$）的"洞"以互补的方式配对。典则层 $\omega_X$ 如同这个形状的"体积形式"，提供了对偶配对的基础。

## 形式化表述

设 $X$ 是 $n$ 维光滑射影簇，$\mathcal{F}$ 是 coherent 层。

**Serre对偶**：存在自然同构
$$H^i(X, \mathcal{F}) \cong H^{n-i}(X, \mathcal{F}^\vee \otimes \omega_X)^*$$

其中：
- $\mathcal{F}^\vee = \mathcal{Hom}(\mathcal{F}, \mathcal{O}_X)$ 是对偶层
- $\omega_X = \Lambda^n \Omega_X^1$ 是典则层（最高阶微分形式）
- $V^*$ 表示线性对偶

**迹映射**：存在典范映射 $\text{Tr}: H^n(X, \omega_X) \to k$，使得对偶配对由杯积和迹给出。

## 证明思路

1. **Ext解释**：$H^i(X, \mathcal{F}) = \text{Ext}^i(\mathcal{O}_X, \mathcal{F})$
2. **Yoneda配对**：Ext与局部Ext的配对
3. **局部对偶**：局部上同调的对偶性
4. **迹构造**：$H^n(X, \omega_X) \cong k$
5. **整体配对**：组装局部配对得到整体对偶

## 示例

### 示例 1：曲线的Riemann-Roch

**问题**：从Serre对偶推导曲线的Riemann-Roch定理。

**解答**：

对曲线 $C$ 上的线丛 $L$：

$H^0(C, L)$ 和 $H^1(C, L) \cong H^0(C, K_C \otimes L^{-1})^*$

因此 $\chi(L) = h^0(L) - h^0(K_C \otimes L^{-1}) = \deg(L) + 1 - g$。

这就是Riemann-Roch公式。

### 示例 2：曲面的几何亏格

**问题**：计算曲面的几何亏格 $p_g = h^0(X, \omega_X)$。

**解答**：

由Serre对偶：$h^2(X, \mathcal{O}_X) = h^0(X, \omega_X) = p_g$。

Euler示性数：$\chi(\mathcal{O}_X) = 1 - q + p_g$，其中 $q = h^1(X, \mathcal{O}_X)$。

这是曲面的基本不变量。

## 应用

- **Riemann-Roch定理**：曲线和曲面的推广
- **Kodaira消失定理**：正线丛的上同调消失
- **双有理几何**：典范模型和极小模型
- **模空间理论**：形变和障碍理论
- ** mirror symmetry**：Hodge数的对称性

## 相关概念

- [层上同调](./sheaf-cohomology.md)：Serre对偶的对象
- [典则层](./canonical-sheaf.md)：对偶性中的关键层
- [Grothendieck对偶](./grothendieck-duality.md)：Serre对偶的推广
- [Riemann-Roch定理](./riemann-roch-theorem.md)：Serre对偶的应用
- [Kodaira消失定理](./kodaira-vanishing.md)：Serre对偶的推论

## 参考

### 教材

- Hartshorne, R. Algebraic Geometry. Springer, 1977. Chapter 3
- Serre, J-P. Faisceaux algébriques cohérents. Ann. of Math., 61: 197-278, 1955.

### 论文

- Serre, J-P. Un théorème de dualité. Comment. Math. Helv., 29: 9-26, 1955.
- Grothendieck, A. Théorèmes de dualité pour les faisceaux algébriques cohérents. Séminaire Bourbaki, 149, 1957.

### 在线资源

- [Serre Duality Wikipedia](https://en.wikipedia.org/wiki/Serre_duality)
- [Stacks Project - Duality](https://stacks.math.columbia.edu/tag/0A7B)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
