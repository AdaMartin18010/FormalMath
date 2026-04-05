---
msc_primary: 00A99
processed_at: '2026-04-03'
title: Darboux定理 (Darboux's Theorem)
---
# Darboux定理 (Darboux's Theorem)

## Mathlib4 引用

```lean
import Mathlib.Geometry.Symplectic.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

namespace DarbouxTheorem

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2n)) M]
  [SmoothManifoldWithCorners (𝓡 (2n)) M] [SymplecticForm M]

/-- Darboux定理：辛流形的局部标准形 -/
theorem darboux (x : M) :
    ∃ (U : OpenNhds x) (φ : U ≃ᵐ (OpenBall (0 : EuclideanSpace ℝ (Fin 2n)) 1)),
      ∀ y ∈ U, φ.symm* (symplecticForm (φ y)) = ∑ i, dp_i ∧ dq_i := by
  -- Moser同痕技巧
  sorry

/-- 线性Darboux定理 -/
theorem linear_darboux {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (ω : AlternatingMap ℝ V ℝ (Fin 2)) (hω : Nondegenerate ω) :
    ∃ (e : V ≃ₗ[ℝ] Fin n → ℝ × ℝ),
      ∀ v w, ω v w = ∑ i, (e v i).1 * (e w i).2 - (e v i).2 * (e w i).1 := by
  -- 辛基的构造
  sorry

end DarbouxTheorem
```

## 数学背景

Darboux定理由Gaston Darboux在1882年证明，是辛几何的基本结果。该定理表明所有辛流形在局部都是"相同"的——局部辛同构于标准辛空间 $(\mathbb{R}^{2n}, \sum dp_i \wedge dq_i)$。这与黎曼几何形成鲜明对比（曲率是局部不变量），显示了辛结构的"柔性"。Darboux定理是哈密顿力学和几何量子化的基础。

## 直观解释

Darboux定理告诉我们：**所有辛空间在局部看起来都一样**。

想象辛结构像一种"几何织物"。定理说，无论这种织物有多复杂，在局部（小区域）它总是可以"熨平"成标准形式。这与黎曼几何中的曲率不同——辛几何没有局部不变量，只有全局拓扑不变量。

## 形式化表述

设 $(M, \omega)$ 是辛流形（$\omega$ 是闭的非退化2-形式）。

**Darboux定理**：对任意 $x \in M$，存在坐标邻域 $(U, (p_1, \ldots, p_n, q_1, \ldots, q_n))$ 使得：
$$\omega|_U = \sum_{i=1}^n dp_i \wedge dq_i$$

**辛坐标**：$(p_i, q_i)$ 称为Darboux坐标或辛坐标。

**等价表述**：所有同维数的辛流形局部辛同构。

## 证明思路

1. **Moser同痕技巧**：
   - 给定两个辛形式 $\omega_0, \omega_1$
   - 构造同痕 $\phi_t$ 使得 $\phi_t^* \omega_t = \omega_0$
   
2. **线性Darboux**：
   - 先找到切空间上的辛基
   - 用指数映射局部延拓
   
3. **标准形**：
   - 证明 $\omega$ 与标准形式 $\omega_0 = \sum dp_i \wedge dq_i$ 同痕
   - 由Moser技巧得局部等价

核心洞察是辛形式的闭性与非退化性允许局部"标准化"。

## 示例

### 示例 1：余切丛

$T^*Q$ 有标准辛结构 $\omega = d\theta$，其中 $\theta = p_i dq^i$ 是Liouville形式。

局部坐标 $(q^i, p_i)$ 是Darboux坐标。

### 示例 2：$\mathbb{R}^{2n}$

标准辛结构：$\omega = \sum dx_i \wedge dy_i$。

$(x_i, y_i)$ 是Darboux坐标。

### 示例 3：球面

$S^2$ 有标准辛结构（面积形式）。

局部用球坐标 $(\theta, \phi)$，但这不是辛坐标。

需用立体投影得到Darboux坐标。

## 应用

- **哈密顿力学**：正则方程的标准形式
- **几何量子化**：极化选择
- **镜像对称**：辛几何与复几何的对偶
- **Floer同调**：辛拓扑不变量
- **Gromov-Witten理论**：伪全纯曲线

## 相关概念

- [辛形式 (Symplectic Form)](./symplectic-form.md)：闭的非退化2-形式
- [辛流形 (Symplectic Manifold)](./symplectic-manifold.md)：带辛结构的流形
- [Moser同痕 (Moser Isotopy)](./moser-isotopy.md)：辛形式变形技巧
- [Liouville形式 (Liouville Form)](./liouville-form.md)：余切丛的典则1-形式
- [辛同构 (Symplectomorphism)](./symplectomorphism.md)：辛结构的同构

## 参考

### 教材

- [Cannas da Silva. Lectures on Symplectic Geometry. Springer, 2008. Chapter 3]
- [McDuff & Salamon. Introduction to Symplectic Topology. Oxford, 2nd edition, 1998. Chapter 2]

### 历史文献

- [Darboux. Sur le problème de Pfaff. 1882]

### 在线资源

- [Mathlib4 文档 - Symplectic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Symplectic/Basic.html)
- [Wikipedia - Darboux's Theorem](https://en.wikipedia.org/wiki/Darboux%27s_theorem)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
