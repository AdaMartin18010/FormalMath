---
msc_primary: 00A99
processed_at: '2026-04-03'
title: Bishop-Gromov不等式 (Bishop-Gromov Inequality)
---
# Bishop-Gromov不等式 (Bishop-Gromov Inequality)

## Mathlib4 引用

```lean
import Mathlib.Geometry.RiemannianManifold.BishopGromov
import Mathlib.Geometry.RiemannianManifold.Volume

namespace BishopGromov

variable {M : Type*} [RiemannianMetric M] [CompleteSpace M]
  (hRic : ∀ x : M, RicciCurvature x ≥ (n-1) * k)

/-- Bishop-Gromov体积比较定理 -/
theorem bishop_gromov (x : M) (r R : ℝ) (hr : 0 < r) (hR : r ≤ R) :
    volume (ball x R) / volume (ball x r) ≤ volume (ball_{S_k} R) / volume (ball_{S_k} r) := by
  -- 体积元的Laplace比较
  sorry

/-- 体积增长的有界性 -/
theorem volume_growth_bounded (x : M) :
    Tendsto (fun r => volume (ball x r) / r^n) atTop (𝓝 (0 : ℝ)) := by
  sorry

end BishopGromov
```

## 数学背景

Bishop-Gromov不等式由Richard Bishop和Mikhail Gromov发展，是黎曼几何中关于体积比较的基本结果。它表明Ricci曲率有下界的流形的体积增长不超过空间形式（常曲率空间）。这是Gromov紧致性定理和许多几何分析结果的基础。

## 直观解释

Bishop-Gromov不等式告诉我们：**Ricci曲率有下界限制了流形"膨胀"的速度**。

想象曲率如何影响空间展开。正曲率（如球面）使体积增长慢于欧氏空间，负曲率（如双曲空间）使体积增长更快。不等式给出了精确的定量比较。

## 形式化表述

设 $\text{Ric} \geq (n-1)k$，$S_k$ 是常曲率 $k$ 的空间形式。

**Bishop-Gromov**：对 $0 < r \leq R$：
$$\frac{\text{Vol}(B(x, R))}{\text{Vol}(B(x, r))} \leq \frac{\text{Vol}(B_{S_k}(R))}{\text{Vol}(B_{S_k}(r))}$$

## 应用

- Gromov紧致性定理
- 极限空间理论（Alexandrov空间）
- Perelman的Ricci流理论

---

*最后更新：2026-04-03 | 版本：v1.0.0*
