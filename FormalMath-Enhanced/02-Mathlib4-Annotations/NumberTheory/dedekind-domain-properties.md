---
msc_primary: 00A99
processed_at: '2026-04-03'
title: Dedekind整环性质 (Dedekind Domain Properties)
---
# Dedekind整环性质 (Dedekind Domain Properties)

## Mathlib4 引用

```lean
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.FractionalIdeal.Basic

namespace DedekindDomain

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- Dedekind整环：理想唯一分解 -/
theorem ideal_unique_factorization {I : Ideal R} (hI : I ≠ ⊥) :
    ∃ (P : Finset {P : Ideal R // P.IsPrime ∧ P ≠ ⊥}) (e : {P // P.IsPrime ∧ P ≠ ⊥} → ℕ),
      I = ∏ P in P, (P : Ideal R) ^ e P := by
  -- 理想类群有限性的推论
  sorry

/-- 分式理想的可逆性 -/
theorem fractional_ideal_invertible (I : FractionalIdeal R K) (hI : I ≠ 0) :
    ∃ J, I * J = 1 := by
  -- Dedekind整环的定义
  sorry

/-- Dedekind整环是Noether整闭整区 -/
theorem dedekind_characterization :
    IsNoetherian R R ∧ IsIntegrallyClosed R ∧ ∀ P : Ideal R, P.IsPrime → P = ⊥ ∨ P.IsMaximal := by
  constructor
  · -- Noether性质
    sorry
  constructor
  · -- 整闭性
    sorry
  · -- 维数≤1
    sorry

end DedekindDomain
```

## 数学背景

Dedekind整环由Richard Dedekind在19世纪引入，是代数数论的核心概念。它是整数环在数域中的自然推广，满足理想的唯一分解性质（替代元素的分解）。Dedekind证明了数域的整数环具有这一性质，奠定了代数数论的基础。Dedekind整环的理论是类域论、Iwasawa理论和现代算术几何的基础。

## 直观解释

Dedekind整环告诉我们：**在"好"的数环中，虽然元素可能没有唯一分解，但理想总有唯一分解**。

想象整数可以分解为素数的乘积。在某些数环（如 $\mathbb{Z}[\sqrt{-5}]$）中，元素可能没有唯一分解（$6 = 2 \cdot 3 = (1+\sqrt{-5})(1-\sqrt{-5})$）。Dedekind发现，如果考虑"理想"（可以看作"素数分布"）而不是单个元素，唯一分解仍然成立。这就像说，虽然不同方式包装的货物看起来不同，但它们来自同一批货源。

## 形式化表述

整环 $R$ 称为**Dedekind整环**，如果满足以下等价条件之一：

1. $R$ 是Noether、整闭、维数 $\leq 1$（非零素理想极大）
2. $R$ 的分式理想群可逆（是群）
3. $R$ 是Noether且局部化在每非零素理想是DVR

**理想唯一分解**：每个非零理想 $I$ 可唯一写成：
$$I = P_1^{e_1} P_2^{e_2} \cdots P_k^{e_k}$$
其中 $P_i$ 是相异素理想。

## 证明思路

1. **Noether $\Rightarrow$ 理想有限生成**
2. **整闭 $\Rightarrow$ 元素积分封闭**
3. **维数 $\leq 1$ $\Rightarrow$ 非零素理想极大**

**理想分解**：

- 对理想 $I$，考虑 $R/I$ 是Artin环
- Artin环的理想是有限个极大理想的交
- 提升得到 $I$ 的分解

**唯一性**：

- 局部化在每素理想是DVR
- DVR中理想唯一分解
- 整体唯一性由局部唯一性得到

核心洞察是局部化方法与理想理论的结合。

## 示例

### 示例 1：整数环

$\mathbb{Z}$ 是Dedekind整环。

理想 $(6) = (2)(3) = (2) \cap (3)$。

### 示例 2：二次域

$K = \mathbb{Q}(\sqrt{-5})$，$\mathcal{O}_K = \mathbb{Z}[\sqrt{-5}]$。

$(6) = (2, 1+\sqrt{-5})^2 (3, 1+\sqrt{-5}) (3, 1-\sqrt{-5})$。

### 示例 3：多项式环

$k[x]$（$k$ 域）是Dedekind整环。

理想对应首一多项式。

## 应用

- **代数数论**：数域的整数环
- **代数几何**：光滑曲线的坐标环
- **类域论**：理想类群与Abel扩张
- **密码学**：椭圆曲线的算术
- **编码理论**：代数几何码

## 相关概念

- 理想类群 (Ideal Class Group)：分式理想模主理想
- 分式理想 (Fractional Ideal)：理想的推广
- DVR (Discrete Valuation Ring)：局部Dedekind整环
- 整闭性 (Integral Closure)：代数整元的封闭性
- 类数 (Class Number)：类群的阶

## 参考

### 教材

- [Neukirch. Algebraic Number Theory. Springer, 1999. Chapter 1]
- [Marcus. Number Fields. Springer, 1977. Chapter 3]

### 历史文献

- [Dedekind. Sur la théorie des nombres entiers algébriques. 1877]

### 在线资源

- [Mathlib4 文档 - DedekindDomain](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/DedekindDomain/Basic.html)[需更新]
- [Wikipedia - Dedekind Domain](https://en.wikipedia.org/wiki/Dedekind_domain)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
