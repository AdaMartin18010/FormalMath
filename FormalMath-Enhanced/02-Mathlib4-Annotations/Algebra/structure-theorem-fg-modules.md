---
msc_primary: 00A99
processed_at: '2026-04-03'
title: 有限生成模结构定理 (Structure Theorem for Finitely Generated Modules)
---
# 有限生成模结构定理 (Structure Theorem for Finitely Generated Modules)

## Mathlib4 引用

```lean
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Module.Torsion

namespace StructureTheorem

variable {R : Type*} [CommRing R] [IsPrincipalIdealRing R] [IsDomain R]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- PID上有限生成模的结构定理 -/
theorem structure_theorem_pid :
    ∃ (n : ℕ) (p : Fin n → R) (e : Fin n → ℕ),
      (∀ i, Irreducible (p i)) ∧
      Nonempty (M ≅ₗ[R] (R ⧸ Ideals (p i ^ e i))) := by
  -- 分解为自由部分和挠部分
  have hfree : ∃ r : ℕ, Nonempty (M ⧸ Module.torsion R M ≅ₗ[R] (Fin r → R)) := by
    sorry
  have htorsion : ∃ (s : ℕ) (p : Fin s → R) (e : Fin s → ℕ),
    (∀ i, Irreducible (p i)) ∧
    Nonempty (Module.torsion R M ≅ₗ[R] (⨁ i, R ⧸ Ideals (p i ^ e i))) := by
    sorry
  sorry

/-- 不变因子分解 -/
theorem invariant_factor_decomposition :
    ∃ (r : ℕ) (d : Fin r → R),
      (∀ i, d i ∣ d (i + 1)) ∧
      Nonempty (M ≅ₗ[R] (⨁ i, R ⧸ Ideals (d i))) := by
  sorry

/-- 初等因子分解 -/
theorem elementary_divisor_decomposition (htor : Module.IsTorsion R M) :
    ∃ (s : ℕ) (p : Fin s → R) (e : Fin s → ℕ),
      (∀ i, Irreducible (p i)) ∧
      Nonempty (M ≅ₗ[R] (⨁ i, R ⧸ Ideals (p i ^ e i))) := by
  sorry

end StructureTheorem
```

## 数学背景

PID上有限生成模结构定理由Frobenius和Stickelberger在1878年对阿贝尔群（$\mathbb{Z}$-模）证明，后推广到一般PID。这是线性代数基本定理（有限维向量空间有基）到模论的深刻推广。该定理表明，PID上的有限生成模可以完全分类为循环模的直和，其形式类似于有限阿贝尔群的基本定理。

## 直观解释

结构定理告诉我们：**PID上的有限生成模都像"扭曲"的向量空间**。

想象整数上的模。有些元素可以被任意整数"缩放"（自由部分），有些则被限制（挠部分）。结构定理说整个模可以分解为这些部分的直和：一部分像向量空间（自由），另一部分像有限群（挠）。挠部分进一步分解为循环 $p$-群，类似于整数的素因数分解。

## 形式化表述

设 $R$ 是PID，$M$ 是有限生成 $R$-模。

**结构定理**：$M$ 同构于：
$$M \cong R^r \oplus \bigoplus_{i=1}^k R/(d_i)$$

其中：
- $r \geq 0$ 是自由秩（不变量）
- $d_1 | d_2 | \cdots | d_k$ 是非零非单位的**不变因子**（唯一确定）

**初等因子形式**：挠部分也可写成：
$$\text{Tor}(M) \cong \bigoplus_{j} R/(p_j^{e_j})$$

其中 $p_j$ 是素元，$e_j \geq 1$。

## 证明思路

1. **关系矩阵**：设 $M$ 由 $n$ 个元素生成，有 $m$ 个关系，得 $m \times n$ 关系矩阵
2. **Smith标准形**：通过初等变换化为对角形 $\text{diag}(d_1, \ldots, d_r, 0, \ldots, 0)$
3. **PID性质**：利用PID是Bézout域，初等变换对应可逆操作
4. **循环分解**：标准形给出循环模的直和分解
5. **唯一性**：通过理想序列的唯一性证明不变因子的唯一性

核心洞察是PID允许矩阵对角化，将复杂模结构约化为循环模。

## 示例

### 示例 1：有限阿贝尔群

设 $M = \mathbb{Z}_{12} \times \mathbb{Z}_{18}$。

初等因子分解：$\mathbb{Z}_{12} \cong \mathbb{Z}_4 \times \mathbb{Z}_3$，$\mathbb{Z}_{18} \cong \mathbb{Z}_2 \times \mathbb{Z}_9$

故 $M \cong \mathbb{Z}_2 \times \mathbb{Z}_4 \times \mathbb{Z}_3 \times \mathbb{Z}_9$

不变因子分解：$M \cong \mathbb{Z}_6 \times \mathbb{Z}_{36}$（因为 $\text{lcm}(2,4) = 4$，等等）

### 示例 2：线性变换的标准形

设 $T: V \to V$ 是有限维空间上的线性算子。

$V$ 成为 $k[x]$-模，$x \cdot v = T(v)$。

结构定理给出有理标准形和Jordan标准形。

### 示例 3：格上的模

设 $M$ 是有限生成 $\mathbb{Z}[i]$-模（Gauss整数）。

结构定理给出分解：$M \cong \mathbb{Z}[i]^r \oplus \bigoplus \mathbb{Z}[i]/(\pi_j^{e_j})$。

## 应用

- **线性代数**：Jordan标准形和有理标准形
- **阿贝尔群分类**：有限生成阿贝尔群的结构
- **代数数论**：理想类的结构
- **代数拓扑**：同调群的计算
- **编码理论**：循环码的分类

## 相关概念

- [PID (Principal Ideal Domain)](./pid.md)：主理想整环
- [Smith标准形 (Smith Normal Form)](./smith-normal-form.md)：矩阵对角化
- [挠模 (Torsion Module)](./torsion-module.md)：被非零元零化的元素
- [不变因子 (Invariant Factor)](./invariant-factor.md)：分解中的整除序列
- [初等因子 (Elementary Divisor)](./elementary-divisor.md)：素幂分解

## 参考

### 教材

- [Dummit & Foote. Abstract Algebra. Wiley, 3rd edition, 2004. Chapter 12]
- [Hungerford. Algebra. Springer, 1974. Chapter 4]

### 历史文献

- [Frobenius & Stickelberger. Über Gruppen von vertauschbaren Elementen. 1878]

### 在线资源

- [Mathlib4 文档 - Module PID](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/PID.html)
- [Keith Conrad - Modules over PIDs](https://kconrad.math.uconn.edu/blurbs/linmultialg/modulesoverpids.pdf)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
