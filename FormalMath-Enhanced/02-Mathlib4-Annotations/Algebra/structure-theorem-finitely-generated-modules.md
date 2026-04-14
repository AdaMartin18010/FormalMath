---
msc_primary: 00A99
processed_at: '2026-04-15'
title: 有限生成模结构定理 (Structure Theorem for Finitely Generated Modules)
---
# 有限生成模结构定理 (Structure Theorem for Finitely Generated Modules)

## Mathlib4 引用

```lean
import Mathlib.Algebra.Module.PID

namespace StructureTheorem

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- 结构定理：有限生成 PID 上的模同构于自由部分与扭部分的直积 -/
theorem equiv_free_prod_directSum [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Finite R M] : ∃ (r : ℕ) (p : Fin n → R) (e : Fin n → ℕ),
    Nonempty (M ≃ₗ[R] (Fin r → R) × ⨁ i : Fin n, R ⧸ R ∙ (p i ^ e i)) := by
  -- 参见 Mathlib4 Algebra.Module.PID
  sorry

end StructureTheorem
```

## 数学背景

有限生成模结构定理是交换代数与线性代数中最深刻的分类结果之一。当基环为主理想整环（PID）时，该定理断言任何有限生成模都可以唯一地分解为自由部分与扭部分的直和，其中扭部分进一步分解为素数幂循环模的直和。这一定理统一了有限生成 Abel 群的结构定理（$R = \mathbb{Z}$）和线性变换的 Jordan 标准型理论（$R = F[x]$），是19世纪末至20世纪初代数学的核心成就。

## 直观解释

结构定理告诉我们：**PID 上的有限生成模就像乐高积木搭成的模型，总能拆成两类基本积木——“自由积木条”和“扭动积木环”**。自由部分类似于向量空间（可以沿任意方向无限延伸），而扭部分则像被“卡住”的结构——沿某些方向走有限步后会回到原点。每个扭动环的大小由素数幂决定，就像钟表有不同齿数。

## 形式化表述

设 $R$ 为主理想整环（PID），$M$ 为有限生成 $R$-模，则存在非负整数 $r$（自由秩）和不变因子 $d_1, d_2, \ldots, d_k \in R$（满足 $d_1 \mid d_2 \mid \cdots \mid d_k$），使得：

$$M \cong R^r \oplus R/(d_1) \oplus R/(d_2) \oplus \cdots \oplus R/(d_k)$$

**初等因子形式**：也可分解为素数幂循环模的直和

$$M \cong R^r \oplus \bigoplus_{i,j} R/(p_i^{e_{ij}})$$

其中 $p_i$ 为 $R$ 中的素元（在 $\mathbb{Z}$ 中对应素数，在 $F[x]$ 中对应不可约多项式）。

## 证明思路

1. **扭子模分解**：证明 $M = M_{tor} \oplus M_{free}$，其中 $M_{free} \cong R^r$ 为自由部分
2. **素幂分解**：对扭子模，利用中国剩余定理将其分解为 $p$-准素分量的直和
3. **循环模结构**：证明每个 $p$-准素分量可进一步分解为循环模 $R/(p^e)$ 的直和
4. **唯一性**：通过零化子和初等因子的唯一性证明两种分解形式在同构意义下唯一

核心工具包括：Smith 标准型、主理想整环上的矩阵对角化、以及模的升链条件。

## 示例

### 示例 1：有限生成 Abel 群

取 $R = \mathbb{Z}$。任何有限生成 Abel 群具有形式：

$$G \cong \mathbb{Z}^r \oplus \mathbb{Z}_{d_1} \oplus \cdots \oplus \mathbb{Z}_{d_k}$$

例如 $\mathbb{Z}_{12} \oplus \mathbb{Z}_{18}$ 的初等因子形式为 $\mathbb{Z}_2 \oplus \mathbb{Z}_4 \oplus \mathbb{Z}_9 \oplus \mathbb{Z}_3$（需重新组合验证）。

### 示例 2：Jordan 标准型

取 $R = F[x]$，$V$ 为有限维 $F$-向量空间，$T: V \to V$ 为线性变换。将 $V$ 看作 $F[x]$-模（$x \cdot v = T(v)$），则：

$$V \cong F[x]/(p_1(x)^{e_1}) \oplus \cdots \oplus F[x]/(p_k(x)^{e_k})$$

当 $F = \mathbb{C}$ 时，$p_i(x) = x - \lambda_i$，对应 Jordan 块。

### 示例 3：具体模分解

设 $R = \mathbb{Z}$，$M = \mathbb{Z}^2 / \langle (2,0), (0,6) \rangle$。

通过 Smith 标准型计算得 $M \cong \mathbb{Z}_2 \oplus \mathbb{Z}_6 \cong \mathbb{Z}_2 \oplus \mathbb{Z}_2 \oplus \mathbb{Z}_3$。

## 应用

- **线性代数**：Jordan 标准型与有理标准型的统一理论
- **代数数论**：理想类群与 Dedekind 域上的模结构
- **代数几何**：层上同调与局部自由分解
- **编码理论**：循环码与模论方法
- **拓扑学**：同调群的计算与胞腔复形

## 相关概念

- 主理想整环 (PID)：每个理想都由单个元素生成的整环
- 扭子模 (Torsion Submodule)：被非零元零化的元素构成的子模
- 自由模 (Free Module)：具有基底的模，同构于 $R^n$
- Smith 标准型 (Smith Normal Form)：PID 上矩阵的对角标准型
- 中国剩余定理 (Chinese Remainder Theorem)：环的直积分解工具

## 参考

### 教材

- [Dummit & Foote. Abstract Algebra. Wiley, 3rd edition, 2004. Chapter 12]
- [Hungerford. Algebra. Springer, 1974. Chapter 4]

### 在线资源

- [Mathlib4 文档 - Algebra.Module.PID][https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/PID.html]

---

*最后更新：2026-04-15 | 版本：v1.0.0*
