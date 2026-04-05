---
msc_primary: 00A99
processed_at: '2026-04-03'
title: Riesz表示定理 (Riesz Representation Theorem)
---
# Riesz表示定理 (Riesz Representation Theorem)

## Mathlib4 引用

```lean
import Mathlib.MeasureTheory.Measure.RieszRepresentation
import Mathlib.MeasureTheory.ContinuousFunctionalCalculus.Basic

namespace RieszRepresentation

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
variable {Λ : C_c(X, ℝ) →L[ℝ] ℝ} -- 紧支撑连续函数上的正线性泛函

/-- Riesz表示定理：正线性泛函由正则Borel测度表示 -/
theorem riesz_representation (hΛ : ∀ f, 0 ≤ f → 0 ≤ Λ f) :
    ∃ μ : Measure X, IsRegular μ ∧
      ∀ f : C_c(X, ℝ), Λ f = ∫ x, f x ∂μ := by
  -- 构造外测度
  let μ* : Set X → ℝ≥0∞ := fun A =>
    ⨅ (K : Set X) (hK : IsCompact K) (hKA : K ⊆ A),
    ⨅ (f : C_c(X, ℝ)) (hf : ∀ x ∈ K, 1 ≤ f x) (hf0 : ∀ x, 0 ≤ f x),
    Λ f
  -- Carathéodory延拓
  sorry

/-- Riesz表示定理（复值情形）-/
theorem riesz_representation_complex {Λ : C_c(X, ℂ) →L[ℂ] ℂ}
    (hΛ : ∀ f, ContinuousMap.norm f ≤ 1 → ‖Λ f‖ ≤ Λ 1) :
    ∃ μ : Measure X, IsRegular μ ∧
      ∀ f : C_c(X, ℂ), Λ f = ∫ x, f x ∂μ := by
  sorry

/-- 测度的唯一性 -/
theorem riesz_representation_unique {μ ν : Measure X} [IsRegular μ] [IsRegular ν]
    (h : ∀ f : C_c(X, ℝ), ∫ x, f x ∂μ = ∫ x, f x ∂ν) :
    μ = ν := by
  -- 用连续函数分离测度
  sorry

end RieszRepresentation
```

## 数学背景

Riesz表示定理由Frigyes Riesz在1909年（对 $C[0,1]$）和1911年（一般紧空间）证明，后由Mark Krein、Shizuo Kakutani等人推广到局部紧空间。这是测度论和泛函分析的里程碑结果，表明局部紧空间上紧支撑连续函数空间上的任何正线性泛函都可以由唯一的正则Borel测度表示。该定理是概率论、调和分析和量子场论的基础，提供了"函数"视角到"测度"视角的桥梁。

## 直观解释

Riesz表示定理告诉我们：**连续函数上的"平均值"总可以表示为关于某个测度的积分**。

想象你在空间 $X$ 上定义了一个"平均"操作（正线性泛函），它对连续函数给出数值。定理说，存在一个"分布"（测度），使得这个平均操作等于按该分布加权求和。这就像说，任何合理的加权方案都可以表示为某种密度分布下的期望。

## 形式化表述

设 $X$ 是局部紧Hausdorff空间，$C_c(X)$ 是紧支撑连续函数空间。

**Riesz表示定理**：设 $\Lambda: C_c(X) \to \mathbb{R}$ 是正线性泛函（$f \geq 0 \Rightarrow \Lambda(f) \geq 0$）。

则存在唯一的正则Borel测度 $\mu$ 使得：
$$\Lambda(f) = \int_X f \, d\mu$$

对所有 $f \in C_c(X)$ 成立。

**正则性**：
- 内正则：$\mu(A) = \sup\{\mu(K) : K \subseteq A, K \text{ 紧}\}$
- 外正则：$\mu(A) = \inf\{\mu(U) : A \subseteq U, U \text{ 开}\}$

## 证明思路

1. **构造外测度**：
   - 对开集 $U$：$\mu^*(U) = \sup\{\Lambda(f) : f \prec U\}$（$f \prec U$ 表示 $0 \leq f \leq 1$，$\text{supp } f \subseteq U$）
   - 延拓到所有集合
   
2. **Carathéodory延拓**：
   - 证明可测集构成 $\sigma$-代数
   - 包含所有开集，故包含Borel集
   
3. **正则性验证**：
   - 局部紧性保证紧逼近
   - Urysohn引理构造截断函数
   
4. **表示等式**：
   - 对示性函数用逼近
   - 线性性扩展到简单函数
   - 单调收敛到一般可积函数

核心洞察是正泛函的单调性和局部紧空间的拓扑结构。

## 示例

### 示例 1：Dirac测度

$\Lambda(f) = f(x_0)$ 对应 $\mu = \delta_{x_0}$（Dirac测度）。

$\int f d\delta_{x_0} = f(x_0)$。

### 示例 2：Lebesgue测度

$X = \mathbb{R}$，$\Lambda(f) = \int_{-\infty}^{\infty} f(x) dx$（Riemann积分）。

对应 $\mu$ 是Lebesgue测度。

### 示例 3：概率测度

$X = [0,1]$，$\Lambda(f) = \sum_{n=1}^{\infty} 2^{-n} f(q_n)$，其中 $\{q_n\}$ 是 $[0,1]$ 中有理数枚举。

对应 $\mu = \sum_{n=1}^{\infty} 2^{-n} \delta_{q_n}$（离散概率测度）。

## 应用

- **概率论**：分布函数的对应
- **谱理论**：算子谱测度的存在
- **调和分析**：Fourier变换的测度形式
- **量子场论**：Wightman公理
- **遍历理论**：不变测度的存在性

## 相关概念

- 正则Borel测度 (Regular Borel Measure)：内外正则的测度
- 紧支撑函数 (Compact Support Function)：在紧集外为零的函数
- 正线性泛函 (Positive Linear Functional)：保持序结构的泛函
- Urysohn引理 (Urysohn's Lemma)：连续函数的分离
- Carathéodory延拓 (Carathéodory Extension)：测度构造方法

## 参考

### 教材

- [Rudin. Real and Complex Analysis. McGraw-Hill, 3rd edition, 1987. Chapter 2]
- [Folland. Real Analysis. Wiley, 2nd edition, 1999. Chapter 7]

### 历史文献

- [Riesz. Sur les opérations fonctionnelles linéaires. 1909]
- [Riesz. Sur certains systèmes singuliers d'équations intégrales. 1911]

### 在线资源

- [Mathlib4 文档 - RieszRepresentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/RieszRepresentation.html)[需更新]
- [Wikipedia - Riesz Representation Theorem](https://en.wikipedia.org/wiki/Riesz%E2%80%93Markov%E2%80%93Kakutani_representation_theorem)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
