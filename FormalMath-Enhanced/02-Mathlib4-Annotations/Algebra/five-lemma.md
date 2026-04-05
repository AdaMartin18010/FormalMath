---
msc_primary: 00A99
processed_at: '2026-04-03'
title: 五引理 (Five Lemma)
---
# 五引理 (Five Lemma)

## Mathlib4 引用

```lean
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.CategoryTheory.Abelian.Five

namespace FiveLemma

variable {C : Type*} [Category C] [Abelian C]

/-- 五引理：同构的传播 -/
theorem five_lemma_isomorphism {A B C D E A' B' C' D' E' : C}
    (f₁ : A ⟶ B) (f₂ : B ⟶ C) (f₃ : C ⟶ D) (f₄ : D ⟶ E)
    (g₁ : A' ⟶ B') (g₂ : B' ⟶ C') (g₃ : C' ⟶ D') (g₄ : D' ⟶ E')
    (α : A ⟶ A') (β : B ⟶ B') (γ : C ⟶ C') (δ : D ⟶ D') (ε : E ⟶ E')
    (h₁ : f₁ ≫ β = α ≫ g₁) (h₂ : f₂ ≫ γ = β ≫ g₂)
    (h₃ : f₃ ≫ δ = γ ≫ g₃) (h₄ : f₄ ≫ ε = δ ≫ g₄)
    (hex₁ : Exact f₁ f₂) (hex₂ : Exact f₂ f₃) (hex₃ : Exact f₃ f₄)
    (hex₁' : Exact g₁ g₂) (hex₂' : Exact g₂ g₃) (hex₃' : Exact g₃ g₄)
    (hα : IsIso α) (hβ : IsIso β) (hδ : IsIso δ) (hε : IsIso ε) :
    IsIso γ := by
  -- 利用核和余核的性质
  have h₁ : Mono γ := by
    apply mono_of_isZero_kernel
    -- 证明ker γ = 0
    sorry
  have h₂ : Epi γ := by
    apply epi_of_isZero_cokernel
    -- 证明coker γ = 0
    sorry
  exact isIso_of_mono_of_epi γ

/-- 五引理（满射版本）-/
theorem five_lemma_epi {A B C D E A' B' C' D' E' : C}
    (f₁ : A ⟶ B) (f₂ : B ⟶ C) (f₃ : C ⟶ D) (f₄ : D ⟶ E)
    (g₁ : A' ⟶ B') (g₂ : B' ⟶ C') (g₃ : C' ⟶ D') (g₄ : D' ⟶ E')
    (α : A ⟶ A') (β : B ⟶ B') (γ : C ⟶ C') (δ : D ⟶ D') (ε : E ⟶ E')
    (h₁ : f₁ ≫ β = α ≫ g₁) (h₂ : f₂ ≫ γ = β ≫ g₂)
    (h₃ : f₃ ≫ δ = γ ≫ g₃) (h₄ : f₄ ≫ ε = δ ≫ g₄)
    (hex₁ : Exact f₁ f₂) (hex₂ : Exact f₂ f₃) (hex₃ : Exact f₃ f₄)
    (hex₁' : Exact g₁ g₂) (hex₂' : Exact g₂ g₃) (hex₃' : Exact g₃ g₄)
    (hα : Epi α) (hβ : Epi β) (hδ : Mono δ) (hε : Mono ε) :
    Epi γ := by
  sorry

/-- 五引理（单射版本）-/
theorem five_lemma_mono {A B C D E A' B' C' D' E' : C}
    (f₁ : A ⟶ B) (f₂ : B ⟶ C) (f₃ : C ⟶ D) (f₄ : D ⟶ E)
    (g₁ : A' ⟶ B') (g₂ : B' ⟶ C') (g₃ : C' ⟶ D') (g₄ : D' ⟶ E')
    (α : A ⟶ A') (β : B ⟶ B') (γ : C ⟶ C') (δ : D ⟶ D') (ε : E ⟶ E')
    (h₁ : f₁ ≫ β = α ≫ g₁) (h₂ : f₂ ≫ γ = β ≫ g₂)
    (h₃ : f₃ ≫ δ = γ ≫ g₃) (h₄ : f₄ ≫ ε = δ ≫ g₄)
    (hex₁ : Exact f₁ f₂) (hex₂ : Exact f₂ f₃) (hex₃ : Exact f₃ f₄)
    (hex₁' : Exact g₁ g₂) (hex₂' : Exact g₂ g₃) (hex₃' : Exact g₃ g₄)
    (hα : Epi α) (hβ : Mono β) (hδ : Mono δ) (hε : Epi ε) :
    Mono γ := by
  sorry

end FiveLemma
```

## 数学背景

五引理是同调代数中的基本工具，是四引理的自然推广。它最早由Eilenberg和Steenrod在代数拓扑的公理化工作中系统使用。该引理的重要性在于：当两个长正合列通过交换图连接时，它允许我们"传播"同构性质。这是证明同调不变性的关键工具，广泛应用于代数拓扑、同调代数和代数几何。

## 直观解释

五引理告诉我们：**在五个对象构成的交换图中，如果外部四个映射是同构（或单/满射），则中间的映射也是同构（或单/满射）**。

想象两排各五个相连的盒子，盒子间有竖直连接线。如果竖直连接在两端四个位置都是"好"的（同构），那么中间位置的连接也必须是"好"的。这是因为正合性条件强制了信息在中间位置的传递，没有"泄漏"或"阻塞"。

## 形式化表述

给定交换图（行正合）：
```
A --f₁--> B --f₂--> C --f₃--> D --f₄--> E
|α        |β        |γ        |δ        |ε
v         v         v         v         v
A'--g₁--> B'--g₂--> C'--g₃--> D'--g₄--> E'
```

**五引理**：
1. **同构版本**：若 $\alpha, \beta, \delta, \varepsilon$ 是同构，则 $\gamma$ 是同构
2. **单射版本**：若 $\alpha$ 满、$\beta, \delta$ 单、$\varepsilon$ 满，则 $\gamma$ 单
3. **满射版本**：若 $\alpha$ 满、$\beta, \delta$ 满、$\varepsilon$ 单，则 $\gamma$ 满

## 证明思路

1. **单射性证明**（追图法）：
   - 设 $\gamma(c) = 0$，需证 $c = 0$
   - 由交换性，$\delta(f_3(c)) = g_3(\gamma(c)) = 0$
   - $\delta$ 单，故 $f_3(c) = 0$
   - 上行正合，存在 $b$ 使 $f_2(b) = c$
   - 继续追踪得 $\beta(b) = g_1(a')$ 对某个 $a'$
   - $\alpha$ 满，$a' = \alpha(a)$，得 $b = f_1(a)$（$\beta$ 单）
   - $c = f_2(b) = f_2(f_1(a)) = 0$

2. **满射性证明**：类似追图

3. **同构**：单射+满射

核心洞察是正合性允许我们通过相邻对象"传递"信息。

## 示例

### 示例 1：同调群比较

设 $f: X \to Y$ 是拓扑空间的映射，诱导：
```
Hₙ(A) → Hₙ(X) → Hₙ(X,A) → Hₙ₋₁(A) → Hₙ₋₁(X)
  ↓        ↓        ↓         ↓         ↓
Hₙ(B) → Hₙ(Y) → Hₙ(Y,B) → Hₙ₋₁(B) → Hₙ₋₁(Y)
```

若左右四映射同构（如 $f$ 是同伦等价），则中间 $H_n(X,A) \cong H_n(Y,B)$。

### 示例 2：导出函子

比较两个对象的导出函子计算时，五引理确保不同分解给出同构结果。

### 示例 3：短五引理

五引理的特例（省略两端）：短正合列的态射若两端是同构，则中间也是。

## 应用

- **同调不变性**：证明同调群的同伦不变性
- **长正合列比较**：比较不同空间的长正合列
- **导出函子**：证明不同分解的同构性
- **代数几何**：层上同调的比较定理

## 相关概念

- [短五引理 (Short Five Lemma)](./short-five-lemma.md)：三个对象的版本
- [四引理 (Four Lemma)](./four-lemma.md)：四个对象的部分结果
- [九引理 (Nine Lemma)](./nine-lemma.md)：$3 \times 3$ 交换图的结果
- [追图法 (Diagram Chasing)](./diagram-chasing.md)：证明技术
- [正合列 (Exact Sequence)](./exact-sequence.md)：同调代数基础

## 参考

### 教材

- [Weibel. An Introduction to Homological Algebra. Cambridge, 1994. Chapter 1]
- [Hilton & Stammbach. A Course in Homological Algebra. Springer, 1971. Chapter 1]

### 历史文献

- [Eilenberg & Steenrod. Foundations of Algebraic Topology. Princeton, 1952]

### 在线资源

- [Mathlib4 文档 - Five](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Abelian/Five.html)
- [Stacks Project - 010M](https://stacks.math.columbia.edu/tag/010M)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
