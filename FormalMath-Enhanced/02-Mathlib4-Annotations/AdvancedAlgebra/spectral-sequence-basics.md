# 谱序列基础

## Mathlib4 引用

```lean
import Mathlib.Algebra.Homology.SpectralSequence

namespace HomologicalAlgebra

/-- 谱序列的定义 -/
structure SpectralSequence (C : Type*) [Category C]
    [Abelian C] where
  page : ℕ → CochainComplex C ℤ
  differential (r : ℕ) : ∀ (p q : ℤ),
    page r p q ⟶ page r (p - r) (q + r - 1)
  convergence : ∃ (E∞ : GradedObject C ℤ),
    ∀ (n : ℤ), E∞ n ≅
      (colimit (page ·)).homology n

/-- 谱序列的收敛性 -/
theorem spectral_sequence_convergence
    {C : Type*} [Category C] [Abelian C]
    (E : SpectralSequence C)
    {A : C} (F : Filtration A) :
    (∃ (r₀ : ℕ), ∀ (r : ℕ) (_ : r ≥ r₀),
      E.differential r = 0) →
    E.convergence.1 ≅
      associatedGraded (F) := by
  -- 证明谱序列收敛到滤过对象的相伴分次
  sorry

end HomologicalAlgebra
```

## 数学背景

谱序列是Jean Leray在1946年作为战俘期间发明的工具，用于计算层上同调。这是一种复杂的代数结构，通过逐页逼近的方式计算（通常难以直接计算的）同调或上同调群。谱序列已成为代数拓扑、代数几何和同调代数中不可或缺的技术工具。Grothendieck用谱序列证明了许多深刻的定理，Serre也用它来研究球面的同伦群。

## 直观解释

谱序列如同一本逐步揭示秘密的书。每一页 $E^r$ 都包含一些信息，微分 $d^r$ 如同"解谜线索"——当 $d^r$ 作用后，某些信息被消除，新的信息被揭示。随着页数增加，页中的信息逐渐"稳定"。最终，极限页 $E^\infty$ 给出了我们想要的答案的"骨架"——虽然可能需要进一步组装才能得到完整结果。这就像通过逐步优化来逼近一个复杂问题的解。

## 形式化表述

**谱序列**：一族 $R$-模（或对象）$E^r_{p,q}$（$r \geq 2$，$p, q \in \mathbb{Z}$），配备微分
$$d^r_{p,q}: E^r_{p,q} \to E^r_{p-r, q+r-1}$$
满足 $d^r \circ d^r = 0$，且
$$E^{r+1}_{p,q} = \frac{\ker(d^r_{p,q})}{\text{im}(d^r_{p+r, q-r+1})}$$

**收敛**：谱序列**收敛**到 $H$，若存在滤过 $F^\bullet H$ 使得
$$E^\infty_{p,q} \cong F^p H_{p+q} / F^{p+1} H_{p+q}$$

## 证明思路

1. **构造双复形**：从双复形 $C^{\bullet,\bullet}$ 出发
2. **定义谱序列**：行或列滤过给出两种谱序列
3. **计算微分**：逐页计算微分的性质
4. **证明收敛**：验证极限页与目标同调的关系

## 示例

### 示例 1：Grothendieck谱序列

**问题**：设 $F: \mathcal{A} \to \mathcal{B}$，$G: \mathcal{B} \to \mathcal{C}$ 是左正合函子，$F$ 将内射对象映到 $G$-零调对象。计算 $R^n(G \circ F)$。

**解答**：

Grothendieck谱序列：
$$E^{p,q}_2 = R^p G(R^q F(X)) \Rightarrow R^{p+q}(G \circ F)(X)$$

这是连接复合函子导出函子的有力工具。

### 示例 2：Leray-Serre谱序列

**问题**：设 $F \to E \to B$ 是纤维丛，计算 $H^*(E)$。

**解答**：

Leray-Serre谱序列：
$$E^{p,q}_2 = H^p(B, \mathcal{H}^q(F)) \Rightarrow H^{p+q}(E)$$

这是代数拓扑中计算纤维丛上同调的基本工具。

## 应用

- **代数拓扑**：纤维丛的上同调计算
- **代数几何**：导出范畴的交换性
- **群上同调**：Hochschild-Serre谱序列
- **复几何**：Frölicher谱序列
- **K-理论**：Atiyah-Hirzebruch谱序列

## 相关概念

- [导出函子](./derived-functor.md)：谱序列的主要计算对象
- [Leray-Serre谱序列](./leray-serre-spectral-sequence.md)：拓扑学应用
- [Grothendieck谱序列](./grothendieck-spectral-sequence.md)：函子复合
- [滤过结构](./filtration.md)：谱序列的收敛基础
- [双复形](./double-complex.md)：谱序列的来源

## 参考

### 教材

- McCleary, J. A User's Guide to Spectral Sequences. Cambridge, 2001.
- Weibel, C.A. An Introduction to Homological Algebra. Cambridge, 1994. Chapter 5

### 论文

- Leray, J. L'anneau spectral et l'anneau filtré d'homologie d'un espace localement compact et d'une application continue. J. Math. Pures Appl., 29: 1-139, 1950.

### 在线资源

- [Spectral Sequence Wikipedia](https://en.wikipedia.org/wiki/Spectral_sequence)
- [nLab - Spectral Sequence](https://ncatlab.org/nlab/show/spectral+sequence)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
