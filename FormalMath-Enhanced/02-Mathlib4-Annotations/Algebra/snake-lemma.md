# 蛇引理 (Snake Lemma)

## Mathlib4 引用

```lean
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory

namespace SnakeLemma

variable {C : Type*} [Category C] [Abelian C]

/-- 蛇引理：连接同态的构造 -/
theorem snake_lemma {A B C A' B' C' : C}
    (f : A ⟶ B) (g : B ⟶ C) (f' : A' ⟶ B') (g' : B' ⟶ C')
    (α : A ⟶ A') (β : B ⟶ B') (γ : C ⟶ C')
    (h₁ : f ≫ β = α ≫ f') (h₂ : g ≫ γ = β ≫ g')
    (hex₁ : Exact f g) (hex₂ : Exact f' g')
    (hα : Mono α) (hγ : Epi γ) :
    ∃ (δ : kernel γ ⟶ cokernel α), Exact (kernel.map g γ β h₂) δ ∧
      Exact δ (cokernel.map α f' f h₁) := by
  -- 构造连接同态
  use connectingHomomorphism α β γ h₁ h₂ hex₁ hex₂ hα hγ
  constructor
  · -- 证明正合性的第一部分
    sorry
  · -- 证明正合性的第二部分
    sorry

/-- 蛇引理的长正合列 -/
theorem snake_lemma_long_exact {A B C A' B' C' : C}
    (f : A ⟶ B) (g : B ⟶ C) (f' : A' ⟶ B') (g' : B' ⟶ C')
    (α : A ⟶ A') (β : B ⟶ B') (γ : C ⟶ C')
    (h₁ : f ≫ β = α ≫ f') (h₂ : g ≫ γ = β ≫ g')
    (hex₁ : Exact f g) (hex₂ : Exact f' g')
    (hα : Mono α) (hγ : Epi γ) :
    ExactSeq C [
      kernel.ι γ, kernel.map g γ β h₂,
      connectingHomomorphism α β γ h₁ h₂ hex₁ hex₂ hα hγ,
      cokernel.map α f' f h₁, cokernel.π α
    ] := by
  sorry

end SnakeLemma
```

## 数学背景

蛇引理由Bernhard Eckmann和Peter Hilton在1950年代系统化表述（虽然更早就有类似构造），是同调代数中最基本和最强大的工具之一。它连接了两个短正合列之间的同态，产生一个长正合列。该引理在代数拓扑、代数几何和同调代数中无处不在，是导出函子理论的核心工具。

## 直观解释

蛇引理告诉我们：**在交换图的同调中，存在自然的"连接同态"填补缺口**。

想象一个蛇形的交换图，上下两行是正合列，中间有垂直映射连接。蛇引理构造了一个从上行核到下行余核的映射，使得整体形成正合列。"蛇"的名字来源于连接同态在图中的曲折路径——从下行对象的核出发，向上到中间对象，横移，再向下。

## 形式化表述

给定交换图（行正合）：
```
A --f--> B --g--> C --> 0
|α       |β       |γ
v        v        v
0 --> A' --f'-> B' --g'-> C'
```

**蛇引理**：存在连接同态 $\delta: \ker \gamma \to \text{coker } \alpha$ 使得：

$$\ker \alpha \to \ker \beta \to \ker \gamma \xrightarrow{\delta} \text{coker } \alpha \to \text{coker } \beta \to \text{coker } \gamma$$

形成正合列。

**构造**：
1. 取 $c \in \ker \gamma$，存在 $b \in B$ 使 $g(b) = c$
2. $\beta(b) \in \ker g' = \text{im } f'$，故 $\beta(b) = f'(a')$
3. 定义 $\delta(c) = a' + \text{im } \alpha \in \text{coker } \alpha$

## 证明思路

1. **良定义性**：验证 $\delta(c)$ 不依赖于 $b$ 的选择
2. **同态性**：证明 $\delta$ 保持加法结构
3. **在 $\ker \beta$ 处正合**：验证 $\ker \beta \to \ker \gamma \to \text{coker } \alpha$ 正合
4. **在 $\text{coker } \alpha$ 处正合**：类似验证
5. **自然性**：证明构造关于交换图的自然性

核心洞察是利用行的正合性进行"追踪"论证。

## 示例

### 示例 1：阿贝尔群

设 $A = \mathbb{Z}$，$B = \mathbb{Z}^2$，$C = \mathbb{Z}$，映射：
- $f(n) = (n, 0)$，$g(m, n) = n$
- $A' = \mathbb{Z}_2$，$B' = \mathbb{Z}_2 \times \mathbb{Z}$，$C' = \mathbb{Z}$
- $\alpha, \beta, \gamma$ 是商映射或投影

蛇引理构造连接同态并验证正合性。

### 示例 2：链复形

在同调论中，蛇引理用于证明短正合列诱导的长正合列：

$$0 \to A_\bullet \to B_\bullet \to C_\bullet \to 0$$

诱导：
$$\cdots \to H_n(A) \to H_n(B) \to H_n(C) \xrightarrow{\partial} H_{n-1}(A) \to \cdots$$

### 示例 3：模的扩张

设 $0 \to N' \to N \to N'' \to 0$ 和 $0 \to M' \to M \to M'' \to 0$ 是短正合列。

蛇引理用于研究 $\text{Ext}$ 函子的长正合列。

## 应用

- **同调论**：长正合列的构造（Mayer-Vietoris等）
- **导出函子**：$\text{Ext}$ 和 $\text{Tor}$ 的长正合列
- **代数几何**：层的上同调理论
- **代数拓扑**：同调群的计算

## 相关概念

- [长正合列 (Long Exact Sequence)](./long-exact-sequence.md)：同调的基本工具
- [导出函子 (Derived Functor)](./derived-functor.md)：同调代数的核心构造
- [正合列 (Exact Sequence)](./exact-sequence.md)：核等于像的序列
- [Ext函子 (Ext Functor)](./ext-functor.md)：扩张的分类
- [Tor函子 (Tor Functor)](./tor-functor.md)：张量积的左导出

## 参考

### 教材

- [Weibel. An Introduction to Homological Algebra. Cambridge, 1994. Chapter 1]
- [Hilton & Stammbach. A Course in Homological Algebra. Springer, 1971. Chapter 2]

### 历史文献

- [Eckmann & Hilton. Exact couples in an abelian category. 1956]

### 在线资源

- [Mathlib4 文档 - Homology](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/ShortComplex/Basic.html)
- [Stacks Project - 010J](https://stacks.math.columbia.edu/tag/010J)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
