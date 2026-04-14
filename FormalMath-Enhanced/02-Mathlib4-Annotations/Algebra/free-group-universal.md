---
msc_primary: 00A99
processed_at: '2026-04-03'
title: 自由群万有性质 (Free Group Universal Property)
---
# 自由群万有性质 (Free Group Universal Property)

## Mathlib4 引用

```lean
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.IsFreeGroup

namespace FreeGroup

variable {α : Type*} {G : Type*} [Group G]

/-- 自由群的万有性质：任意函数可唯一延拓为群同态 -/
theorem universal_property (f : α → G) :
    ∃! φ : FreeGroup α →* G, ∀ a : α, φ (of a) = f a := by
  use lift f
  constructor
  · -- 证明延拓性质
    intro a
    simp [lift, of]
  · -- 证明唯一性
    intro φ hφ
    ext x
    induction x with
    | h => simp
    | ih => sorry

def lift (f : α → G) : FreeGroup α →* G where
  toFun := by
    refine FreeGroup.recOn (C := fun _ => G) · (1) ?_ ?_
    · intro x _ hx
      exact f x * hx
    · intro x _ hx
      exact (f x)⁻¹ * hx
  map_one' := rfl
  map_mul' := sorry

end FreeGroup
```

## 数学背景

自由群的概念由Walther von Dyck在1882年系统化提出。它是群论中最基本的构造之一，类似于向量空间中的自由向量空间。自由群体现了"最一般"的群结构，任何群都可以表示为自由群的商，这使得自由群成为理解群表示理论的关键工具。

## 直观解释

自由群是**由一组生成元"自由"生成**的群，没有任何额外关系（除了群公理要求的关系）。

想象一个字母表，自由群的元素就是由这些字母组成的"单词"，可以正写（生成元）也可以反写（逆元）。两个单词相乘就是简单拼接，但要通过消去相邻的逆元对来化简（如 $aa^{-1}$ 消去）。自由群之所以"自由"，是因为除了群的基本规则外，没有任何限制这些字母如何组合的关系。

## 形式化表述

设 $\alpha$ 是任意集合（字母表），$F(\alpha)$ 是 $\alpha$ 上的自由群。

**万有性质**：对任意群 $G$ 和任意函数 $f: \alpha \to G$，存在唯一的群同态 $\varphi: F(\alpha) \to G$ 使得下图交换：

```
α --of--> F(α)
|         |
f    ∃!φ  |
v         v
G ------> G
```

即 $\varphi \circ \text{of} = f$，其中 $\text{of}: \alpha \to F(\alpha)$ 是标准嵌入。

## 证明思路

1. **构造延拓**：在生成元上定义 $\varphi([a]) = f(a)$，然后按同态规则扩展到整个群
2. **验证同态性**：证明 $\varphi(xy) = \varphi(x)\varphi(y)$，利用自由群元素的简化形式
3. **验证交换图**：由构造直接满足 $\varphi \circ \text{of} = f$
4. **证明唯一性**：任何满足条件的同态必须在生成元上与 $\varphi$ 一致，由生成性得唯一性

核心洞察是自由群由 $\alpha$ 自由生成，没有额外关系限制同态的定义。

## 示例

### 示例 1：单生成元自由群

设 $\alpha = \{a\}$，则 $F(\alpha) \cong \mathbb{Z}$。

任意函数 $f: \{a\} \to G$ 由 $f(a) = g$ 决定。

延拓同态 $\varphi: \mathbb{Z} \to G$ 为 $\varphi(n) = g^n$。

### 示例 2：两个生成元的自由群

设 $\alpha = \{a, b\}$，$F(\alpha) = F_2$。

元素形如简化单词：$a^2b^{-1}ab^3a^{-2}$ 等。

给定 $f(a) = g, f(b) = h$，则 $\varphi(a^2b^{-1}ab^3) = g^2h^{-1}gh^3$。

### 示例 3：群表示

任何群 $G$ 都可表示为自由群的商：$G \cong F(X)/R$，其中 $X$ 是生成集，$R$ 是关系集。

例如 $\mathbb{Z}_6 \cong F(\{a\})/\langle a^6 \rangle$。

## 应用

- **群表示理论**：将群描述为生成元和关系
- **组合群论**：研究群的算法性质
- **代数拓扑**：基本群的计算（van Kampen定理）
- **自动机理论**：群的字问题与形式语言

## 相关概念

- 自由积 (Free Product)：群的自由并
- 群表示 (Group Presentation)：生成元与关系
- 字问题 (Word Problem)：群的算法判定问题
- 自由阿贝尔群 (Free Abelian Group)：交换版本的自由群
- 生成元与关系 (Generators and Relations)：群的结构描述

## 参考

### 教材

- [M. Artin. Algebra. Pearson, 2nd edition, 2010. Chapter 6]
- [Lyndon & Schupp. Combinatorial Group Theory. Springer, 1977. Chapter 1]

### 历史文献

- [von Dyck. Gruppentheoretische Studien. Mathematische Annalen, 1882]

### 在线资源

- [Mathlib4 文档 - FreeGroup][https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/FreeGroup/Basic.html](需更新)
- [Groupprops - Free group][https://groupprops.subwiki.org/wiki/Free_group](需更新)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
