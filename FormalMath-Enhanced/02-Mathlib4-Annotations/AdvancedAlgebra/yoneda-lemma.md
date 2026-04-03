# Yoneda引理

## Mathlib4 引用

```lean
import Mathlib.CategoryTheory.Yoneda

namespace CategoryTheory

/-- Yoneda引理 -/
theorem yoneda_lemma
    {C : Type*} [Category C]
    {F : Cᵒᵖ ⥤ Type*} {X : C} :
    F.obj (Opposite.op X) ≅
    (yoneda.obj X ⟶ F) := by
  -- 构造自然的同构
  constructor
  · -- 正向映射
    intro x
    exact {
      app := fun Y f => F.map f.op x
      naturality := by aesop
    }
  · -- 反向映射
    intro α
    exact α.app X (𝟙 X)
  · -- 验证互逆
    aesop_cat

/-- Yoneda嵌入的完全忠实性 -/
theorem yoneda_fully_faithful
    {C : Type*} [Category C] :
    FullyFaithful (yoneda : C ⥤ (Cᵒᵖ ⥤ Type*)) := by
  -- 由Yoneda引理直接推出
  apply fullyFaithfulYoneda

end CategoryTheory
```

## 数学背景

Yoneda引理由日本数学家Nobuo Yoneda在1954年证明（发表则在1958年），是范畴论中最基本且深刻的定理之一。引理表明，一个对象完全由它与其他对象的关系（态射）决定。这一定理将抽象的数学对象"具体化"为可操作的函子，是表示论、代数几何和计算机科学中许多构造的基础。

## 直观解释

Yoneda引理的核心洞察是"对象由其行为决定"。想象一个神秘的盒子——你无法直接看到里面，但可以通过它与外界的交互来了解它。Yoneda引理说：这种外部交互的完整记录（所有可能的输入输出关系）完全确定了这个盒子本身。在数学中，这意味着我们可以通过研究一个对象的"表示"（即从其他对象到它的映射）来完全理解这个对象。

## 形式化表述

设 $\mathcal{C}$ 是局部小范畴，$F: \mathcal{C}^{op} \to \mathbf{Set}$ 是反变函子，$X \in \mathcal{C}$。

**Yoneda引理**：存在自然双射
$$\text{Nat}(\text{Hom}(-, X), F) \cong F(X)$$

**推论（Yoneda嵌入）**：函子 $y: \mathcal{C} \to [\mathcal{C}^{op}, \mathbf{Set}]$，$X \mapsto \text{Hom}(-, X)$ 是完全忠实的。

**表示函子**：若 $F \cong \text{Hom}(-, X)$，称 $F$ **可表示**，$X$ 是**表示对象**。

## 证明思路

1. **构造映射**：给定自然变换 $\alpha: \text{Hom}(-, X) \to F$，计算其在 $X$ 处的作用 $\alpha_X(1_X) \in F(X)$
2. **构造逆映射**：给定 $x \in F(X)$，定义自然变换 $\alpha_Y(f) = F(f)(x)$
3. **验证互逆**：直接计算验证两个映射互逆
4. **验证自然性**：证明同构关于 $X$ 和 $F$ 是自然的

## 示例

### 示例 1：群作用

**问题**：描述群 $G$ 的集合作用与可表示函子的关系。

**解答**：

群 $G$ 可以看作单对象范畴 $\mathcal{B}G$。函子 $\mathcal{B}G \to \mathbf{Set}$ 是 $G$-集合。

Yoneda引理给出：$G$-集合的同态 $\text{Hom}_G(G, X) \cong X$（作为集合），其中 $G$ 通过左乘作用于自身。

### 示例 2：拓扑中的分类空间

**问题**：用Yoneda引理解释分类空间 $BG$。

**解答**：

函子 $F: \mathbf{Top}^{op} \to \mathbf{Set}$，$F(X) = \{\text{主$G$-丛在$X$上}\}$ 是可表示的。

表示对象是分类空间 $BG$，即：
$$\text{Hom}_{\mathbf{Top}}(X, BG) \cong \{\text{主$G$-丛在$X$上}\}$$

## 应用

- **表示论**：表示函子的可表示性
- **代数几何**：可表示函子与模空间
- **泛性质**：泛构造的表示论解释
- **类型论**：依赖类型与范畴语义
- **计算机科学**：continuation-passing style

## 相关概念

- [可表示函子](./representable-functor.md)：Yoneda引理的核心对象
- [泛性质](./universal-property.md)：与表示对象等价
- [伴随函子](./adjoint-functor.md)：Yoneda引理的应用
- [极限](./limit.md)：可表示性的特例
- [余极限](./colimit.md)：对偶的Yoneda引理

## 参考

### 教材

- Mac Lane, S. Categories for the Working Mathematician. Springer, 1998. Chapter 3
- Riehl, E. Category Theory in Context. Dover, 2016. Chapter 2

### 论文

- Yoneda, N. On the homology theory of modules. J. Fac. Sci. Univ. Tokyo Sect. I, 7: 193-227, 1954.

### 在线资源

- [Yoneda Lemma Wikipedia](https://en.wikipedia.org/wiki/Yoneda_lemma)
- [nLab - Yoneda Lemma](https://ncatlab.org/nlab/show/Yoneda+lemma)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
